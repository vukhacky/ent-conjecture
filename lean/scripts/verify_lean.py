#!/usr/bin/env python3
"""Compile the Lean proof and its statement and axiom checks from a fresh artifact tree."""
import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import tempfile


def package_paths(project):
    manifest = json.loads((project / "lake-manifest.json").read_text())
    package_root = project / manifest["packagesDir"]
    paths = []
    for package in manifest["packages"]:
        directory = (package_root / package["name"]).resolve()
        head = subprocess.check_output(
            ["git", "-C", directory, "rev-parse", "HEAD"], text=True
        ).strip()
        if head != package["rev"]:
            raise SystemExit(f"Package {directory.name} is at {head}, expected {package['rev']}")
        paths.append(directory)
    return paths


def import_graph(project, roots, env, mathlib):
    """Ask the installed Lean frontend to resolve module headers, including their source paths."""
    graph = {}
    mathlib_imports = set()
    pending = list(roots)
    while pending:
        source = pending.pop()
        if source in graph:
            continue
        path = project / source
        result = subprocess.run(
            ["lean", "--src-deps", path], cwd=project, env=env, text=True,
            stdout=subprocess.PIPE, check=True,
        )
        local = set()
        for line in result.stdout.splitlines():
            dependency = Path(line).resolve()
            if dependency.is_relative_to(mathlib):
                relative = dependency.relative_to(mathlib).with_suffix("")
                mathlib_imports.add(".".join(relative.parts))
            elif dependency.is_relative_to(project):
                relative = dependency.relative_to(project)
                if relative.parts[0] != ".lake":
                    local.add(relative)
        graph[source] = local
        pending.extend(local)
    return graph, mathlib_imports


def verify(project, roots, workers, output, full, fetch):
    expected = (project / "lean-toolchain").read_text().strip().split(":v")[-1]
    actual = subprocess.check_output(["lean", "--short-version"], cwd=project, text=True).strip()
    if actual != expected:
        raise SystemExit(f"Lean {actual} is installed, expected {expected}")
    if fetch:
        subprocess.run(["lake", "env", "lean", "--version"], cwd=project, check=True,
                       env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
    packages = package_paths(project)
    env = os.environ.copy()
    env["LEAN_SRC_PATH"] = os.pathsep.join(map(str, [project, *packages]))
    mathlib = next(p for p in packages if p.name == "mathlib")
    graph, mathlib_imports = import_graph(project, roots, env, mathlib)
    if full:
        shipped = {p.relative_to(project) for p in (project / "ENT").rglob("*.lean")}
        shipped.add(Path("ENT.lean"))
        missing = shipped.difference(graph)
        if missing:
            raise SystemExit("Source files outside the audit closure: " + ", ".join(map(str, sorted(missing))))
    if fetch and mathlib_imports:
        subprocess.run(["lake", "exe", "cache", "get", *sorted(mathlib_imports)], cwd=project, check=True)
    libraries = [p / ".lake/build/lib/lean" for p in packages]
    for library in libraries:
        if (library / "ENT").exists() or (library / "ENT.olean").exists():
            raise SystemExit(f"Unexpected project artifact in a dependency cache: {library}")
    env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *(p for p in libraries if p.is_dir())]))

    sorter = TopologicalSorter(graph)
    sorter.prepare()
    print(f"Compiling {len(graph)} Lean modules with {workers} worker(s)", flush=True)

    def compile_module(source):
        target = (output / source).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = ["lean", "-j1", "-M4096", "-o", target, source]
        proc = subprocess.run(command, cwd=project, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if proc.returncode or "uses 'sorry'" in proc.stdout:
            raise RuntimeError(f"{source} returned {proc.returncode}\n{proc.stdout}")
        if source in roots and proc.stdout:
            print(proc.stdout, end="", flush=True)

    ready = deque()
    active = {}
    done = 0
    with ThreadPoolExecutor(max_workers=workers) as executor:
        while sorter.is_active():
            ready.extend(sorted(sorter.get_ready()))
            while ready and len(active) < workers:
                source = ready.popleft()
                active[executor.submit(compile_module, source)] = source
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for job in finished:
                source = active.pop(job)
                job.result()
                sorter.done(source)
                done += 1
                if done % 25 == 0 or source in roots:
                    print(f"[{done}/{len(graph)}] {source}", flush=True)
    print(f"Verified all {done} modules.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2, help="simultaneous Lean processes (default 2)")
    parser.add_argument("--fetch-cache", action="store_true",
                        help="checkout pinned packages and fetch the imported mathlib cache")
    parser.add_argument("modules", nargs="*", help="specific modules (default: audit all shipped sources)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    project = Path.cwd()
    if not (project / "lean-toolchain").is_file():
        parser.error("run this script in the directory containing lean-toolchain")
    modules = args.modules or ["ENT.Audit", "ENT.PaperStatements"]
    roots = [Path(*m.split(".")).with_suffix(".lean") for m in modules]
    for source in roots:
        if not (project / source).is_file():
            parser.error(f"missing target {source}")
    with tempfile.TemporaryDirectory(prefix="ent-verify-") as tmp:
        verify(project, roots, args.jobs, Path(tmp), not args.modules, args.fetch_cache)


if __name__ == "__main__":
    main()
