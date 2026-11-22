"""Recompute all four finite certificates for ENT_proof.tex."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent.parent
CHECKS = {
    'small34': 'certify_small34.py',
    'small56': 'certify_small56.py',
    'large': 'ent_verify_large.py',
    'curvature': 'ent_verify_curvature.py',
}


def complete_certificate(name, data):
    if name == 'small34':
        return (data['all_pass'] and [row['n'] for row in data['results']] == [3, 4] and
                all(row['pass'] for row in data['results']))
    if name == 'small56':
        return [row['n'] for row in data] == [5, 6] and all(row['pass_all'] for row in data)
    if name == 'large':
        return (data['langevin']['pass'] and data['fourier']['pass'] and
                data['fourier']['threshold'] == 256)
    if name == 'curvature':
        return (data['passed'] and data['constant'] == 7 and
                [row['n'] for row in data['dimensions']] == list(range(7, 256)) and
                all(row['passed'] for row in data['dimensions']))
    raise ValueError(f'Unknown certificate {name}')


def run_certificate(name, directory):
    script = ROOT / 'code' / CHECKS[name]
    result = subprocess.run([sys.executable, str(script)], cwd=directory, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{script.name} exited with {result.returncode}\n{result.stdout}")
    path = directory / f'{name}_results.json'
    data = json.loads(path.read_text(encoding='utf-8'))
    if not complete_certificate(name, data):
        raise RuntimeError(f'{script.name} produced an incomplete or failed certificate')
    print(f'{name} passed', flush=True)
    return path


def main():
    if not __debug__:
        raise RuntimeError("The certificates require Python assertions. Run without -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='compare with the recorded JSON files without replacing them')
    parser.add_argument('--figure', action='store_true',
                        help='also regenerate the illustrative density figure in figures/')
    args = parser.parse_args()
    results = ROOT / 'results'
    if not args.check:
        results.mkdir(exist_ok=True)
    # The four programs have distinct output names. A failed run leaves the
    # recorded data intact. Publish the summary after all four verified files.
    with TemporaryDirectory(dir=None if args.check else results) as tmp:
        directory = Path(tmp)
        with ThreadPoolExecutor(max_workers=len(CHECKS)) as executor:
            jobs = [executor.submit(run_certificate, name, directory) for name in CHECKS]
            files = [job.result() for job in jobs]

        summary = {
            'all_passed': True,
            'dependencies': {name: version(name) for name in ('python-flint', 'sympy')},
            'certificates': [
                {'program': f'code/{script}', 'output': f'results/{path.name}',
                 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                for script, path in zip(CHECKS.values(), files)
            ],
        }
        summary_path = directory / 'verification_summary.json'
        summary_path.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
        files.append(summary_path)
        if args.check:
            mismatches = [path.name for path in files if
                          not (results / path.name).is_file() or
                          (results / path.name).read_bytes() != path.read_bytes()]
            if mismatches:
                raise SystemExit('Missing or different recorded results: ' + ', '.join(mismatches))
            print('All four certificates and the recorded summary match.')
        else:
            for path in files:
                path.replace(results / path.name)
            print('Wrote four verified certificates and their summary to results/.')

    if args.figure:
        subprocess.run([sys.executable, str(ROOT / 'code/ent_make_figure.py'),
                        '--output-dir', str(ROOT / 'figures')], check=True)


if __name__ == '__main__':
    main()
