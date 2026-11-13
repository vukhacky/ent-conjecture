"""Reproduce the exact and interval certificates accompanying ENT_proof.tex."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import importlib.metadata
import json
import os
import platform
import subprocess
import sys
import time


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: certificate assertions must remain enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--figure', action='store_true', help='also regenerate the illustrative density figure')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    results = root / 'results'
    results.mkdir(exist_ok=True)
    environment = os.environ.copy()
    environment.pop('PYTHONOPTIMIZE', None)
    tasks = [
        ('small34', [sys.executable, str(root/'code/certify_small34.py')]),
        ('small56', [sys.executable, str(root/'code/certify_small56.py')]),
        ('large', [sys.executable, str(root/'code/ent_verify_large.py')]),
        ('curvature', [sys.executable, str(root/'code/ent_verify_curvature.py'), '--output', 'curvature_results.json']),
    ]
    started = time.perf_counter()

    def execute(task):
        name, command = task
        before = time.perf_counter()
        process = subprocess.run(command, cwd=results, env=environment, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (results/(name+'.log')).write_text(process.stdout)
        row = {'certificate': name, 'returncode': process.returncode,
               'seconds': time.perf_counter()-before, 'passed': process.returncode == 0}
        print(json.dumps(row), flush=True)
        return row

    with ThreadPoolExecutor(max_workers=4) as executor:
        records = list(executor.map(execute, tasks))
    if args.figure:
        record = execute(('figure', [sys.executable, str(root/'code/ent_make_figure.py'),
                                    '--output-dir', str(root/'figures')]))
        records.append(record)
    summary = {'python': platform.python_version(),
               'dependencies': {k: importlib.metadata.version(k) for k in ['sympy', 'python-flint']},
               'certificates': records, 'seconds': time.perf_counter()-started,
               'all_passed': all(row['passed'] for row in records)}
    (results/'verification_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    if not summary['all_passed']:
        raise SystemExit('A verification failed; inspect results/*.log')


if __name__ == '__main__':
    main()
