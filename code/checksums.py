"""Check or refresh SHA256.json for the manuscript and its Python supplement."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / 'SHA256.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='record the current file digests')
    args = parser.parse_args()
    paths = [ROOT / name for name in ('ENT_proof.pdf', 'ENT_proof.tex', 'Makefile', 'README.md',
                                       'requirements.txt', 'requirements-figure.txt')]
    for pattern in ('code/*.py', 'figures/*.pdf', 'figures/*.png', 'figures/*.json',
                    'results/*.json'):
        paths.extend(ROOT.glob(pattern))
    observed = {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(paths)}
    if args.write:
        MANIFEST.write_text(json.dumps(observed, indent=2) + '\n', encoding='utf-8')
        return
    expected = json.loads(MANIFEST.read_text(encoding='utf-8'))
    changed = sorted(name for name in expected.keys() | observed.keys()
                     if expected.get(name) != observed.get(name))
    if changed:
        raise SystemExit('Checksum mismatch: ' + ', '.join(changed))
    print(f'{len(observed)} files match SHA256.json.')


if __name__ == '__main__':
    main()
