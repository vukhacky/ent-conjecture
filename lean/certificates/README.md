# Generated Lean spline certificates

The four Lean templates and `modules.tsv` specify 710 modules under `ENT/Pilot/`. They cover the 5,266 cells with `31 ≤ n ≤ 149` and `1 ≤ k ≤ floor((n−1)/2)`. The manifest records the inclusive cell range, formatting and expected SHA-256 of each UTF-8 source file. The expanded sources occupy 1,104,146,017 bytes.

From the Lean project directory, generate the modules before building:

```sh
python -m pip install python-flint==0.9.0
python scripts/generate_certificates.py
```

The generator needs no network access once Python and python-flint are installed. It computes integer splines, curvature polynomials, Bernstein numerators and Kronecker base exponents. It checks the resulting module against the manifest before writing it. Lean checks the arithmetic identities in those modules when their targets are built.

For a hash comparison without writing the sources, use `python scripts/generate_certificates.py --verify-only`. To generate one dimension in another directory, use e.g. `python scripts/generate_certificates.py --dimension 31 --output /tmp/ent-splines`.

To revise these certificates, edit the formulas in `scripts/generate_certificates.py`, the Lean proof templates, or the ranges in `modules.tsv`. Generate a candidate manifest with `python scripts/generate_certificates.py --new-manifest modules.next.tsv`, review its diff against `certificates/modules.tsv`, and adopt the new manifest after reviewing the change. Generate into a clean project and rerun the corresponding Lean checks.
