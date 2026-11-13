# Entropy maximization for cube projections

**A proof of the Eskenazis–Nayar–Tkocz conjecture on entropy maximization for cube projections**  
Vu Khac Ky, FPT University, Hanoi, Vietnam

This archive contains the manuscript, its complete LaTeX source, the figure,
and the programs and recorded outputs for its finite proof certificates.
The verification scripts are also available on
[GitHub](https://github.com/vukhacky/ent-conjecture/).

## Mathematical scope

The main theorem combines the proof here for dimensions at most 149 with
Zhekai Pang's theorem for dimensions at least 150 (arXiv:2611.13533).
The finite computation includes dimension 150. The proof explicitly depends
on Pang's theorem and comparison lemma; the archive does not replace those
external mathematical inputs.

The quantitative result is obtained separately. Exact spline certificates
cover dimensions 7 through 255; a quantitative refinement of Pang's Fourier
estimates treats every dimension at least 256. Dimensions 3 through 6 use
polynomial entropy duals and local estimates with certified integrals.
The asymptotically optimal stability coefficient is 3/50.

## Contents

- `ENT_proof.pdf`: compiled paper.
- `ENT_proof.tex`: complete LaTeX source, including the appendices and bibliography.
- `figures/projection_density.pdf`: vector figure used by the manuscript.
- `figures/projection_density.png`: raster preview.
- `figures/figure_results.json`: illustrative density and entropy calculations.
- `code/`: verification and figure-generation programs.
- `results/`: actual JSON outputs and console logs of the accompanying run.
- `SHA256.json`: checksums of the delivered files, excluding the manifest itself.

## Reproduce the certificates

Use Python 3.11 or newer. From the extracted archive directory:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
python3 code/run_all.py
```

The entry point runs four independent checks and writes their outputs to
`results/`. The curvature check is the longest. The timings and Python/package
versions of the recorded run are in `results/verification_summary.json`.
A nonzero exit status signals a failed verification. Assertions are part of
the verifier: do not use Python's `-O` option or `PYTHONOPTIMIZE`.

| Program | Verified component | Arithmetic |
| --- | --- | --- |
| `certify_small34.py` | Polynomial gaps and integral bounds in dimensions 3 and 4 | Exact rational arithmetic and 192-bit Arb balls |
| `certify_small56.py` | Polynomial gaps, Hessian bounds and averaged remainders in dimensions 5 and 6 | Exact rational arithmetic and 192-bit Arb balls |
| `ent_verify_curvature.py` | Third logarithmic derivative bound in dimensions 7 through 255 | Arbitrary-precision integers |
| `ent_verify_large.py` | Scalar inequality and rational Fourier bounds for dimensions at least 256 | Symbolic identities and exact rational arithmetic |

`small_integrals.py` contains the shared moment and certified integration
routines for the dimension-5 and dimension-6 checks. The analytic proof of
the local dimension-3 and dimension-4 estimates is given in the appendices.
The large-dimension asymptotic arguments are analytic; the program verifies
the finite identities and constants used in them.

To reproduce only the finite curvature range needed to complete the conjecture
with Pang's theorem (including the overlap dimension), run:

```sh
python3 code/ent_verify_curvature.py --last 150 --output curvature_7_150.json
```

The full recorded curvature run checks 16,372 cells and 8,347,574 Bernstein
numerators, including 30 independently cross-checked cells. Its certificate
digest is `1c79243e41aa9141eb6896e6f60d4446cc9b0999d1fc085e7987ffa4818fd0b3`.
Zero coefficients are permitted because the claimed inequality is non-strict;
strict entropy maximality follows from the positive stability constant.

## Reproduce the illustration

```sh
python3 -m pip install -r requirements-figure.txt
python3 code/ent_make_figure.py --output-dir figures
```

Alternatively, `python3 code/run_all.py --figure` runs both the certificates
and the figure generation. The plot compares the two-coordinate and full
diagonal directions in the eight-dimensional cube. Its floating-point
quadrature is independently compared with high-precision integration.
These are illustrative numerical calculations and are not proof certificates.

## Compile the manuscript

A standard TeX Live installation with the packages named in `ENT_proof.tex`
is sufficient. The manuscript uses the bundled figure at
`figures/projection_density.pdf` and includes its bibliography directly.
Compile from the archive directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error ENT_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error ENT_proof.tex
```

The equivalent commands are `make paper`, `make verify`, and `make figure`.
