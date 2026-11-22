# Entropy maximization for cube projections

**A proof of the Eskenazis–Nayar–Tkocz conjecture on entropy maximization for cube projections**, by Vu Khac Ky, FPT University, Hanoi, Vietnam.

The paper studies the differential entropy of a projection of the uniform measure on the cube. It proves that, among unit directions, entropy is maximized precisely when all coordinates have equal magnitude. It also gives quantitative stability bounds and determines the asymptotically optimal coefficient. [Manuscript (PDF)](ENT_proof.pdf) · [LaTeX source](ENT_proof.tex)

## Scope of verification

The paper uses Pang's theorem for the entropy maximum and equality characterization in dimensions at least 150. Its finite curvature calculation includes the overlap dimension 150 and extends through 255 for quantitative stability. The large-dimensional argument uses analytic estimates, and the sharp upper bound uses an entropic Edgeworth expansion. The Python programs verify the finite calculations in these arguments. The Lean project's README describes its theorem statements, assumptions, and build procedure. [Lean project](lean/)

| Dimensions | Finite calculation in the manuscript | Program | Recorded output |
| --- | --- | --- | --- |
| 3 and 4 | Octic entropy duals, local integral bounds and rational margins for Proposition `prop:small` | [certify_small34.py](code/certify_small34.py) | [small34_results.json](results/small34_results.json) |
| 5 and 6 | Schur bounds, Hessians, averaged remainders and local/global overlap for the same proposition | [certify_small56.py](code/certify_small56.py) | [small56_results.json](results/small56_results.json) |
| 7–255 | Nonnegative integer Bernstein numerators for Theorem `thm:finite-curvature` | [ent_verify_curvature.py](code/ent_verify_curvature.py) | [curvature_results.json](results/curvature_results.json) |
| 256 and above | Polynomial identity for tilted variance and rational bounds at 256 for Proposition `prop:large-curvature`. The paper supplies the extension to larger dimensions. | [ent_verify_large.py](code/ent_verify_large.py) | [large_results.json](results/large_results.json) |

The two small-dimensional programs use exact rational moments and 192-bit Arb enclosures. The coefficient array and comparison parameters are defined near the top of each program. Both use the same integration and moment routines. [small_integrals.py](code/small_integrals.py)

The curvature run checks 16,372 spline cells and 8,347,574 Bernstein numerators. It cross-checks both the spline construction and the basis change by a second formula on all 30 cells in dimensions 7–12. The SHA-256 digest of the ordered numerators is `1c79243e41aa9141eb6896e6f60d4446cc9b0999d1fc085e7987ffa4818fd0b3`.

## Reproduce the results

From the repository root, create a Python environment and install the pinned verification dependencies. The recorded results were reproduced with Python 3.12.14, python-flint 0.9.0 and SymPy 1.14.0.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python code/run_all.py --check
```

This command recomputes all four certificates from their defining formulas and compares all five JSON files with the copies in `results/`. The summary records a digest for each program's output. A failed check or a discrepancy exits with a nonzero status. Use ordinary Python with assertions enabled. [Verification summary](results/verification_summary.json)

To run the finite curvature check through the overlap dimension alone, use

```sh
python code/ent_verify_curvature.py --last 150 --output curvature_7_150.json
```

## Revise the supplement

Edit the mathematical source in `ENT_proof.tex` and the corresponding program under `code/`. The TeX labels in the table are stable search terms if section numbers change.

- `make update-results` (or `python code/run_all.py`) regenerates the four certificate outputs and summary under `results/` once all four verifiers succeed.
- `make verify` recomputes and compares the recorded results.
- `make figure` regenerates the figure and the numerical data under `figures/` after `python -m pip install -r requirements-figure.txt`. The plot compares the two-coordinate and diagonal projections in dimension eight. Its floating-point quadrature is checked separately against high-precision integration. [Figure data](figures/figure_results.json)
- `make paper` runs pdfLaTeX twice using the bundled figure. The LaTeX source includes its bibliography.
- After reviewing the changes, `make update-checksums` refreshes `SHA256.json` for the manuscript and Python supplement, and `make checksums` verifies those files. Commit source and regenerated data together to keep each manuscript revision reproducible.
