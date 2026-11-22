# Lean formalization of the ENT conjecture

For independent uniform random variables on `[-1,1]` and real coefficients with sum of squares one, the normalized diagonal sum maximizes differential entropy. Equality holds exactly when all coefficients have absolute value `1/√n`. The formalization also establishes the quantitative entropy and relative-entropy bounds and the limiting optimal stability coefficient.

## Statements

The following declarations are in the namespace `ENT.PaperStatements`. Their types spell out the probability laws, densities, entropy integrals and coefficient normalization used in the paper. [PaperStatements.lean](ENT/PaperStatements.lean) · [Paper](https://arxiv.org/abs/2611.18798v1)

| Paper | Lean declaration | Conclusion |
| --- | --- | --- |
| Theorem 1.1 | `paper_theorem_1_1`, `paper_theorem_1_1_canonical` | Entropy maximum and both directions of the equality characterization for every positive dimension. |
| Theorem 1.2 | `stability_small` | Entropy gap at least `δ/1000` for dimensions 3–6. |
| Theorem 1.2 | `stability_large` | Entropy gap at least `7δ/(180n) + D(p ∥ q)` for dimensions at least 7. |
| Theorem 1.2 | `stability_asymptotic` | For each `η > 0`, the lower bound `(3/50 − η)δ/n + D(p ∥ q)` holds uniformly above a dimension threshold. |
| Theorem 1.3 | `sharp_coefficient_limit` | The infimum of the normalized entropy gap over unit vectors with positive deficit tends to `3/50`. |
| Theorem 3.1 | `diagonal_density_curvature` | The density of the normalized diagonal sum has `(−log q)'''(x) ≥ 7x/n` for `7 ≤ n ≤ 255` and `0 < x < √n`. |

Here `δ = ∑ᵢ (aᵢ² − 1/n)²`, `p` is the density of the weighted sum and `q` is the density of the diagonal sum. The KL term is `∫ p log(p/q)`. The curvature proof uses exact cell certificates through dimension 149 and an analytic argument from dimension 150 onward. [Definitions](ENT/Statement.lean) · [Curvature](ENT/Quantitative/ActualFiniteCurvature255.lean) · [All dimensions](ENT/AllDimensions.lean)

## Build and verify

Install Lean's Elan toolchain manager, Git and Python 3. From the repository root, check or materialize the generated sources. This compares each of the 710 generated modules with its recorded SHA-256 and writes missing files. See the certificate formulas and edit instructions in [certificates/README.md](certificates/README.md).

```sh
cd lean
python3 -m venv .venv
.venv/bin/python -m pip install python-flint==0.9.0
.venv/bin/python scripts/generate_certificates.py
```

For a source-only check, run the following command in the same directory. It fetches the pinned dependencies, uses the mathlib cache for imported libraries, and compiles the complete project into a fresh temporary directory. Use `--jobs 1` to reduce concurrent memory use.

```sh
python3 scripts/verify_lean.py --fetch-cache --jobs 2
```

For development, keep the build artifacts with Lake. After generating the certificates and fetching the package cache, the default target builds `ENT`, the paper statements and the axiom audit. To inspect a declaration interactively, write `import ENT.PaperStatements` followed by e.g. `#print ENT.PaperStatements.sharp_coefficient_limit`.

```sh
lake build
```

The toolchain is Lean 4.37.0-rc1. Mathlib is pinned to `c47f9ad906c5ec32a953f99911b446cd26dcc123`, with exact transitive revisions in the Lake manifest. The axiom audit walks every public declaration in the `ENT` namespace and fails on axioms outside `propext`, `Classical.choice` and `Quot.sound`. [Toolchain](lean-toolchain) · [Dependency revisions](lake-manifest.json) · [Audit.lean](ENT/Audit.lean)

## Source layout

- [ENT.lean](ENT.lean) imports the all-dimensional, quantitative and sharpness results. The mathematical development is in the individual modules beneath `ENT/`.
- [ENT/Certificate](ENT/Certificate) proves soundness of the polynomial and Bernstein checks. [ENT/Pilot](ENT/Pilot) contains their concrete integer inputs and exact proofs for individual cells. [ENT/FiniteCertificates](ENT/FiniteCertificates) assembles the results by dimension.
- [ENT/Supplement.lean](ENT/Supplement.lean) collects supplementary results on cube sections, pair balancing, spline recurrences, quadrature, tilt moments and density representatives.
