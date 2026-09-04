# Dependencies and source provenance

## Active build dependencies

`lakefile.lean` declares two local libraries, `ParisiFormula` and `Targets`. Their
upstream dependencies are locked in `lake-manifest.json`:

| Dependency | Source | Locked revision |
|---|---|---|
| `mathlib` | `leanprover-community/mathlib4`, tag `v4.32.1` | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `QuantitativeStrictAT` | `njimaMath/research_public`, subdirectory `RSAT` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` |

`Lemmas.*` imports resolve to the RSAT dependency under
`.lake/packages/QuantitativeStrictAT/RSAT/`, not the historical root-level `Lemmas/`
copies. Neither `Lemmas/` nor `port/` is a local build target. The `main` selector in
the RSAT dependency declaration does not replace the pinned revision when reproducing
the checked-in manifest; `lake update` would deliberately refresh dependencies.

## Historical copies and local ports

All vendored files are Apache-2.0.  Original headers are retained unchanged.

| File in this repo | Origin | Path in origin | Commit | Edits |
|---|---|---|---|---|
| `Lemmas/SpinGlass/Calculus.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Calculus.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Defs.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Defs.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/gaussian_concentration.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/gaussian_concentration.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GuerraBound.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GuerraBound.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Replicas.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Replicas.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/SKModel.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/SKModel.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `ParisiFormula/GuerraToninelli.lean` | njimaMath/research_public | `perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | 2 import lines + provenance header; proof repairs for Lean v4.32.1 (see below) |
| `ParisiFormula/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | provenance header and `Mathlib.MeasureTheory.Integral.Prod` import; compiled local port |
| `port/GuerraInterpolation.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraInterpolation.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraIBP.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraIBP.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraTrace.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraTrace.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraPipeline.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraPipeline.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `lean-toolchain`, `lake-manifest.json`, `LICENSE` | njimaMath/research_public | `RSAT/` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | initial source; manifest subsequently regenerated for this project's dependencies (see above) |

The RSAT core files (`Lemmas/SpinGlass/`) are themselves derived from or4nge19/SpinGlass;
RSAT's own NOTICE says so and is reproduced in our NOTICE.

Toolchains at the time of vendoring: RSAT and perceptronFixed used Lean v4.32.1 / v4.32.0
with matching Mathlib; or4nge19/SpinGlass used Lean v4.28.0-rc1 (hence the `port/` folder).

`ParisiFormula/ParisiOperatorGrowth.lean` is a local extension of the ported semigroup
law to linear-growth functions. The cascade files in `Targets/` and the local Stein
lemmas support the completed SK Theorem 2.1; they are not pending upstream ports.

## Post-vendoring repairs to `ParisiFormula/GuerraToninelli.lean`

The upstream file was verified against a slightly different Mathlib. These compatibility
repairs preserve the theorem statements:

* `cfgEquiv.left_inv` and `cfgJoin_cfgLeft_cfgRight` — `Fin.addCases_castAdd_natAdd` is now
  stated pointwise, and `simpa` cannot close the goal because the `simp` equation lemmas for
  `cfgLeft`/`cfgRight` are in applied form; `exact` (default transparency) does.
* `integrable_log_skZ`, the `hEnergy` continuity step — `simpa` normalised the goal into
  `Pi.add` form, which no longer matches `Continuous.add`; replaced by `simp only [skEnergy]`
  followed by `exact`.

The covariance comparison lemmas `cov_deriv_diag` and `cov_deriv_offdiag_nonpos` were
also made public for reuse.
