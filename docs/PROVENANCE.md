# Provenance of vendored files

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
| `ParisiFormula/GuerraToninelli.lean` | njimaMath/research_public | `perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | 2 import lines + provenance header |
| `port/GuerraInterpolation.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraInterpolation.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraIBP.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraIBP.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraTrace.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraTrace.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraPipeline.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraPipeline.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `lean-toolchain`, `lake-manifest.json`, `LICENSE` | njimaMath/research_public | `RSAT/` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | manifest: package name only |

The RSAT core files (`Lemmas/SpinGlass/`) are themselves derived from or4nge19/SpinGlass;
RSAT's own NOTICE says so and is reproduced in our NOTICE.

Toolchains at the time of vendoring: RSAT and perceptronFixed used Lean v4.32.1 / v4.32.0
with matching Mathlib; or4nge19/SpinGlass used Lean v4.28.0-rc1 (hence the `port/` folder).
