# port/ — historical upstream reference files (not built)

These five files are copied verbatim from `or4nge19/SpinGlass` (commit in
`docs/PROVENANCE.md`), which targets **Lean v4.28.0-rc1**. This project is on
**v4.32.1**, so these copies are *not* included in any build target. They preserve
the source and proof-structure references from the initial porting investigation;
this directory is not a queue of prerequisites for Theorem 2.2.

| File | Historical reference | Related work |
|---|---|---|
| `GuerraInterpolation.lean` | `hasDerivAt_guerraPhi`: differentiate `t ↦ E F_N(H_t)` under the expectation (dominated convergence) | Target 1b, step 1 |
| `GuerraIBP.lean` | `derivative_value_guerraPhi_eq_ibp`: rewrite the derivative by Gaussian IBP | Target 1b, step 2 |
| `GuerraTrace.lean` | `..._eq_trace_integral`: reduce the IBP expression to a covariance-vs-Hessian trace | Target 1b, step 3 |
| `GuerraPipeline.lean` | `hasDerivAt_guerraPhi_eq_trace_integral`: the three steps composed | template for 1b |
| `ParisiOperator.lean` | `Parisi.T m v A` and the semigroup law `T_add` | Already ported into `ParisiFormula/ParisiOperator.lean` |

## Historical porting result

`ParisiOperator.lean` ported cleanly and now lives in `ParisiFormula/ParisiOperator.lean`.
It needed **zero** renames: only `import Mathlib.MeasureTheory.Integral.Prod`.  That is
because it depends on *Mathlib only*.

The other four files did not port by import/rename changes alone. The obstacle was
not Mathlib renames but a **fork mismatch**:

* active `Lemmas.*` imports come from the **njimaMath/research_public** RSAT dependency
  at `f3b34d2`; the root `Lemmas/SpinGlass/` copies are historical and are not compiled;
* `port/` is vendored from **or4nge19/SpinGlass** `d1342fd`.

RSAT is *derived from* or4nge19/SpinGlass but is a trimmed/modified fork.  The four Guerra
files use or4nge19 API that RSAT never vendored:

| Incompatible or absent in the RSAT API used by this project | Used by |
|---|---|
| the whole `FiniteGibbs` namespace (`FiniteGibbs.Z`, `.free_energy_density`, `.hasDerivAt_free_energy_density_comp`) | GuerraInterpolation, GuerraTrace |
| `SKDisorder.measU`, `SimpleDisorder.measV` (RSAT's `SKDisorder` has only `U`, `hU`, `cov_eq`) | GuerraInterpolation |
| `disorderPair`, `disorderPairLaw` | GuerraInterpolation |
| `abs_free_energy_density_le`, `integrable_norm_of_isGaussian_map`, `norm_dH_t_le_on_ball` | GuerraInterpolation |

Vendoring the missing or4nge19 modules alongside is **not** a fix: both forks put
`SKDisorder`, `Defs`, `Z`, `free_energy_density` in the same `SpinGlass` namespace with
different signatures, so they would collide.

## Current implementation

The SK Theorem 2.1 proof now uses local cascade differentiation, coordinate Gaussian
IBP, and replica identities in `Targets/Talagrand.lean` and the `Targets/Cascade*.lean`
modules. Its Stein ingredients are in `ParisiFormula/GaussianStein.lean`,
`CoordStein.lean`, and `PiStein.lean`. `Targets/GuerraAudit.lean` checks that the theorem
and its upper-bound consequences have no placeholder dependencies.

The RSAT dependency also supplies related interpolation ingredients:

* `Lemmas/SpinGlass/Replicas.lean` — `H_gauss`, `H_field`, `H_t` (the same interpolating
  path), `hasDerivAt_H_t`, `hasDerivAt_nu` (differentiation under the disorder expectation);
* `Lemmas/SpinGlass/Defs.lean` — `trace_formula`, `trace_sk`, `trace_simple`,
  `guerra_derivative_bound_algebra`;
* `Lemmas/SpinGlass/GuerraBound.lean` — `guerra_derivative_bound_algebra_core`.

The separate Guerra–Toninelli monotonicity target (`Φ_monotoneOn`) remains open and
off the current critical path. These four files may still serve as proof-structure
references for that development; they are not missing components of the completed
Theorem 2.1. The next critical theorem is `talagrand_theorem_2_2`; see
[`../docs/ROADMAP.md`](../docs/ROADMAP.md).
