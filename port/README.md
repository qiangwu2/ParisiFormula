# port/ — upstream files awaiting a toolchain port

These five files are copied verbatim from `or4nge19/SpinGlass` (commit in
`docs/PROVENANCE.md`), which targets **Lean v4.28.0-rc1**. This project is on
**v4.32.1**, so they are *not* included in any build target. They are here because
they contain exactly the machinery Milestones 1–2 need:

| File | What it gives us | Needed for |
|---|---|---|
| `GuerraInterpolation.lean` | `hasDerivAt_guerraPhi`: differentiate `t ↦ E F_N(H_t)` under the expectation (dominated convergence) | Target 1b, step 1 |
| `GuerraIBP.lean` | `derivative_value_guerraPhi_eq_ibp`: rewrite the derivative by Gaussian IBP | Target 1b, step 2 |
| `GuerraTrace.lean` | `..._eq_trace_integral`: reduce the IBP expression to a covariance-vs-Hessian trace | Target 1b, step 3 |
| `GuerraPipeline.lean` | `hasDerivAt_guerraPhi_eq_trace_integral`: the three steps composed | template for 1b |
| `ParisiOperator.lean` | `Parisi.T m v A` and the semigroup law `T_add` | Milestone 2 |

**Porting plan — REVISED after an attempt (CI run 33823189093).**

`ParisiOperator.lean` ported cleanly and now lives in `ParisiFormula/ParisiOperator.lean`.
It needed **zero** renames: only `import Mathlib.MeasureTheory.Integral.Prod`.  That is
because it depends on *Mathlib only*.

The other four files **cannot be ported this way**, and the estimate above was wrong.  The
blocker is not Mathlib renames but a **fork mismatch**:

* `Lemmas/SpinGlass/` is vendored from **njimaMath/research_public** (RSAT) `f3b34d2`;
* `port/` is vendored from **or4nge19/SpinGlass** `d1342fd`.

RSAT is *derived from* or4nge19/SpinGlass but is a trimmed/modified fork.  The four Guerra
files use or4nge19 API that RSAT never vendored:

| Missing in `Lemmas/SpinGlass/` | Used by |
|---|---|
| the whole `FiniteGibbs` namespace (`FiniteGibbs.Z`, `.free_energy_density`, `.hasDerivAt_free_energy_density_comp`) | GuerraInterpolation, GuerraTrace |
| `SKDisorder.measU`, `SimpleDisorder.measV` (RSAT's `SKDisorder` has only `U`, `hU`, `cov_eq`) | GuerraInterpolation |
| `disorderPair`, `disorderPairLaw` | GuerraInterpolation |
| `abs_free_energy_density_le`, `integrable_norm_of_isGaussian_map`, `norm_dH_t_le_on_ball` | GuerraInterpolation |

Vendoring the missing or4nge19 modules alongside is **not** a fix: both forks put
`SKDisorder`, `Defs`, `Z`, `free_energy_density` in the same `SpinGlass` namespace with
different signatures, so they would collide.

**What to do instead.**  Rebuild this chain on RSAT's own API, which already provides most
of the ingredients in its own idiom:

* `Lemmas/SpinGlass/Replicas.lean` — `H_gauss`, `H_field`, `H_t` (the same interpolating
  path), `hasDerivAt_H_t`, `hasDerivAt_nu` (differentiation under the disorder expectation);
* `Lemmas/SpinGlass/Defs.lean` — `trace_formula`, `trace_sk`, `trace_simple`,
  `guerra_derivative_bound_algebra`;
* `Lemmas/SpinGlass/GuerraBound.lean` — `guerra_derivative_bound_algebra_core`.

What is genuinely missing is the Gaussian-IBP step connecting the derivative of
`∫ free_energy_density (H_t ·)` to the trace expression.  The four files here remain useful
as a **proof-structure reference** for that, but not as source to compile.
