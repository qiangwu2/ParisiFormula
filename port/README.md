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

**Porting plan.** Change the imports from `SpinGlass.*` to `Lemmas.SpinGlass.*`, move the
file into `ParisiFormula/`, run `lake build ParisiFormula`, and fix whatever Mathlib renamed
between early and late 2026 (typically a handful of lemma names). Port `ParisiOperator.lean`
first: it is 191 lines and depends only on Mathlib.
