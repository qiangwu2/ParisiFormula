/-
# Towards Target 1b: the Guerra–Toninelli interpolation is non-decreasing

New work for the ParisiFormula project (not vendored).

Target 1b (`Targets/Milestones.lean`) asks for `MonotoneOn Φ (Icc 0 1)`, where

  `Φ(t) = 𝔼[log Z_{N+M}(√t · K_{N+M} + √(1-t) · (K_N ⊕ K_M))]`.

The argument has three parts:

1. **differentiate the field** — `hasDerivAt_K_interpol` below;
2. **differentiate `Φ` under the expectation, and rewrite `Φ'` by Gaussian integration by
   parts as a trace of the covariance difference against the Hessian of `log Z`** — this is
   the missing analytic step, see the note at the end of this file;
3. **sign** — `covDiff_hessian_sum_nonneg` below.

Parts 1 and 3 are proved here.  Part 2 is what remains.

## Note on the `port/` files

`port/GuerraInterpolation.lean` etc. are *not* a source for step 2: they were cut from
or4nge19/SpinGlass, whereas `Lemmas/SpinGlass/` is vendored from the RSAT fork, and they use
or4nge19 API (`FiniteGibbs`, `SKDisorder.measU`, `disorderPair`, …) that RSAT never
vendored.  They also interpolate a *different* path (`H_t`: SK against a `SimpleDisorder`
reference at a single size `N`), not `K_interpol` (size `N+M` against `N ⊕ M`).
See `port/README.md`.

The reusable RSAT template for step 2 is `Lemmas/SpinGlass/Replicas.lean`:
`H_gauss` there has exactly the shape `√t • U + √(1-t) • V` of `K_interpol`, and
`hasDerivAt_H_gauss` / `hasDerivAt_nu` carry out the differentiation-under-the-integral for
*replica averages*.  What is missing is the same chain for `∫ free_energy_density (· ω)`.
-/
import ParisiFormula.GuerraToninelli

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## 1. Differentiating the interpolating field -/

section FieldDeriv

variable {N M : ℕ} (β h : ℝ)
variable (skL : SKDisorder (Ω := Ω) (N + M) β h)
variable (skN : SKDisorder (Ω := Ω) N β h)
variable (skM : SKDisorder (Ω := Ω) M β h)

/--
The `t`-derivative of the Guerra–Toninelli interpolating field

  `K(t) = √t · K_{N+M} + √(1-t) · (K_N ⊕ K_M)`,

namely `K'(t) = (1/(2√t)) · K_{N+M} - (1/(2√(1-t))) · (K_N ⊕ K_M)`.
-/
noncomputable def dK_interpol (t : ℝ) : Ω → EnergySpace (N + M) :=
  fun ω =>
    (1 / (2 * Real.sqrt t)) • skL.U ω
      + ((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) •
          K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω

/--
**Step 1 of Target 1b.**  Pointwise (in `ω`) differentiability of the interpolating field on
the open interval `(0,1)`.

The restriction to `Ioo 0 1` is essential and not an artefact: `√t` is not differentiable at
`t = 0`, and `√(1-t)` is not differentiable at `t = 1`.  Consequently the eventual monotonicity
argument must go through `MonotoneOn` from a derivative sign on the *interior* plus continuity
on the closed interval, not through differentiability on `Icc 0 1`.

This mirrors `SpinGlass.hasDerivAt_H_gauss` in `Lemmas/SpinGlass/Replicas.lean`, whose path
`H_gauss t = √t • sk.U + √(1-t) • sim.V` has the same shape.
-/
theorem hasDerivAt_K_interpol (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
    HasDerivAt
      (fun s : ℝ => K_interpol (N := N) (M := M) (β := β) (h := h)
        (skL := skL) (skN := skN) (skM := skM) s ω)
      (dK_interpol (N := N) (M := M) (β := β) (h := h)
        (skL := skL) (skN := skN) (skM := skM) t ω) t := by
  have ht_ne0 : t ≠ 0 := ne_of_gt ht.1
  have h1t_ne0 : (1 - t) ≠ 0 := by
    have : t < 1 := ht.2
    linarith
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt ht_ne0
  have hsub : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1 : ℝ) t := by
    simpa using (HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id t))
  have hsqrt_sub :
      HasDerivAt (fun s : ℝ => Real.sqrt ((1 : ℝ) - s))
        ((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) t :=
    (Real.hasDerivAt_sqrt h1t_ne0).comp t hsub
  have hU :
      HasDerivAt (fun s : ℝ => (Real.sqrt s) • skL.U ω)
        ((1 / (2 * Real.sqrt t)) • skL.U ω) t :=
    hsqrt.smul_const (skL.U ω)
  have hV :
      HasDerivAt
        (fun s : ℝ => (Real.sqrt ((1 : ℝ) - s)) •
          K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
        (((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) •
          K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) t :=
    hsqrt_sub.smul_const _
  -- Do *not* use `simpa` here: `simp` rewrites the `PiLp`/`WithLp` instances on
  -- `EnergySpace (N+M)` into a defeq but syntactically different form, and
  -- `HasDerivAt.add` yields a `Pi.add` rather than a lambda.  Ascribing the type
  -- makes both mismatches go away definitionally.
  have hadd :
      HasDerivAt
        (fun s : ℝ =>
          (Real.sqrt s) • skL.U ω
            + (Real.sqrt (1 - s)) •
                K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
        ((1 / (2 * Real.sqrt t)) • skL.U ω
          + ((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) •
              K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) t :=
    hU.add hV
  exact hadd

end FieldDeriv

/-! ## 2. The sign of the interpolation derivative -/

section Sign

variable {N M : ℕ} (β : ℝ)

/--
The covariance difference driving the interpolation:

  `ΔC(γ,γ') = C_{N+M}(γ,γ') - [C_N(α,α') + C_M(σ,σ')]`,   `γ = (α,σ)`.

Gaussian integration by parts turns `Φ'(t)` into `(1/2) ∑_{γ,γ'} ΔC(γ,γ') · Hess(log Z)(γ,γ')`.
-/
noncomputable def covDiff (γ γ' : Config (N + M)) : ℝ :=
  sk_cov_kernel (N := N + M) (β := β) γ γ'
    - (sk_cov_kernel (N := N) (β := β)
          (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ')
        + sk_cov_kernel (N := M) (β := β)
          (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ'))

/-- `ΔC` vanishes on the diagonal: the interpolation preserves the variance of each spin
configuration. -/
theorem covDiff_diag (hN : 0 < N) (hM : 0 < M) (γ : Config (N + M)) :
    covDiff (N := N) (M := M) (β := β) γ γ = 0 := by
  have h := cov_deriv_diag (N := N) (M := M) (β := β) hN hM γ
  simp [covDiff, h]

/-- `ΔC ≤ 0` everywhere, by convexity of `x ↦ x²` applied to the split overlap. -/
theorem covDiff_nonpos (hN : 0 < N) (hM : 0 < M) (γ γ' : Config (N + M)) :
    covDiff (N := N) (M := M) (β := β) γ γ' ≤ 0 := by
  have h := cov_deriv_offdiag_nonpos (N := N) (M := M) (β := β) hN hM (γ := γ) (γ' := γ')
  simp only [covDiff, sub_nonpos]
  exact h

/--
**Step 3 of Target 1b (the sign argument).**

`0 ≤ ∑_{γ,γ'} ΔC(γ,γ') · Hess(log Z)(γ,γ')`.

Both factors are non-positive off the diagonal (`covDiff_nonpos` and
`hessian_free_energy_std_basis_offdiag_nonpos`), so each off-diagonal term is a product of
two non-positive reals; and `ΔC` vanishes on the diagonal (`covDiff_diag`), so those terms
contribute nothing.  This is the whole content of "`Φ' ≥ 0`" once step 2 supplies the
identification of `Φ'` with this sum.
-/
theorem covDiff_hessian_sum_nonneg (hN : 0 < N) (hM : 0 < M) (H : EnergySpace (N + M)) :
    0 ≤ ∑ γ : Config (N + M), ∑ γ' : Config (N + M),
        covDiff (N := N) (M := M) (β := β) γ γ'
          * hessian_free_energy (N + M) H
              (std_basis (N + M) γ) (std_basis (N + M) γ') := by
  classical
  refine Finset.sum_nonneg (fun γ _ => Finset.sum_nonneg (fun γ' _ => ?_))
  by_cases hγ : γ = γ'
  · subst hγ
    rw [covDiff_diag (N := N) (M := M) (β := β) hN hM γ, zero_mul]
  · have hcov : covDiff (N := N) (M := M) (β := β) γ γ' ≤ 0 :=
      covDiff_nonpos (N := N) (M := M) (β := β) hN hM γ γ'
    have hhess :
        hessian_free_energy (N + M) H (std_basis (N + M) γ) (std_basis (N + M) γ') ≤ 0 :=
      hessian_free_energy_std_basis_offdiag_nonpos (N := N + M) (H := H) hγ
    simpa [neg_mul_neg] using
      mul_nonneg (neg_nonneg.2 hcov) (neg_nonneg.2 hhess)

end Sign

/-!
## What remains for Target 1b

Only step 2, in two halves:

* **2a (differentiation under the expectation).**  `HasDerivAt Φ (𝔼[⟪∇ log Z (K(t)), K'(t)⟫]) t`
  for `t ∈ Ioo 0 1`, by dominated convergence.  Template: `hasDerivAt_nu` in
  `Lemmas/SpinGlass/Replicas.lean`; the domination constant must survive the `1/√t`
  blow-up of `dK_interpol`, which is why one works on compact subintervals of `(0,1)`.

* **2b (Gaussian integration by parts).**  Rewrite that expectation as
  `(1/2) ∑_{γ,γ'} ΔC(γ,γ') · Hess(γ,γ')` using
  `PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op`
  together with `SpinGlass.trace_formula`.

Then `Φ' ≥ 0` on `Ioo 0 1` by `covDiff_hessian_sum_nonneg`, and `MonotoneOn Φ (Icc 0 1)`
follows from continuity of `Φ` on `Icc 0 1` plus the derivative sign on the interior.
Note that Mathlib has no Gaussian comparison theorem (no Slepian, no Sudakov–Fernique, no
interpolation formula), so step 2b cannot be short-circuited.
-/

end SpinGlass
