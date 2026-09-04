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
This is the separate, off-path Guerra–Toninelli target. The SK RSB interpolation
identity (Theorem 2.1) is already proved in `Targets/Talagrand.lean` using the local
Stein and cascade modules; the missing assembly here does not affect that result.

## Note on the `port/` files

`port/GuerraInterpolation.lean` etc. are *not* a source for step 2: they were cut from
or4nge19/SpinGlass, whereas active `Lemmas.*` imports come from the RSAT dependency, and they use
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

/-! ## 3. The domination bound for step 2 -/

section GradientBound

variable {N : ℕ}

/--
**`|d(free_energy_density)_H (v)| ≤ (1/N) ‖v‖`.**

By `fderiv_free_energy_density_apply` the derivative is `-(1/N) ∑_σ g_σ v_σ`, where the
Gibbs weights `g_σ` are non-negative and sum to `1`; so the sum is a convex combination of
coordinates of `v`, each bounded by `‖v‖` (`PiLp.norm_apply_le`).

RSAT does not provide this.  `port/GuerraInterpolation.lean` had it as
`abs_fderiv_free_energy_density_apply_le`, but that file is unusable here (fork mismatch,
see `port/README.md`), so it is reproved from RSAT's own `fderiv_free_energy_density_apply`.

This is the bound that step 2 of Target 1b needs in order to dominate the difference
quotients and differentiate `Φ` under the expectation.
-/
theorem abs_fderiv_free_energy_density_apply_le (H v : EnergySpace N) :
    |fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H') H v|
      ≤ (1 / (N : ℝ)) * ‖v‖ := by
  classical
  have hg_nonneg : ∀ σ : Config N, 0 ≤ gibbs_pmf N H σ :=
    fun σ => gibbs_pmf_nonneg (N := N) (H := H) σ
  have hcoord : ∀ σ : Config N, |v σ| ≤ ‖v‖ := by
    intro σ
    simpa using PiLp.norm_apply_le v σ
  have hsum : |∑ σ : Config N, gibbs_pmf N H σ * v σ| ≤ ‖v‖ := by
    calc |∑ σ : Config N, gibbs_pmf N H σ * v σ|
        ≤ ∑ σ : Config N, |gibbs_pmf N H σ * v σ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Config N, gibbs_pmf N H σ * |v σ| := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [abs_mul, abs_of_nonneg (hg_nonneg σ)]
      _ ≤ ∑ σ : Config N, gibbs_pmf N H σ * ‖v‖ :=
          Finset.sum_le_sum (fun σ _ =>
            mul_le_mul_of_nonneg_left (hcoord σ) (hg_nonneg σ))
      _ = ‖v‖ := by
          rw [← Finset.sum_mul, sum_gibbs_pmf (N := N) (H := H), one_mul]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  rw [fderiv_free_energy_density_apply]
  calc |(-(1 / (N : ℝ))) * ∑ σ : Config N, gibbs_pmf N H σ * v σ|
      = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N H σ * v σ| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hN]
    _ ≤ (1 / (N : ℝ)) * ‖v‖ := mul_le_mul_of_nonneg_left hsum hN

end GradientBound

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

  **Historical obstacle (also recorded in the roadmap).** That IBP lemma needs the *pair*
  `(skL.U, K_block)` packaged as one `IsGaussianHilbert` vector — RSAT does this for a pair
  of independent Gaussian-Hilbert vectors in `Lemmas/SpinGlass/Replicas.lean`
  (`UV`, `isGaussianHilbert_UV`), which is what Target 1b's `IndepTriple` hypothesis is for.
  But it first requires

      `IsGaussianHilbert (K_block …)`,

  and **that is not available**: `K_block` is never shown to be Gaussian anywhere in the
  project, and `IsGaussianHilbert` is a *concrete* structure (an orthonormal basis together
  with independent Gaussian coordinates), not a propositional property, so it is **not
  closed under linear images** in any immediate way — there is no such closure lemma in
  `Lemmas/SpinGlass/`.

  `K_block ω : γ ↦ U_N(α) + U_M(σ)` is the image of the independent pair `(skN.U, skM.U)`
  under a linear map, so it *is* Gaussian; the difficulty is exhibiting an orthonormal basis
  diagonalising its covariance.  Note the naive attempt fails: writing `K_block = A(U_N) + B(U_M)`
  with `(A u)(γ) = u(α)`, `(B v)(γ) = v(σ)`, one has `⟪A u, A u'⟫ = 2^M ⟪u,u'⟫` (so `A` is a
  rescaled isometry, fine) but `⟪A u, B v⟫ = (∑_α u α)(∑_σ v σ) ≠ 0` in general, so the two
  transported bases are *not* mutually orthogonal and cannot simply be concatenated.

  **Resolution: the obstacle can be avoided entirely.**  `IsGaussianHilbert (K_block …)` is
  *not* actually needed.  All three of `skL.U`, `skN.U`, `skM.U` are `IsGaussianHilbert` by
  hypothesis, and

      `K_interpol t ω = √t · skL.U ω + √(1-t) · (A (skN.U ω) + B (skM.U ω))`

  is a *linear image* of the triple `(skL.U, skN.U, skM.U)`, where `(A u)(γ) = u α` and
  `(B v)(γ) = v σ`.  So one applies the IBP lemma to the **packaged triple** — which is
  Gaussian-Hilbert because each factor is and they are independent — rather than to the pair
  `(skL.U, K_block)`.  The function being integrated is then
  `(x₁,x₂,x₃) ↦ free_energy_density (√t x₁ + √(1-t) (A x₂ + B x₃))`, smooth on the product
  space.  Nothing has to be diagonalised, and the spectral theorem is not needed.

  What this needs instead: a **generalisation of RSAT's `isGaussianHilbert_UV`** from its
  current special form (an `SKDisorder` paired with a `SimpleDisorder`, both at size `N`) to
  two arbitrary independent `IsGaussianHilbert` vectors in possibly different Hilbert
  spaces, and then one nesting to reach a triple.  Its proof is already generic in
  substance — it opens with `let hU := sk.hU; let hV := sim.hV` and thereafter uses only
  those two coordinate models plus the independence hypothesis, never `cov_eq` or the SK
  kernels — so this is a mechanical generalisation of an existing proof rather than new
  mathematics.  That is a much smaller task than the eigenbasis construction, and it is the
  recommended route.

  **Concrete recipe (2026-09-04).**  Two library facts, found after that note was written,
  shorten this well below RSAT's ~250 lines (`Replicas.lean` 85–336), because both halves of
  the construction are already in Mathlib rather than hand-rolled:

  * the **basis** — `OrthonormalBasis.prod` (`Mathlib/Analysis/InnerProductSpace/ProdL2.lean`)
    builds an `OrthonormalBasis (ι₁ ⊕ ι₂) ℝ (WithLp 2 (H₁ × H₂))` from bases of `H₁` and
    `H₂`, with `OrthonormalBasis.prod_apply` giving the explicit
    `Sum.elim (toLp ∘ inl ∘ v) (toLp ∘ inr ∘ w)`.  RSAT instead hand-builds the basis over a
    `Sigma` index `(b : Bool) × κ b`; nothing there needs repeating.
  * the **independence** — `ProbabilityTheory.iIndepFun_uncurry` combines "the two families
    are independent of each other" with "each family is internally independent" into
    independence of the combined family.  This is the single lemma RSAT's long setup is
    building towards (`Replicas.lean` 214–215), and it is what makes `c_indep` short.

  So the target shape is

      noncomputable def isGaussianHilbert_prod
          {g₁ : Ω → H₁} {g₂ : Ω → H₂}
          (h₁ : IsGaussianHilbert g₁) (h₂ : IsGaussianHilbert g₂)
          (hindep : IndepFun g₁ g₂ ℙ) :
          IsGaussianHilbert (fun ω => WithLp.toLp 2 (g₁ ω, g₂ ω)) where
        ι  := h₁.ι ⊕ h₂.ι
        w  := h₁.w.prod h₂.w
        τ  := Sum.elim h₁.τ h₂.τ
        c  := Sum.elim h₁.c h₂.c
        …

  with `c_indep` from `iIndepFun_uncurry` transported along `(b : Bool) × κ b ≃ ι₁ ⊕ ι₂`
  (or proved directly on the sum index), and `repr` from `prod_apply` plus
  `Fintype.sum_sum_type`.  The only genuinely new work is deriving "the two coordinate
  families are independent of each other" from `hindep`, by composing with the (continuous,
  hence measurable) coordinate maps `u ↦ (⟪u, wᵢ⟫)ᵢ` — which is RSAT's `h1`, lines 107–213,
  and is the part worth porting.

  (For the record, the eigenbasis route — `HasGaussianLaw.map_fun` to push the law forward,
  then `HasGaussianLaw.iIndepFun_of_covariance_inner` on an eigenbasis of the covariance
  operator — would also work, but needs the finite-dimensional spectral theorem and is
  considerably larger.)

Then `Φ' ≥ 0` on `Ioo 0 1` by `covDiff_hessian_sum_nonneg`, and `MonotoneOn Φ (Icc 0 1)`
follows from continuity of `Φ` on `Icc 0 1` plus the derivative sign on the interior.
Note that Mathlib has no Gaussian comparison theorem (no Slepian, no Sudakov–Fernique, no
interpolation formula), so step 2b cannot be short-circuited.
-/

end SpinGlass
