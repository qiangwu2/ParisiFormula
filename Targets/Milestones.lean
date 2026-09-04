import ParisiFormula.GuerraToninelli
import ParisiFormula.AnnealedBound
import ParisiFormula.GaussianCosh
import ParisiFormula.ParisiOperator
import ParisiFormula.GaussianConcentration1D
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Target statements for the ParisiFormula project

This file states, with `sorry`, the theorems the project aims to prove.  It is the
Lean-side counterpart of `blueprint/blueprint.tex`.  Nothing here is proved; the
point is to pin down *exact statements* against the vendored API so that every
milestone has a precise, machine-checkable finish line.

This file is built by `lake build Targets`, never by the default build, because it
contains `sorry` on purpose (and, being written before the project had a working
Lean environment, may need small syntactic repairs).

## Conventions (inherited from the vendored core, `Lemmas/SpinGlass/`)

* A configuration on `N` spins is `Config N := Fin N → Bool`, with `spin N σ i ∈ {±1}`.
* An SK disorder `sk : SKDisorder N β h` is a centred Gaussian random vector
  `sk.U : Ω → EnergySpace N` with covariance `E[U σ · U τ] = (N β²/2) · R(σ,τ)²`,
  where `R` is the overlap.  In the language of mixed p-spin models this is
  `N β² ξ(R)` with `ξ(x) = x²/2`.
* The quenched free entropy is `free_entropy β h sk.U = (1/N) E log ∑_σ exp(U σ + h ∑ᵢ σᵢ)`
  (defined in `ParisiFormula/GuerraToninelli.lean`).

## References

* M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263.
* F. Guerra, *Broken replica symmetry bounds in the mean field spin glass model*,
  Comm. Math. Phys. 233 (2003), 1–12.
* F. Guerra, F. L. Toninelli, *The thermodynamic limit in mean field spin glass models*,
  Comm. Math. Phys. 230 (2002), 71–79.
* M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I (Ch. 1) and Vol. II (Ch. 12–14).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal ProbabilityTheory

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Milestone 1 — existence of the thermodynamic limit (Guerra–Toninelli)

`ParisiFormula/GuerraToninelli.lean` already contains the whole argument *except* two
hypotheses that were left open upstream: an upper bound on the free entropy, and
monotonicity of the interpolation `Φ`.  Targets 1a and 1b discharge them; 1c assembles.
-/

/-- Mutual independence of the three disorders entering the Guerra–Toninelli interpolation
(sizes `N+M`, `N`, `M`).  Expressed as pairwise independence of `skN.U` and `skM.U`, plus
independence of `skL.U` from the pair. -/
structure IndepTriple {N M : ℕ} {β h : ℝ}
    (skL : SKDisorder (Ω := Ω) (N + M) β h)
    (skN : SKDisorder (Ω := Ω) N β h)
    (skM : SKDisorder (Ω := Ω) M β h) : Prop where
  indep_NM : skN.U ⟂ᵢ[(ℙ : Measure Ω)] skM.U
  indep_L_pair : skL.U ⟂ᵢ[(ℙ : Measure Ω)] (fun ω => (skN.U ω, skM.U ω))

/-- **Target 1a (annealed bound).**  Jensen's inequality `E log Z ≤ log E Z` and the Gaussian
moment generating function give `(1/N) E log Z_N ≤ log 2 + β²/4 + |h|`.

Reference: Talagrand Vol. I, (1.24) and the discussion after it. -/
theorem free_entropy_le_annealed {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U
      ≤ Real.log 2 + β ^ 2 / 4 + |h| :=
  _root_.SpinGlass.free_entropy_le_annealed hN β h sk

/-- **Target 1b (Gaussian comparison).**  The Guerra–Toninelli interpolation
`Φ(t) = E log Z_{N+M}(√t · K_{N+M} + √(1-t) · (K_N ⊕ K_M))` is non-decreasing on `[0,1]`.

Proof plan (blueprint, Chapter 1): differentiate under the expectation (dominated
convergence, cf. `SpinGlass.hasDerivAt_nu` in `Lemmas/SpinGlass/Replicas.lean`), rewrite
`Φ'(t)` by Gaussian integration by parts
(`PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov`) as a trace of
the covariance difference `C_L - C_blk` against the Hessian of `log Z`
(`SpinGlass.trace_formula`), then use the two facts already proved in
`ParisiFormula/GuerraToninelli.lean`: the diagonal of `C_L - C_blk` vanishes and its
off-diagonal is `≤ 0` (convexity of `x ↦ x²`), while the off-diagonal Hessian entries of
`log Z` are `≤ 0`.  Hence `Φ' ≥ 0`.

Reference: Guerra–Toninelli (2002); Talagrand Vol. I, Theorem 1.3.7 (in the 2nd edition:
Section 1.3, "the Guerra–Toninelli argument"). -/
theorem Φ_monotoneOn {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (β h : ℝ) (hβ : 0 < β)
    (skL : SKDisorder (Ω := Ω) (N + M) β h)
    (skN : SKDisorder (Ω := Ω) N β h)
    (skM : SKDisorder (Ω := Ω) M β h)
    (hindep : IndepTriple skL skN skM) :
    MonotoneOn
      (Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM))
      (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- **Target 1c (thermodynamic limit).**  Assembles 1a and 1b with the already-formalised
Fekete argument `free_entropy_tendsto_of_bddAbove`. -/
theorem free_entropy_tendsto (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h)
    (hindep : ∀ N M : ℕ, IndepTriple (sk (N + M)) (sk N) (sk M)) :
    ∃ ℓ : ℝ, Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 ℓ) := by
  sorry

/-! ## Milestone 2 — the finite-step Parisi functional (no PDE)

Following Talagrand (Annals 2006, §1), a `k`-step replica-symmetry-breaking scheme is a pair
of non-decreasing sequences

  `0 = m₀ ≤ m₁ ≤ ⋯ ≤ m_k ≤ m_{k+1} = 1`,   `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`.

The functional is defined by a *finite backward recursion* through the Gaussian smoothing
operator `T_{m,v}`, so no Parisi PDE is needed.  (The vendored file `port/ParisiOperator.lean`
contains an upstream formalisation of `T_{m,v}` and its semigroup law, awaiting port.)
-/

/-- A `k`-step RSB scheme.  Sequences are indexed by `ℕ` (values beyond the stated range are
irrelevant) to avoid dependent-index bookkeeping. -/
structure RSBScheme (k : ℕ) where
  /-- `m 0 = 0`, …, `m (k+1) = 1`. -/
  m : ℕ → ℝ
  /-- `q 0 = 0`, …, `q (k+2) = 1`. -/
  q : ℕ → ℝ
  m_zero : m 0 = 0
  m_top : m (k + 1) = 1
  m_mono : ∀ p, p ≤ k → m p ≤ m (p + 1)
  q_zero : q 0 = 0
  q_top : q (k + 2) = 1
  q_mono : ∀ p, p ≤ k + 1 → q p ≤ q (p + 1)

/-- Gaussian smoothing step at "temperature" `m` and variance `v`:

  `T_{m,v} A (x) = (1/m) log ∫ exp(m · A(x + √v · z)) dγ(z)`  for `m ≠ 0`,
  `T_{0,v} A (x) = ∫ A(x + √v · z) dγ(z)`,

with `γ` the standard Gaussian.  The `m = 0` case is the `m → 0` limit of the first. -/
noncomputable def parisiStep (m v : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then
    ∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1)
  else
    (1 / m) * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))

/--
**Reconciliation of `parisiStep` with the ported operator `Parisi.T`** (roadmap Phase 2).

For `m ≠ 0` the two agree, via the Gaussian rescaling
`integral_comp_sqrt_mul_gaussianReal`.

They do **not** agree at `m = 0`, and this matters.  `Parisi.T` has no `m = 0` branch, so
`Parisi.T 0 v A x = (1/0) * log (…) = 0`, whereas `parisiStep 0 v A x` is the `m → 0` limit
`∫ A (x + √v z) dγ`.  So `parisiStep` must **not** be redefined as `Parisi.T`: the `m = 0`
branch is precisely the outermost step `F₀ = T_{0, β²q₁} F₁` of the Parisi recursion, and
collapsing it to `0` would break `parisiFunctional` (and with it Target 2a, which is proved
below and does use that branch).
-/
theorem parisiStep_eq_T {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0) {A : ℝ → ℝ} (hA : Measurable A)
    (x : ℝ) :
    parisiStep m (v : ℝ) A x = Parisi.T m v A x := by
  have hf : Measurable (fun y : ℝ => Real.exp (m * A y)) :=
    Real.continuous_exp.measurable.comp (hA.const_mul m)
  rw [parisiStep, if_neg hm, Parisi.T,
      integral_comp_sqrt_mul_gaussianReal v hf x]

/--
**The smoothing step is non-expansive in the sup-norm of its argument.**

If `|A - A'| ≤ ε` pointwise then `|T_{m,v} A - T_{m,v} A'| ≤ ε`, *uniformly in `m` and `v`*.

This is the inductive engine for **Target 2b**: a perturbation of the scheme parameters
`(m,q)` changes each level of the backward recursion by a controlled amount, and this lemma
carries that change through the remaining levels without amplification.  The uniformity in
`m` is what makes the resulting Lipschitz constant independent of `k`, which is exactly the
property Target 2b needs (see the note there on quantifier order).

For `m ≠ 0` the proof is the standard one: `|m(A - A')| ≤ |m| ε` gives `I ≤ e^{|m|ε} I'` for
the two exponential integrals, hence `|log I - log I'| ≤ |m| ε`, and the prefactor `1/m`
cancels the `|m|`.

The integrability hypotheses are not removable: the `m = 0` branch needs `A`, `A'`
integrable, and the `m ≠ 0` branch needs the exponentials integrable, else Lean's junk value
`∫ = 0` breaks the comparison.  Discharging them for `parisiF` at every level is the
"moderate-growth" item of Phase 2 in `docs/ROADMAP.md`.
-/
theorem parisiStep_dist_le {m v ε x : ℝ} {A A' : ℝ → ℝ}
    (hε : ∀ y, |A y - A' y| ≤ ε)
    (hA : Integrable (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1))
    (hA' : Integrable (fun z => A' (x + Real.sqrt v * z)) (gaussianReal 0 1))
    (hEA : Integrable (fun z => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1))
    (hEA' : Integrable (fun z => Real.exp (m * A' (x + Real.sqrt v * z))) (gaussianReal 0 1)) :
    |parisiStep m v A x - parisiStep m v A' x| ≤ ε := by
  classical
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm]
    rw [← integral_sub hA hA']
    calc |∫ z, (A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)|
        ≤ ∫ z, |A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z)| ∂(gaussianReal 0 1) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (μ := (gaussianReal 0 1))
              (f := fun z => A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z))
      _ ≤ ∫ _z : ℝ, ε ∂(gaussianReal 0 1) :=
          integral_mono (hA.sub hA').abs (integrable_const ε)
            (fun z => hε (x + Real.sqrt v * z))
      _ = ε := by simp
  · have hmabs : (0 : ℝ) < |m| := abs_pos.2 hm
    have hIpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      integral_exp_pos hEA
    have hI'pos : 0 < ∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      integral_exp_pos hEA'
    have key : ∀ B B' : ℝ → ℝ,
        (∀ y, |B y - B' y| ≤ ε) →
        Integrable (fun z => Real.exp (m * B (x + Real.sqrt v * z))) (gaussianReal 0 1) →
        Integrable (fun z => Real.exp (m * B' (x + Real.sqrt v * z))) (gaussianReal 0 1) →
        (∫ z, Real.exp (m * B (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ Real.exp (|m| * ε)
            * ∫ z, Real.exp (m * B' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) := by
      intro B B' hBB hEB hEB'
      have hpt : ∀ z : ℝ,
          Real.exp (m * B (x + Real.sqrt v * z))
            ≤ Real.exp (|m| * ε) * Real.exp (m * B' (x + Real.sqrt v * z)) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z)) ≤ |m| * ε := by
          calc m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z))
              ≤ |m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z))| := le_abs_self _
            _ = |m| * |B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z)| := abs_mul _ _
            _ ≤ |m| * ε :=
                mul_le_mul_of_nonneg_left (hBB (x + Real.sqrt v * z)) (abs_nonneg m)
        linarith
      calc (∫ z, Real.exp (m * B (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ ∫ z, Real.exp (|m| * ε) * Real.exp (m * B' (x + Real.sqrt v * z))
              ∂(gaussianReal 0 1) :=
            integral_mono hEB (hEB'.const_mul _) hpt
        _ = Real.exp (|m| * ε)
              * ∫ z, Real.exp (m * B' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
            integral_const_mul _ _
    have hεsymm : ∀ y, |A' y - A y| ≤ ε := by
      intro y
      rw [abs_sub_comm]
      exact hε y
    have h1 := key A A' hε hEA hEA'
    have h2 := key A' A hεsymm hEA' hEA
    have hlog1 :
        Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ |m| * ε := by
      have h := Real.log_le_log hIpos h1
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hI'pos), Real.log_exp] at h
      linarith
    have hlog2 :
        Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ |m| * ε := by
      have h := Real.log_le_log hI'pos h2
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hIpos), Real.log_exp] at h
      linarith
    have habs :
        |Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))|
          ≤ |m| * ε := abs_le.2 ⟨by linarith, hlog1⟩
    simp only [parisiStep, if_neg hm]
    rw [← mul_sub, abs_mul, abs_one_div]
    calc 1 / |m|
          * |Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
              - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))|
        ≤ 1 / |m| * (|m| * ε) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ = ε := by field_simp

/--
**The smoothing step preserves linear growth.**

Together with `hasLinearGrowth_log_cosh` this closes the induction that discharges
`parisiStep_dist_le`'s integrability hypotheses at every level of `parisiF`.

For `m ≠ 0` the constant produced here degrades like `1/|m|`.  That is an artefact of the
crude two-sided bound and is harmless: growth preservation is only ever used at a *fixed*
`m`, purely to obtain integrability.  The estimate that must be uniform in `m` is
`parisiStep_dist_le`, and that one is.
-/
theorem hasLinearGrowth_parisiStep {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v : ℝ) :
    HasLinearGrowth (parisiStep m v A) := by
  classical
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  have hshift : ∀ x z : ℝ,
      |A (x + Real.sqrt v * z)| ≤ (C + D * |x|) + (D * |Real.sqrt v|) * |z| := by
    intro x z
    refine (hb _).trans ?_
    have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
      calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
        _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
    nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]
  by_cases hm : m = 0
  · -- `m = 0`: the step is the plain Gaussian average.
    set M : ℝ := ∫ z, |z| ∂(gaussianReal 0 1) with hMdef
    have hM0 : 0 ≤ M := integral_nonneg (fun z => abs_nonneg z)
    refine ⟨C + (D * |Real.sqrt v|) * M, D, by positivity, hD, fun x => ?_⟩
    simp only [parisiStep, if_pos hm]
    have hint : Integrable (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) :=
      integrable_of_hasLinearGrowth ⟨C, D, hC, hD, hb⟩ hmeas x v
    have hdom : Integrable
        (fun z : ℝ => (C + D * |x|) + (D * |Real.sqrt v|) * |z|) (gaussianReal 0 1) :=
      (integrable_const _).add ((integrable_id_stdGaussian.abs).const_mul _)
    calc |∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1)|
        ≤ ∫ z, |A (x + Real.sqrt v * z)| ∂(gaussianReal 0 1) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (gaussianReal 0 1))
              (f := fun z => A (x + Real.sqrt v * z))
      _ ≤ ∫ z, ((C + D * |x|) + (D * |Real.sqrt v|) * |z|) ∂(gaussianReal 0 1) :=
          integral_mono hint.abs hdom (fun z => hshift x z)
      _ = (C + D * |x|) + (D * |Real.sqrt v|) * M := by
          rw [integral_add (integrable_const _)
                ((integrable_id_stdGaussian.abs).const_mul _),
            integral_const_mul]
          simp [hMdef, probReal_univ]
      _ = (C + (D * |Real.sqrt v|) * M) + D * |x| := by ring
  · -- `m ≠ 0`.
    have hmabs : (0 : ℝ) < |m| := abs_pos.2 hm
    set a : ℝ := |m| * (D * |Real.sqrt v|) with hadef
    set K : ℝ := ∫ z, Real.exp (a * |z|) ∂(gaussianReal 0 1) with hKdef
    set K' : ℝ := ∫ z, Real.exp (-a * |z|) ∂(gaussianReal 0 1) with hK'def
    have hKpos : 0 < K := integral_exp_pos (integrable_exp_abs_mul_stdGaussian a)
    have hK'pos : 0 < K' := integral_exp_pos (integrable_exp_abs_mul_stdGaussian (-a))
    set E : ℝ := |Real.log K| + |Real.log K'| with hEdef
    refine ⟨C + E / |m|, D, by positivity, hD, fun x => ?_⟩
    simp only [parisiStep, if_neg hm]
    set I : ℝ := ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) with hIdef
    have hIint : Integrable
        (fun z => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) :=
      integrable_exp_mul_of_hasLinearGrowth ⟨C, D, hC, hD, hb⟩ hmeas m x v
    have hIpos : 0 < I := integral_exp_pos hIint
    set B : ℝ := |m| * (C + D * |x|) with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hkey : ∀ z : ℝ, |m| * |A (x + Real.sqrt v * z)| ≤ B + a * |z| := by
      intro z
      have h := mul_le_mul_of_nonneg_left (hshift x z) (abs_nonneg m)
      calc |m| * |A (x + Real.sqrt v * z)|
          ≤ |m| * ((C + D * |x|) + (D * |Real.sqrt v|) * |z|) := h
        _ = B + a * |z| := by rw [hBdef, hadef]; ring
    have hup : I ≤ Real.exp B * K := by
      have hpt : ∀ z : ℝ,
          Real.exp (m * A (x + Real.sqrt v * z))
            ≤ Real.exp B * Real.exp (a * |z|) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : m * A (x + Real.sqrt v * z) ≤ |m| * |A (x + Real.sqrt v * z)| := by
          calc m * A (x + Real.sqrt v * z) ≤ |m * A (x + Real.sqrt v * z)| := le_abs_self _
            _ = |m| * |A (x + Real.sqrt v * z)| := abs_mul _ _
        linarith [hkey z]
      calc I ≤ ∫ z, Real.exp B * Real.exp (a * |z|) ∂(gaussianReal 0 1) :=
            integral_mono hIint ((integrable_exp_abs_mul_stdGaussian a).const_mul _) hpt
        _ = Real.exp B * K := integral_const_mul _ _
    have hlow : Real.exp (-B) * K' ≤ I := by
      have hpt : ∀ z : ℝ,
          Real.exp (-B) * Real.exp (-a * |z|)
            ≤ Real.exp (m * A (x + Real.sqrt v * z)) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : -(|m| * |A (x + Real.sqrt v * z)|) ≤ m * A (x + Real.sqrt v * z) := by
          calc -(|m| * |A (x + Real.sqrt v * z)|)
              = -|m * A (x + Real.sqrt v * z)| := by rw [abs_mul]
            _ ≤ m * A (x + Real.sqrt v * z) := neg_abs_le _
        linarith [hkey z]
      calc Real.exp (-B) * K'
          = ∫ z, Real.exp (-B) * Real.exp (-a * |z|) ∂(gaussianReal 0 1) :=
            (integral_const_mul _ _).symm
        _ ≤ I :=
            integral_mono ((integrable_exp_abs_mul_stdGaussian (-a)).const_mul _) hIint hpt
    have hlogup : Real.log I ≤ B + Real.log K := by
      have h := Real.log_le_log hIpos hup
      rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hKpos), Real.log_exp] at h
    have hloglow : -B + Real.log K' ≤ Real.log I := by
      have h := Real.log_le_log (by positivity) hlow
      rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hK'pos), Real.log_exp] at h
    have habsI : |Real.log I| ≤ B + E := by
      refine abs_le.2 ⟨?_, ?_⟩
      · have h1 : -Real.log K' ≤ |Real.log K'| := neg_le_abs _
        have h2 : (0 : ℝ) ≤ |Real.log K| := abs_nonneg _
        rw [hEdef]
        linarith
      · have h1 : Real.log K ≤ |Real.log K| := le_abs_self _
        have h2 : (0 : ℝ) ≤ |Real.log K'| := abs_nonneg _
        rw [hEdef]
        linarith
    rw [abs_mul, abs_one_div]
    calc 1 / |m| * |Real.log I|
        ≤ 1 / |m| * (B + E) := mul_le_mul_of_nonneg_left habsI (by positivity)
      _ = (C + E / |m|) + D * |x| := by
          rw [hBdef]
          field_simp
          ring

/--
**The smoothing step does not increase the Lipschitz constant.**

If `A` is `L`-Lipschitz then so is `parisiStep m v A`, *uniformly in `m` and `v`*.

This is a corollary of `parisiStep_dist_le`, by a translation trick: comparing `A` with
`y ↦ A (y + (x' - x))` turns a change of *evaluation point* into a change of *function*, and
the two differ uniformly by at most `L |x - x'|`.

With `log_cosh_dist_le` as the base case this gives: every level `F_p` of the Parisi
recursion is 1-Lipschitz.  That is what makes a perturbation of the variance `v` tractable
in Target 2b — the argument `x + √v z` then moves by `(√v - √v') z`, and Lipschitz control
converts that into something integrable against the Gaussian.
-/
theorem parisiStep_lipschitz {m v L : ℝ} {A : ℝ → ℝ}
    (hL : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x x' : ℝ) :
    |parisiStep m v A x - parisiStep m v A x'| ≤ L * |x - x'| := by
  classical
  set c : ℝ := x' - x with hc
  set A' : ℝ → ℝ := fun y => A (y + c) with hA'def
  -- `A'` inherits measurability and linear growth
  have hmeas' : Measurable A' := hmeas.comp (measurable_id.add_const c)
  have hgrow' : HasLinearGrowth A' := by
    obtain ⟨C, D, hC, hD, hb⟩ := hA
    refine ⟨C + D * |c|, D, by positivity, hD, fun y => ?_⟩
    refine (hb (y + c)).trans ?_
    have htri : |y + c| ≤ |y| + |c| := abs_add_le _ _
    nlinarith [abs_nonneg y, abs_nonneg c]
  -- translating the argument turns the point change into a function change
  have hshift : ∀ z : ℝ, A' (x + Real.sqrt v * z) = A (x' + Real.sqrt v * z) := by
    intro z
    show A (x + Real.sqrt v * z + c) = A (x' + Real.sqrt v * z)
    congr 1
    rw [hc]; ring
  have heq : parisiStep m v A' x = parisiStep m v A x' := by
    simp only [parisiStep]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
      exact integral_congr_ae (Filter.Eventually.of_forall hshift)
    · rw [if_neg hm, if_neg hm]
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.exp (m * A' (x + Real.sqrt v * z))
          = Real.exp (m * A (x' + Real.sqrt v * z))
      rw [hshift z]
  have hunif : ∀ y, |A y - A' y| ≤ L * |x - x'| := by
    intro y
    have h := hL y (y + c)
    have hrw : |y - (y + c)| = |x - x'| := by
      rw [show y - (y + c) = -c by ring, abs_neg, hc, abs_sub_comm]
    rwa [hrw] at h
  rw [← heq]
  exact parisiStep_dist_le hunif
    (integrable_of_hasLinearGrowth hA hmeas x v)
    (integrable_of_hasLinearGrowth hgrow' hmeas' x v)
    (integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v)
    (integrable_exp_mul_of_hasLinearGrowth hgrow' hmeas' m x v)

/--
Pure arithmetic behind the variance-perturbation estimate: if `X` is squeezed between
`mm * c` and `mm * c + B mm² / 2`, then `1/mm * X` is within `|mm| B / 2` of `c`.

Isolated from the measure theory so that the two can fail independently.
-/
theorem abs_inv_mul_sub_le_of_bounds {X c mm B : ℝ} (hmm : mm ≠ 0) (hB : 0 ≤ B)
    (h1 : mm * c ≤ X) (h2 : X ≤ mm * c + B * mm ^ 2 / 2) :
    |1 / mm * X - c| ≤ |mm| * B / 2 := by
  have hmpos : 0 < |mm| := abs_pos.2 hmm
  have hid : mm * (1 / mm * X - c) = X - mm * c := by field_simp
  have habs : |mm| * |1 / mm * X - c| = |X - mm * c| := by
    rw [← abs_mul, hid]
  have hb : |X - mm * c| ≤ B * mm ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hsq : |mm| * |mm| = mm ^ 2 := by
    rw [abs_mul_abs_self]; ring
  refine le_of_mul_le_mul_left ?_ hmpos
  calc |mm| * |1 / mm * X - c| = |X - mm * c| := habs
    _ ≤ B * mm ^ 2 / 2 := hb
    _ = |mm| * (|mm| * B / 2) := by
        rw [show |mm| * (|mm| * B / 2) = |mm| * |mm| * B / 2 by ring, hsq]
        ring

/--
**The variance-perturbation estimate.**

For `A` `L`-Lipschitz, `w > 0` and `m ≠ 0`,

  `|T_{m,w} A (x) - A x| ≤ L √w 𝔼|Z| + |m| L² w / 2`.

This is the analytic core of the `q`-perturbation half of Target 2b: via the semigroup law
`Parisi.T_add`, changing a scheme parameter `q_p` factors as an extra smoothing step of small
variance `w`, and this bounds its effect.

Both bounds on `(1/m) log 𝔼[exp (m g)]`, `g z = A (x + √w z) - A x`, are used:

* **above** by the Herbst sub-Gaussian bound (`gaussianReal_mgf_le_of_lipschitz`);
* **below** by Jensen (`integral_log_le_log_integral`, proved for Target 1a and generalised
  to an arbitrary probability measure for exactly this use).

The estimate stays bounded as `m → 0`, which the naive `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)` would
not; that is what keeps Target 2b's constant uniform in `k`.
-/
theorem abs_parisiStep_sub_self_le {A : ℝ → ℝ} {L m w : ℝ}
    (hL : 0 < L) (hw : 0 < w) (hm : m ≠ 0)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    |parisiStep m w A x - A x|
      ≤ L * Real.sqrt w * (∫ z, |z| ∂(gaussianReal 0 1)) + |m| * (L ^ 2 * w) / 2 := by
  classical
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hLw : 0 < L * Real.sqrt w := mul_pos hL hsw
  have hfmeas : Measurable (fun z : ℝ => A (x + Real.sqrt w * z)) :=
    hmeas.comp (by fun_prop)
  have hfint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z)) (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth hA hmeas x w
  have hexpint : Integrable
      (fun z : ℝ => Real.exp (m * A (x + Real.sqrt w * z))) (gaussianReal 0 1) :=
    integrable_exp_mul_of_hasLinearGrowth hA hmeas m x w
  have hIpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1) :=
    integral_exp_pos hexpint
  -- `z ↦ A (x + √w z)` is `L √w`-Lipschitz
  have hfLip : LipschitzWith (L * Real.sqrt w).toNNReal
      (fun z : ℝ => A (x + Real.sqrt w * z)) := by
    refine LipschitzWith.of_dist_le_mul (fun z z' => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hLw.le]
    have h := hLip (x + Real.sqrt w * z) (x + Real.sqrt w * z')
    have hrw : |x + Real.sqrt w * z - (x + Real.sqrt w * z')| = Real.sqrt w * |z - z'| := by
      rw [show x + Real.sqrt w * z - (x + Real.sqrt w * z') = Real.sqrt w * (z - z') by ring,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg w)]
    rw [hrw] at h
    calc |A (x + Real.sqrt w * z) - A (x + Real.sqrt w * z')|
        ≤ L * (Real.sqrt w * |z - z'|) := h
      _ = L * Real.sqrt w * |z - z'| := by ring
  -- Herbst, rewritten as a bound on the plain exponential integral
  have hherbst := gaussianReal_mgf_le_of_lipschitz
    (fun z : ℝ => A (x + Real.sqrt w * z)) (L * Real.sqrt w) hLw hfLip hfmeas m
  have hmgf_eq : mgf (fun z : ℝ => A (x + Real.sqrt w * z)
        - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) (gaussianReal 0 1) m
      = Real.exp (-(m * ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
        * ∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1) := by
    simp only [mgf]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show Real.exp (m * (A (x + Real.sqrt w * z)
        - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
      = Real.exp (-(m * ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
        * Real.exp (m * A (x + Real.sqrt w * z))
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper : Real.log (∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1))
      ≤ m * (∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1))
        + (L ^ 2 * w) * m ^ 2 / 2 := by
    rw [hmgf_eq] at hherbst
    have h := Real.log_le_log (by positivity) hherbst
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hIpos), Real.log_exp, Real.log_exp] at h
    have hsq : (L * Real.sqrt w) ^ 2 = L ^ 2 * w := by
      rw [mul_pow, Real.sq_sqrt hw.le]
    rw [hsq] at h
    linarith
  -- Jensen
  have hlower : m * (∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1))
      ≤ Real.log (∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1)) := by
    have hlogint : Integrable
        (fun z : ℝ => Real.log (Real.exp (m * A (x + Real.sqrt w * z))))
        (gaussianReal 0 1) := by
      simpa [Real.log_exp] using hfint.const_mul m
    have h := integral_log_le_log_integral (μ := gaussianReal 0 1)
      (W := fun z : ℝ => Real.exp (m * A (x + Real.sqrt w * z)))
      (fun z => Real.exp_pos _) hexpint hlogint
    simpa [Real.log_exp, integral_const_mul] using h
  -- combine the two bounds, then add the mean term
  have hTc : |parisiStep m w A x
      - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)| ≤ |m| * (L ^ 2 * w) / 2 := by
    rw [parisiStep, if_neg hm]
    exact abs_inv_mul_sub_le_of_bounds hm (by positivity) hlower hupper
  have hcA : |(∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) - A x|
      ≤ L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) :=
    abs_integral_shift_sub_le hL.le hLip hA hmeas x w
  calc |parisiStep m w A x - A x|
      ≤ |parisiStep m w A x - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)|
          + |(∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) - A x| :=
        abs_sub_le _ _ _
    _ ≤ |m| * (L ^ 2 * w) / 2 + L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := by
        linarith [hTc, hcA]
    _ = L * Real.sqrt w * (∫ z, |z| ∂(gaussianReal 0 1)) + |m| * (L ^ 2 * w) / 2 := by ring

/--
**The smoothing step preserves the second-order invariant.**

If `A` satisfies `0 ≤ A'' ≤ 1 - (A')²` and `0 < m ≤ 1`, then so does `parisiStep m v A`,
with derivatives `stepD1` and `stepD2`.

The hypothesis `m ≤ 1` is essential and is exactly what an RSB scheme provides
(`RSBScheme.m_le_one`): it is what gives the `-(1-m)·Var_tilt(A')` term in
`(T A)'' = ⟨A''⟩ + m Var_tilt(A')` the right sign.  For `m > 1` the invariant is *not*
preserved and the second derivative can grow with the level, which would destroy the
uniformity in `k` that Target 2b needs.
-/
theorem hasParisiC2_parisiStep {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm : m ≠ 0) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hA : HasParisiC2 A A' A'')
    (hgrow : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') :
    HasParisiC2 (parisiStep m v A) (stepD1 A A' m v) (stepD2 A A' A'' m v) := by
  have hA'bd : ∀ y, |A' y| ≤ 1 := fun y => hA.abs_first_le_one y
  have hA''bd : ∀ y, |A'' y| ≤ 1 := fun y => hA.abs_second_le_one y
  obtain ⟨hd1, hd2, hnn, hle⟩ := hA
  have hstep : parisiStep m v A
      = fun t : ℝ => (1 / m)
        * Real.log (∫ z, Real.exp (m * A (t + Real.sqrt v * z))
            ∂(gaussianReal 0 1)) := by
    funext t
    rw [parisiStep, if_neg hm]
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hstep]
    exact hasDerivAt_stepD1 hm hd1 hA'bd hgrow hmeas hmeas' x
  · exact hasDerivAt_stepD2 hm hd1 hd2 hA'bd hA''bd hgrow hmeas hmeas' hmeas'' x
  · exact smoothing_second_deriv_nonneg hm0 hA'bd hA''bd hnn hgrow hmeas hmeas' hmeas'' x
  · exact smoothing_second_deriv_le hm0 hm1 hA'bd hA''bd hle hgrow hmeas hmeas' hmeas'' x

/-- Backward Parisi recursion for the SK model (`ξ(x) = x²/2`, so `ξ'(x) = x`).

`parisiF s β j` is the function `F_{k+2-j}` of Talagrand's recursion:

  `F_{k+2}(x) = log cosh x`,
  `F_p = T_{m_p, β²(q_{p+1} - q_p)} F_{p+1}`   for `p = k+1, k, …, 1`,
  `F_0 = T_{0, β² q₁} F_1 = E F_1(· + β√q₁ z)`.

So `parisiF s β (k+2)` is `F_0` (there are `k+2` smoothing steps: `p = k+1, …, 1`, then `p = 0`). -/
noncomputable def parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun x => Real.log (Real.cosh x)
  | j + 1 =>
      parisiStep (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
        (parisiF s β j)

/--
**Every level of the Parisi recursion is measurable, of linear growth, and 1-Lipschitz.**

These are exactly the three side conditions that `parisiStep_dist_le`,
`hasLinearGrowth_parisiStep`, `parisiStep_lipschitz` and `abs_parisiStep_sub_self_le` all
require of the function being smoothed, so proving them once by simultaneous induction
discharges them at every level of `parisiF` — which is what Target 2b needs in order to sum
the per-level perturbation estimates over `p = 0, …, k+1`.

The three properties have to be carried *together*: the Lipschitz step needs measurability
and linear growth as hypotheses, and measurability at the next level is obtained *from* the
Lipschitz bound (Lipschitz ⟹ continuous ⟹ measurable), so neither can be proved on its own.

Base case: `log cosh` is measurable, satisfies `|log cosh y| ≤ |y|`, and is 1-Lipschitz.
Note the Lipschitz constant is `1` at every level — the smoothing step never increases it.
-/
theorem parisiF_props {k : ℕ} (s : RSBScheme k) (β : ℝ) : ∀ j : ℕ,
    Measurable (parisiF s β j)
      ∧ HasLinearGrowth (parisiF s β j)
      ∧ ∀ x x' : ℝ, |parisiF s β j x - parisiF s β j x'| ≤ |x - x'| := by
  intro j
  induction j with
  | zero =>
      refine ⟨?_, hasLinearGrowth_log_cosh, fun x x' => log_cosh_dist_le x x'⟩
      exact (Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))).measurable
  | succ j ih =>
      obtain ⟨hmeas, hgrow, hlip⟩ := ih
      have hlip' : ∀ y y' : ℝ,
          |parisiF s β j y - parisiF s β j y'| ≤ 1 * |y - y'| := by
        intro y y'
        simpa using hlip y y'
      have hstep : ∀ x x' : ℝ,
          |parisiF s β (j + 1) x - parisiF s β (j + 1) x'| ≤ |x - x'| := by
        intro x x'
        have h := parisiStep_lipschitz (m := s.m (k + 1 - j))
          (v := β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) (L := 1)
          hlip' hgrow hmeas x x'
        rw [one_mul] at h
        -- `parisiF s β (j+1)` is definitionally this `parisiStep`; `exact` uses that,
        -- whereas `simpa` normalises the two sides into different syntactic forms.
        exact h
      have hgrow' : HasLinearGrowth (parisiF s β (j + 1)) :=
        hasLinearGrowth_parisiStep hgrow hmeas _ _
      have hmeas' : Measurable (parisiF s β (j + 1)) := by
        have hL : LipschitzWith 1 (parisiF s β (j + 1)) := by
          refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
          rw [Real.dist_eq, Real.dist_eq]
          simpa using hstep a b
        exact hL.continuous.measurable
      exact ⟨hmeas', hgrow', hstep⟩

/-- Every level of the Parisi recursion is measurable. -/
theorem parisiF_measurable {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Measurable (parisiF s β j) := (parisiF_props s β j).1

/-- Every level of the Parisi recursion has linear growth. -/
theorem parisiF_hasLinearGrowth {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    HasLinearGrowth (parisiF s β j) := (parisiF_props s β j).2.1

/-- Every level of the Parisi recursion is 1-Lipschitz. -/
theorem parisiF_lipschitz {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x x' : ℝ) :
    |parisiF s β j x - parisiF s β j x'| ≤ |x - x'| := (parisiF_props s β j).2.2 x x'

/-- The `k`-step Parisi functional for the SK model with external field `h`:

  `𝒫_k(m,q) = log 2 + F_0(h) - (β²/4) ∑_{p=1}^{k+1} m_p (q_{p+1}² - q_p²)`.

(The prefactor `β²/4` is `β²/2 · (θ(q_{p+1}) - θ(q_p))` with `θ(q) = q ξ'(q) - ξ(q) = q²/2`.) -/
noncomputable def parisiFunctional {k : ℕ} (s : RSBScheme k) (β h : ℝ) : ℝ :=
  Real.log 2 + parisiF s β (k + 2) h
    - (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)

/-! ### Well-definedness of the Parisi value

`parisiValue` (below) is an `sInf`.  In Mathlib, `sInf` of a set that is **not bounded
below** is the junk value `sInf ∅ = 0` (`csInf_of_not_bddBelow`).  So without a lower
bound, Target 4 would be asserting that the free entropy converges to `0` — false.

This section supplies the missing bound: `log 2 - β²/4 ≤ 𝒫_k(m,q)` for *every* scheme,
uniformly in `k`.  Two ingredients:

* `parisiF_nonneg` — the Gaussian smoothing operator preserves non-negativity (note the
  junk values work in our favour: a non-integrable integrand gives `∫ = 0`, and
  `log 0 = 0`), and the base case `log cosh ≥ 0`;
* `sum_correction_le_one` — `∑_p m_p (q²_{p+1} - q²_p) ≤ 1` by telescoping, using
  `m_p ≤ 1` and `q` non-decreasing.
-/

namespace RSBScheme

variable {k : ℕ} (s : RSBScheme k)

/-- `s.m` is non-decreasing on `[0, k+1]`. -/
lemma m_mono' : ∀ b, b ≤ k + 1 → ∀ a, a ≤ b → s.m a ≤ s.m b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      exact le_of_eq (congrArg s.m (Nat.le_zero.mp ha))
  | succ b ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have h1 : s.m a ≤ s.m b := ih (by omega) a (Nat.lt_succ_iff.mp h)
        have h2 : s.m b ≤ s.m (b + 1) := s.m_mono b (by omega)
        linarith
      · exact le_of_eq (congrArg s.m (le_antisymm ha h))

/-- `s.q` is non-decreasing on `[0, k+2]`. -/
lemma q_mono' : ∀ b, b ≤ k + 2 → ∀ a, a ≤ b → s.q a ≤ s.q b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      exact le_of_eq (congrArg s.q (Nat.le_zero.mp ha))
  | succ b ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have h1 : s.q a ≤ s.q b := ih (by omega) a (Nat.lt_succ_iff.mp h)
        have h2 : s.q b ≤ s.q (b + 1) := s.q_mono b (by omega)
        linarith
      · exact le_of_eq (congrArg s.q (le_antisymm ha h))

lemma m_le_one {p : ℕ} (hp : p ≤ k + 1) : s.m p ≤ 1 := by
  have h := s.m_mono' (k + 1) le_rfl p hp
  rwa [s.m_top] at h

lemma q_nonneg {p : ℕ} (hp : p ≤ k + 2) : 0 ≤ s.q p := by
  have h := s.q_mono' p hp 0 (Nat.zero_le p)
  rwa [s.q_zero] at h

end RSBScheme

/-- The Gaussian smoothing step preserves non-negativity. -/
lemma parisiStep_nonneg {m v : ℝ} {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) (x : ℝ) :
    0 ≤ parisiStep m v A x := by
  rw [parisiStep]
  split_ifs with hm
  · exact integral_nonneg (fun z => hA _)
  · set I : ℝ := ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) with hIdef
    have hI0 : 0 ≤ I := integral_nonneg (fun z => (Real.exp_pos _).le)
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · have hIle : I ≤ 1 := by
        by_cases hint : Integrable
            (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1)
        · have hmono : I ≤ ∫ _z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
            refine integral_mono hint (integrable_const 1) (fun z => ?_)
            have hle : m * A (x + Real.sqrt v * z) ≤ 0 := by
              nlinarith [hA (x + Real.sqrt v * z)]
            calc Real.exp (m * A (x + Real.sqrt v * z)) ≤ Real.exp 0 :=
                  Real.exp_le_exp.2 hle
              _ = 1 := Real.exp_zero
          simpa using hmono
        · rw [hIdef, integral_undef hint]; norm_num
      have hlog : Real.log I ≤ 0 := Real.log_nonpos hI0 hIle
      have hminv : 1 / m < 0 := div_neg_of_pos_of_neg one_pos hneg
      nlinarith
    · have hcase : (1 : ℝ) ≤ I ∨ I = 0 := by
        by_cases hint : Integrable
            (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1)
        · left
          have hmono : (∫ _z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1)) ≤ I := by
            refine integral_mono (integrable_const 1) hint (fun z => ?_)
            have hle : (0 : ℝ) ≤ m * A (x + Real.sqrt v * z) :=
              mul_nonneg hpos.le (hA _)
            calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
              _ ≤ Real.exp (m * A (x + Real.sqrt v * z)) := Real.exp_le_exp.2 hle
          simpa using hmono
        · right; rw [hIdef, integral_undef hint]
      have hminv : 0 < 1 / m := div_pos one_pos hpos
      rcases hcase with h1 | h1
      · exact mul_nonneg hminv.le (Real.log_nonneg h1)
      · rw [h1, Real.log_zero, mul_zero]

/-- Every level of the Parisi recursion is non-negative. -/
lemma parisiF_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ∀ (j : ℕ) (x : ℝ), 0 ≤ parisiF s β j x := by
  intro j
  induction j with
  | zero => intro x; exact log_cosh_nonneg x
  | succ j ih => intro x; exact parisiStep_nonneg (fun y => ih y) x

/-- The correction sum telescopes to at most `1`. -/
lemma sum_correction_le_one {k : ℕ} (s : RSBScheme k) :
    (∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) ≤ 1 := by
  have hterm : ∀ p ∈ Finset.range (k + 1),
      s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)
        ≤ s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2 := by
    intro p hp
    have hpk : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    have hm1 : s.m (p + 1) ≤ 1 := s.m_le_one (by omega)
    have hq1 : 0 ≤ s.q (p + 1) := s.q_nonneg (by omega)
    have hqle : s.q (p + 1) ≤ s.q (p + 2) := s.q_mono (p + 1) (by omega)
    have hsq : s.q (p + 1) ^ 2 ≤ s.q (p + 2) ^ 2 := by nlinarith
    nlinarith
  calc
    (∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2))
        ≤ ∑ p ∈ Finset.range (k + 1), (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2) :=
          Finset.sum_le_sum hterm
    _ = s.q (k + 2) ^ 2 - s.q 1 ^ 2 := by
          simpa using Finset.sum_range_sub (fun i => s.q (i + 1) ^ 2) (k + 1)
    _ ≤ 1 := by
          rw [s.q_top]
          nlinarith [sq_nonneg (s.q 1)]

/-- **Uniform lower bound on the finite-step Parisi functional.** -/
theorem parisiFunctional_ge {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    Real.log 2 - β ^ 2 / 4 ≤ parisiFunctional s β h := by
  have hF : 0 ≤ parisiF s β (k + 2) h := parisiF_nonneg s β (k + 2) h
  have hS := sum_correction_le_one s
  have hb : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hS hb
  rw [parisiFunctional]
  linarith

/-- The replica-symmetric scheme with overlap `q`: `k = 0`, `m = (0, 1)`, `q = (0, q, 1)`. -/
noncomputable def rsScheme (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : RSBScheme 0 where
  m := fun p => if p = 0 then 0 else 1
  q := fun p => if p = 0 then 0 else if p = 1 then q else 1
  m_zero := by simp
  m_top := by simp
  m_mono := by
    intro p hp
    have : p = 0 := Nat.le_zero.mp hp
    subst this
    norm_num
  q_zero := by simp
  q_top := by simp
  q_mono := by
    intro p hp
    have hp' : p ≤ 1 := by simpa using hp
    interval_cases p <;> simp [hq0, hq1]

/-- **Target 2a (sanity check: RS case).**  The `0`-step functional is the classical
replica-symmetric formula `log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`.

This lemma guards against off-by-one or normalisation mistakes in the definitions above:
if it is false, the definitions are wrong, not the theorem.

Hand computation to check against (`k = 0`, `m = (0,1)`, `q = (0,q,1)`):
`F_1 = T_{1, β²(1-q)} (log cosh)`, and `∫ cosh(x + σ z) dγ(z) = cosh x · e^{σ²/2}`, so
`F_1(x) = log cosh x + β²(1-q)/2`; then `F_0(h) = E log cosh(h + β√q z) + β²(1-q)/2` and
`𝒫_0 = log 2 + F_0(h) - (β²/4)(1 - q²) = log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`. -/
theorem parisiFunctional_rsScheme (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    parisiFunctional (rsScheme q hq0 hq1) β h
      = Real.log 2
        + (∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1))
        + (β ^ 2 / 4) * (1 - q) ^ 2 := by
  classical
  set s := rsScheme q hq0 hq1 with hs
  have hm0 : s.m 0 = 0 := by simp [hs, rsScheme]
  have hm1 : s.m 1 = 1 := by simp [hs, rsScheme]
  have hqq0 : s.q 0 = 0 := by simp [hs, rsScheme]
  have hqq1 : s.q 1 = q := by simp [hs, rsScheme]
  have hqq2 : s.q 2 = 1 := by simp [hs, rsScheme]
  have hv1 : (0:ℝ) ≤ β ^ 2 * (1 - q) := mul_nonneg (sq_nonneg β) (by linarith)
  have hlogcosh_cont : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))
  -- `F₁ = T_{1, β²(1-q)} (log cosh) = log cosh + β²(1-q)/2`
  have hF1 : parisiF s β 1
      = fun x => Real.log (Real.cosh x) + β ^ 2 * (1 - q) / 2 := by
    funext x
    show parisiStep (s.m 1) (β ^ 2 * (s.q 2 - s.q 1)) (parisiF s β 0) x = _
    rw [hm1, hqq2, hqq1, parisiStep, if_neg (one_ne_zero)]
    have hpt : ∀ z : ℝ,
        Real.exp (1 * parisiF s β 0 (x + Real.sqrt (β ^ 2 * (1 - q)) * z))
          = Real.cosh (x + Real.sqrt (β ^ 2 * (1 - q)) * z) := by
      intro z
      show Real.exp (1 * Real.log (Real.cosh _)) = _
      rw [one_mul, Real.exp_log (Real.cosh_pos _)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_cosh_add_mul_stdGaussian x (Real.sqrt (β ^ 2 * (1 - q))),
        Real.sq_sqrt hv1,
        Real.log_mul (ne_of_gt (Real.cosh_pos x)) (Real.exp_ne_zero _),
        Real.log_exp]
    ring
  -- `F₀(h) = ∫ log cosh (h + |β|√q z) dγ + β²(1-q)/2`
  have hsq : Real.sqrt (β ^ 2 * q) = |β| * Real.sqrt q := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have hF0 : parisiF s β 2 h
      = (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
          + β ^ 2 * (1 - q) / 2 := by
    show parisiStep (s.m 0) (β ^ 2 * (s.q 1 - s.q 0)) (parisiF s β 1) h = _
    rw [hm0, hqq1, hqq0, sub_zero, parisiStep, if_pos rfl, hF1, hsq]
    rw [integral_add (integrable_log_cosh_stdGaussian (|β| * Real.sqrt q) h)
        (integrable_const _)]
    simp
  -- the correction sum is `1 * (1 - q²)`
  have hsum : (∑ p ∈ Finset.range (0 + 1),
      s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) = 1 * (1 - q ^ 2) := by
    simp [hm1, hqq1, hqq2]
  -- `|β|√q` and `β√q` agree under the symmetric Gaussian
  have hrefl :
      (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
        = ∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
    rcases le_or_gt 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.log (Real.cosh (h + β * Real.sqrt q * z))
          = Real.log (Real.cosh (β * Real.sqrt q * z + h))
      rw [add_comm]
    · rw [abs_of_neg hβ]
      have hre := integral_reflect_stdGaussian
        (f := fun y : ℝ => Real.log (Real.cosh y)) hlogcosh_cont (β * Real.sqrt q) h
      rw [show -β * Real.sqrt q = -(β * Real.sqrt q) by ring, ← hre]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.log (Real.cosh (h + β * Real.sqrt q * z))
          = Real.log (Real.cosh (β * Real.sqrt q * z + h))
      rw [add_comm]
  rw [parisiFunctional, hF0, hsum, hrefl]
  ring

/-! ### The `m = 0` boundary of the smoothing operator

`parisiStep` branches at `m = 0`, and Talagrand's admissible sequences (1.6) *allow*
`m_0 = 0` — indeed he notes that equality in (1.6)–(1.7) is exactly what makes the
compactness argument behind (2.17) work.  So the two branches must be reconciled
quantitatively before anything can be said about `𝒫_k` as a function of its parameters.

`parisiStep_zero_sandwich` does that: the `m`-branch sits above the `0`-branch (Jensen) and
overshoots it by at most `m·v/2` (Herbst).  Two features matter downstream:

* the estimate is **uniform in `x`** — the constant involves only the Lipschitz constant of
  `A` and the variance `v`, never `sup |A|` (which is infinite for `log cosh`); and
* it is **linear in `m`**, not `√m`, so it survives summation over the `k+2` levels of the
  recursion with a constant independent of `k`.

Both are consequences of using the sub-Gaussian form of the Herbst bound rather than the
naive `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)`, whose `(log 2)/m` term blows up as `m → 0`.
-/

/--
**The `m`-branch and the `0`-branch of `parisiStep` differ by at most `m·v/2`.**

For `A` 1-Lipschitz of linear growth, `0 < m` and `0 ≤ v`:

  `parisiStep 0 v A x ≤ parisiStep m v A x ≤ parisiStep 0 v A x + m·v/2`,

uniformly in `x`.  The lower bound is Jensen's inequality, the upper bound is the Herbst
sub-Gaussian estimate for the `√v`-Lipschitz function `z ↦ A (x + √v z)`.
-/
theorem parisiStep_zero_sandwich {A : ℝ → ℝ} {m v : ℝ}
    (hm : 0 < m) (hv : 0 ≤ v)
    (hLip : ∀ y y', |A y - A y'| ≤ |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    parisiStep 0 v A x ≤ parisiStep m v A x
      ∧ parisiStep m v A x ≤ parisiStep 0 v A x + m * v / 2 := by
  classical
  -- the smoothed function, and the two branches written out
  set f : ℝ → ℝ := fun z => A (x + Real.sqrt v * z) with hf
  have hfmeas : Measurable f := hmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add x)
  have hfint : Integrable f (gaussianReal 0 1) := integrable_of_hasLinearGrowth hA hmeas x v
  have hfexp : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1) :=
    integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hzero : parisiStep 0 v A x = ∫ z, f z ∂(gaussianReal 0 1) := by
    rw [parisiStep, if_pos rfl]
  have hpos : parisiStep m v A x
      = (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1)) := by
    rw [parisiStep, if_neg hm.ne']
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · -- degenerate variance: both branches equal `A x`
    have hfconst : ∀ z : ℝ, f z = A x := by
      intro z
      rw [hf]
      simp [← hv0]
    have h0 : parisiStep 0 v A x = A x := by
      rw [hzero]
      rw [show (∫ z, f z ∂(gaussianReal 0 1)) = ∫ _z : ℝ, A x ∂(gaussianReal 0 1) from
        integral_congr_ae (Filter.Eventually.of_forall hfconst)]
      simp
    have hm' : parisiStep m v A x = A x := by
      rw [hpos]
      rw [show (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
            = ∫ _z : ℝ, Real.exp (m * A x) ∂(gaussianReal 0 1) from
        integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          show Real.exp (m * f z) = Real.exp (m * A x)
          rw [hfconst z]))]
      rw [integral_const, probReal_univ, one_smul, Real.log_exp]
      field_simp
    rw [h0, hm', ← hv0]
    constructor
    · exact le_rfl
    · simp
  · -- non-degenerate: Jensen below, Herbst above
    have hsq : Real.sqrt v > 0 := Real.sqrt_pos.2 hvpos
    have hLipf : LipschitzWith (Real.sqrt v).toNNReal f := by
      refine LipschitzWith.of_dist_le_mul (fun z z' => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg v)]
      have h := hLip (x + Real.sqrt v * z) (x + Real.sqrt v * z')
      rwa [show (x + Real.sqrt v * z) - (x + Real.sqrt v * z')
            = Real.sqrt v * (z - z') by ring,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)] at h
    have hlow := SpinGlass.integral_le_inv_mul_log_integral_exp (f := f) hm hfint hfexp
    have hhigh := SpinGlass.inv_mul_log_integral_exp_le (f := f) (L := Real.sqrt v)
      hm hsq hLipf hfmeas hfexp
    rw [Real.sq_sqrt hv] at hhigh
    refine ⟨?_, ?_⟩
    · rw [hzero, hpos]; exact hlow
    · rw [hzero, hpos]
      calc (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
          ≤ (∫ z, f z ∂(gaussianReal 0 1)) + m * v / 2 := hhigh

/-! ### Target 2b, split

Reading Talagrand's Annals paper directly (see `docs/ROADMAP.md`) shows that the parameter
regularity his proof consumes is **not** a Lipschitz estimate.  Immediately after (1.13) he
declines that viewpoint:

> "Guerra proves that this definition can be extended by a continuity argument to any
> probability measure µ on [0,1] … *We do not adopt this point of view since an essential
> ingredient of our approach is that we need only consider discrete objects rather than
> continuous ones.*"

What he uses instead is (2.17) — that the infimum defining `𝒫` is *attained* — obtained "by
a compactness argument", and he remarks that allowing equality in (1.6)–(1.7) is precisely
what makes that argument available.  Section 5 then works with partial derivatives of the
functional **at** that minimiser.

So the target splits:

* `exists_minimizer_parisiFunctional` (**2b-i**) — Talagrand's (2.17).  On the critical path
  to Target 4.  Needs only continuity of `𝒫_k` in `(m,q)` for *fixed* `k`: no modulus, no
  uniformity in `k`.  The one delicate point is continuity where some `m_p = 0`, since
  `parisiStep` branches there; `parisiStep_zero_sandwich` above supplies exactly that,
  with a bound uniform in `x`.
* `parisiFunctional_lipschitz` (**2b-ii**) — Guerra's uniform-in-`k` Lipschitz bound, needed
  to pass from discrete schemes to general Parisi measures.  Kept, but **off** the critical
  path for the Talagrand route.
-/

/--
**Target 2b-i (Talagrand 2006, (2.17)).**  For each fixed number of levels `k`, the
infimum of `𝒫_k(m,q)` over admissible schemes is **attained**.

This is the form of parameter regularity that Talagrand's proof actually consumes: (2.16)
and (2.17) are the standing hypotheses of Theorem 2.2, and §5 differentiates the functional
at the minimising scheme.  He obtains it "by a compactness argument", noting that it is to
permit that argument that equality is allowed in (1.6) and (1.7) — i.e. the admissible set

  `0 = m_0 ≤ m_1 ≤ … ≤ m_k ≤ m_{k+1} = 1`,  `0 = q_0 ≤ … ≤ q_{k+2} = 1`

is *closed*, hence compact, exactly because the inequalities are not strict.

Proof plan: the admissible schemes form a compact subset of `ℝ^{k+2} × ℝ^{k+3}`
(`isCompact_Icc`, `IsCompact.prod`, intersected with the closed monotonicity constraints);
`𝒫_k` is continuous on it — level by level through `parisiF`, using `parisiStep_dist_le` to
propagate a sup-norm perturbation and dominated convergence for the parameter dependence of
a single step, with `parisiStep_zero_sandwich` covering the `m_p = 0` branch point — and
`IsCompact.exists_isMinOn` finishes.
-/
theorem exists_minimizer_parisiFunctional (k : ℕ) (β h : ℝ) :
    ∃ s : RSBScheme k, ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h := by
  sorry

/-- **Target 2b (Lipschitz continuity in the scheme).**  Guerra's estimate:

  `|𝒫_k(m,q) - 𝒫_k(m',q')| ≤ C(β,h) · ∑_p (|m_p - m'_p| + |q_p - q'_p|)`,

with a constant `C` depending only on `β` and `h` — **uniformly in `k`**.

*Quantifier order matters here, and the previous statement had it wrong.*  It read

  `∀ k, ∃ C, ∀ s s' : RSBScheme k, …`,

which permits `C` to depend on `k`.  That cannot serve the purpose stated for this target:
controlling `parisiValue = inf_k inf_{(m,q)} 𝒫_k` requires an estimate uniform in `k`,
otherwise nothing survives the infimum over all `k`.  So `∃ C` is now hoisted outside
`∀ k`.  (`0 ≤ C` is added for convenience downstream; it costs nothing, since any witness
can be replaced by its absolute value.)

This is what lets one pass from discrete to general Parisi measures, and — under the
Talagrand (2006) route fixed in `docs/ROADMAP.md` — it is **load-bearing** rather than
optional: the induction on the number of RSB levels needs regularity of `𝒫_k` in the
parameters.

The precise form of the right-hand side (the `ℓ¹` distance between the two schemes) should
still be confirmed against Talagrand when the Milestone 4 blueprint chapter is written; what
is *not* negotiable is the uniformity in `k`. -/
theorem parisiFunctional_lipschitz (β h : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (s s' : RSBScheme k),
      |parisiFunctional s β h - parisiFunctional s' β h|
        ≤ C * ∑ p ∈ Finset.range (k + 3), (|s.m p - s'.m p| + |s.q p - s'.q p|) := by
  sorry

/-! ## Milestone 3 — Guerra's replica-symmetry-breaking bound -/

/-- **Target 3 (Guerra 2003).**  For every `N`, every `(β, h)` and every finite-step scheme,
`(1/N) E log Z_N ≤ 𝒫_k(m,q)`.

Because the vendored covariance kernel is exactly `(Nβ²/2) R²` (no diagonal correction), the
bound holds with no `O(1/N)` error term.

Proof plan (blueprint, Chapter 3): interpolate between the SK Hamiltonian and a hierarchical
Gaussian field `∑ᵢ σᵢ ∑_p z_p^i √(β²(q_{p+1} - q_p))` organised along a `k+2`-level tree;
define `φ(t)` through iterated `(1/m_p) log E_p exp(m_p ·)`; compute `φ'(t)` via Gaussian
IBP; the remainder is a sum of terms `-(β²/4)(m_{p+1} - m_p) E⟨(R - q_p)²⟩ ≤ 0`. -/
theorem guerra_rsb_bound {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U ≤ parisiFunctional s β h := by
  sorry

/-- The Parisi value: infimum of the finite-step functionals over all `k` and all schemes. -/
noncomputable def parisiValue (β h : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}

/-! ### `parisiValue` is a genuine infimum

Consequences of `parisiFunctional_ge`: the defining set is non-empty and bounded below,
so `sInf` is *not* the junk value and `parisiValue` means what it says.  `parisiValue_le`
is the form Target 3' consumes.
-/

/-- The set of finite-step Parisi functionals is non-empty (take the RS scheme at `q = 0`). -/
theorem parisiSet_nonempty (β h : ℝ) :
    {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}.Nonempty :=
  ⟨parisiFunctional (rsScheme 0 le_rfl zero_le_one) β h,
    ⟨0, rsScheme 0 le_rfl zero_le_one, rfl⟩⟩

/-- **The set of finite-step Parisi functionals is bounded below**, uniformly in `k`.
Without this, `sInf` would collapse to the junk value `0`. -/
theorem bddBelow_parisiSet (β h : ℝ) :
    BddBelow {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h} := by
  refine ⟨Real.log 2 - β ^ 2 / 4, ?_⟩
  rintro x ⟨k, s, rfl⟩
  exact parisiFunctional_ge s β h

/-- `parisiValue` really is below every finite-step functional. -/
theorem parisiValue_le {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    parisiValue β h ≤ parisiFunctional s β h :=
  csInf_le (bddBelow_parisiSet β h) ⟨k, s, rfl⟩

/-- `parisiValue` is bounded below by `log 2 - β²/4` (in particular it is not the junk value). -/
theorem parisiValue_ge (β h : ℝ) : Real.log 2 - β ^ 2 / 4 ≤ parisiValue β h := by
  refine le_csInf (parisiSet_nonempty β h) ?_
  rintro x ⟨k, s, rfl⟩
  exact parisiFunctional_ge s β h

/-- **Target 3' (upper bound in the limit).**  Immediate from Target 3. -/
theorem limsup_free_entropy_le_parisiValue (β h : ℝ)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h + ε := by
  sorry

/-! ## Milestone 4 — the Parisi formula (Talagrand 2006) -/

/-- **Target 4 (the Parisi formula).**  `lim_N (1/N) E log Z_N = inf_k inf_{(m,q)} 𝒫_k(m,q)`.

The upper bound is Target 3.  The lower bound is Talagrand's coupled-replica argument
(Annals 2006), whose replica-symmetric ancestor is formalised in RSAT as
`SpinGlass.AT.twoReplica_GT_bound`.  This is the long-term goal of the project; the
statement is recorded so the finish line is unambiguous.

Note that no independence assumption across sizes is needed: `free_entropy` depends only on
the law of `sk N`. -/
theorem parisi_formula (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 (parisiValue β h)) := by
  sorry

end Targets
end SpinGlass
