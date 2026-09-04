/-
# The tilted chain rule for an `N`-site cascade level

New work for the ParisiFormula project (not vendored).

`Targets/CascadeDeriv.lean` proves the tilted (Gibbs) chain rule for the one-dimensional
smoothing step.  Talagrand's (3.2) needs it for the `N`-site step `parisiStepPi`, because
for `t > 0` the base `F_{k+1,t}` couples the sites through `√t H(σ)` and does not factorise.
This file is that port.  Growth is measured in `ℓ¹`, `∑ᵢ |yᵢ|`, which is what the spin sum
naturally produces (`|∑ᵢ σᵢ yᵢ| ≤ ∑ᵢ |yᵢ|`), and integrability against `piGauss n` comes from
`Integrable.fintype_prod` applied to `exp (c ∑ᵢ |zᵢ|) = ∏ᵢ exp (c |zᵢ|)`.
-/
import Targets.CascadeDeriv

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

variable {n : ℕ}

/-! ## 1. Integrability against `piGauss n` in `ℓ¹` -/

/-- `∑ᵢ |zᵢ|` as a function; the `ℓ¹` size of the cascade field. -/
noncomputable abbrev l1 (z : Fin n → ℝ) : ℝ := ∑ i, |z i|

theorem l1_nonneg (z : Fin n → ℝ) : 0 ≤ l1 z :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem measurable_l1 : Measurable (fun z : Fin n → ℝ => l1 z) :=
  Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).abs)

theorem measurable_shift (v : ℝ) (x : Fin n → ℝ) :
    Measurable (fun z : Fin n → ℝ => fun i => x i + Real.sqrt v * z i) :=
  measurable_pi_lambda _ (fun i => measurable_const.add (measurable_const.mul (measurable_pi_apply i)))

theorem integrable_exp_l1 (c : ℝ) :
    Integrable (fun z : Fin n → ℝ => Real.exp (c * l1 z)) (piGauss n) := by
  have hfun : (fun z : Fin n → ℝ => Real.exp (c * l1 z))
      = fun z => ∏ i, Real.exp (c * |z i|) := by
    funext z
    rw [l1, Finset.mul_sum, Real.exp_sum]
  rw [hfun]
  exact Integrable.fintype_prod (fun i => integrable_exp_abs_mul_stdGaussian c)

theorem integrable_l1 : Integrable (fun z : Fin n → ℝ => l1 z) (piGauss n) :=
  integrable_finsetSum _ (fun i _ => integrable_piGauss_eval i integrable_abs_stdGaussian)

/-- `(a + b S) e^{c S} ≤ (a + b) e^{(c+1) S}` for `S ≥ 0`, so the left side is integrable. -/
theorem integrable_poly_mul_exp_l1 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    Integrable (fun z : Fin n → ℝ => (a + b * l1 z) * Real.exp (c * l1 z)) (piGauss n) := by
  refine Integrable.mono ((integrable_exp_l1 (c + 1)).const_mul (a + b)) ?_ ?_
  · exact ((measurable_const.add (measurable_l1.const_mul b)).mul
      (Real.continuous_exp.measurable.comp (measurable_l1.const_mul c))).aestronglyMeasurable
  · filter_upwards with z
    have hS := l1_nonneg z
    have hSe : l1 z ≤ Real.exp (l1 z) := by
      have := Real.add_one_le_exp (l1 z); linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a + b * l1 z) * Real.exp (c * l1 z)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a + b) * Real.exp ((c + 1) * l1 z))]
    have h1 : Real.exp (c * l1 z) ≤ Real.exp ((c + 1) * l1 z) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : l1 z * Real.exp (c * l1 z) ≤ Real.exp ((c + 1) * l1 z) := by
      calc l1 z * Real.exp (c * l1 z) ≤ Real.exp (l1 z) * Real.exp (c * l1 z) :=
            mul_le_mul_of_nonneg_right hSe (Real.exp_pos _).le
        _ = Real.exp ((c + 1) * l1 z) := by rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (c * l1 z)]

/-- The shifted argument in `ℓ¹`. -/
theorem l1_shift_le (v : ℝ) (x z : Fin n → ℝ) :
    l1 (fun i => x i + Real.sqrt v * z i) ≤ l1 x + Real.sqrt v * l1 z := by
  simp only [l1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]

/-! ## 2. The tilted weight of an `N`-site level -/

noncomputable def tiltWeightPi (n : ℕ) (m v : ℝ) (A : (Fin n → ℝ) → ℝ) (x z : Fin n → ℝ) : ℝ :=
  if m = 0 then 1
  else Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) /
        ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)

section ChainRule

variable {A A' : ℝ → (Fin n → ℝ) → ℝ} {m v C D C' D' : ℝ}

private theorem shift_bound_pi (hD : 0 ≤ D) (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (x : Fin n → ℝ) (v : ℝ) (u : ℝ) (z : Fin n → ℝ) :
    |A u (fun i => x i + Real.sqrt v * z i)| ≤ (C + D * l1 x) + (D * Real.sqrt v) * l1 z := by
  refine (hb u _).trans ?_
  have := l1_shift_le v x z
  nlinarith [l1_nonneg z, Real.sqrt_nonneg v]

/-- Integrability of `exp (m A_u(x + √v z))` from an `ℓ¹` growth bound. -/
theorem integrable_exp_shift_pi (hD : 0 ≤ D) (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (hmeas : ∀ u, Measurable (A u)) (x : Fin n → ℝ) (u : ℝ) :
    Integrable (fun z : Fin n → ℝ => Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
      (piGauss n) := by
  have hC : 0 ≤ C := by
    have h0 := hb u 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  refine Integrable.mono ((integrable_exp_l1 (|m| * (D * Real.sqrt v))).const_mul
    (Real.exp (|m| * (C + D * l1 x)))) ?_ ?_
  · exact (Real.continuous_exp.measurable.comp
      (((hmeas u).comp (measurable_shift v x)).const_mul m)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (|m| * (C + D * l1 x))
        * Real.exp (|m| * (D * Real.sqrt v) * l1 z)), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : m * A u (fun i => x i + Real.sqrt v * z i)
        ≤ |m| * |A u (fun i => x i + Real.sqrt v * z i)| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 := mul_le_mul_of_nonneg_left (shift_bound_pi hD hb x v u z) (abs_nonneg m)
    nlinarith

theorem integral_exp_shift_pi_pos (hD : 0 ≤ D) (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (hmeas : ∀ u, Measurable (A u)) (x : Fin n → ℝ) (u : ℝ) :
    0 < ∫ z, Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n) :=
  integral_exp_pos (integrable_exp_shift_pi hD hb hmeas x u)

/-- **The `m = 0` branch.** -/
theorem hasDerivAt_integral_param_pi (x : Fin n → ℝ) (u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => ∫ z, A u (fun i => x i + Real.sqrt v * z i) ∂(piGauss n))
      (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)) u₀ := by
  classical
  have hbint : Integrable
      (fun z : Fin n → ℝ => (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) (piGauss n) :=
    (integrable_const _).add (integrable_l1.const_mul _)
  have hA0 : Integrable (fun z : Fin n → ℝ => A u₀ (fun i => x i + Real.sqrt v * z i))
      (piGauss n) := by
    refine Integrable.mono ((integrable_const (C + D * l1 x)).add
        (integrable_l1.const_mul (D * Real.sqrt v)))
      ((hmeas u₀).comp (measurable_shift v x)).aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (shift_bound_pi hD hb x v u₀ z).trans (le_abs_self _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => A u (fun i => x i + Real.sqrt v * z i))
    (F' := fun u z => A' u (fun i => x i + Real.sqrt v * z i))
    (bound := fun z => (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z)
    (s := Set.univ) Filter.univ_mem ?_ hA0 ?_ ?_ hbint ?_).2
  · filter_upwards with u
    exact ((hmeas u).comp (measurable_shift v x)).aestronglyMeasurable
  · exact ((hmeas' u₀).comp (measurable_shift v x)).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs]
    exact shift_bound_pi hD' hb' x v u z
  · filter_upwards with z u _
    exact hderiv u _

/-- **The `m ≠ 0` branch, inner step.** -/
theorem hasDerivAt_integral_exp_param_pi (x : Fin n → ℝ) (u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => ∫ z, Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))
      (∫ z, m * (A' u₀ (fun i => x i + Real.sqrt v * z i)
        * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i))) ∂(piGauss n)) u₀ := by
  classical
  have hC' : 0 ≤ C' := by
    have h0 := hb' u₀ 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  set K : ℝ := Real.exp (|m| * (C + D * l1 x)) with hK
  set a0 : ℝ := |m| * (C' + D' * l1 x) * K with ha0
  set b0 : ℝ := |m| * (D' * Real.sqrt v) * K with hb0
  set c0 : ℝ := |m| * (D * Real.sqrt v) with hc0
  have hKpos : 0 < K := Real.exp_pos _
  have ha0n : 0 ≤ a0 := by rw [ha0]; positivity
  have hb0n : 0 ≤ b0 := by rw [hb0]; positivity
  have hc0n : 0 ≤ c0 := by rw [hc0]; positivity
  have hbint : Integrable (fun z : Fin n → ℝ => (a0 + b0 * l1 z) * Real.exp (c0 * l1 z))
      (piGauss n) := integrable_poly_mul_exp_l1 ha0n hb0n hc0n
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
    (F' := fun u z => m * (A' u (fun i => x i + Real.sqrt v * z i)
      * Real.exp (m * A u (fun i => x i + Real.sqrt v * z i))))
    (bound := fun z => (a0 + b0 * l1 z) * Real.exp (c0 * l1 z))
    (s := Set.univ) Filter.univ_mem ?_ (integrable_exp_shift_pi hD hb hmeas x u₀) ?_ ?_
    hbint ?_).2
  · filter_upwards with u
    exact (Real.continuous_exp.measurable.comp
      (((hmeas u).comp (measurable_shift v x)).const_mul m)).aestronglyMeasurable
  · exact ((((hmeas' u₀).comp (measurable_shift v x)).mul
      (Real.continuous_exp.measurable.comp
        (((hmeas u₀).comp (measurable_shift v x)).const_mul m))).const_mul m).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 := shift_bound_pi hD' hb' x v u z
    have h2 : Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ≤ K * Real.exp (c0 * l1 z) := by
      have hle : m * A u (fun i => x i + Real.sqrt v * z i)
          ≤ |m| * ((C + D * l1 x) + (D * Real.sqrt v) * l1 z) := by
        have hmm : m * A u (fun i => x i + Real.sqrt v * z i)
            ≤ |m| * |A u (fun i => x i + Real.sqrt v * z i)| := by
          rw [← abs_mul]; exact le_abs_self _
        have := mul_le_mul_of_nonneg_left (shift_bound_pi hD hb x v u z) (abs_nonneg m)
        linarith
      calc Real.exp (m * A u (fun i => x i + Real.sqrt v * z i))
          ≤ Real.exp (|m| * ((C + D * l1 x) + (D * Real.sqrt v) * l1 z)) :=
            Real.exp_le_exp.2 hle
        _ = K * Real.exp (c0 * l1 z) := by rw [hK, hc0, ← Real.exp_add]; ring_nf
    have hbn : (0 : ℝ) ≤ (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z :=
      le_trans (abs_nonneg _) h1
    calc |m| * (|A' u (fun i => x i + Real.sqrt v * z i)|
            * Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
        ≤ |m| * (((C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) * (K * Real.exp (c0 * l1 z))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg m)
          exact mul_le_mul h1 h2 (Real.exp_pos _).le hbn
      _ = (a0 + b0 * l1 z) * Real.exp (c0 * l1 z) := by rw [ha0, hb0]; ring
  · filter_upwards with z u _
    exact (((hderiv u _).const_mul m).exp).congr_deriv (by ring)

/--
**The tilted chain rule for one `N`-site cascade level** — Talagrand's
`∂_t F_{ℓ,t} = 𝔼_ℓ W_ℓ ∂_t F_{ℓ+1,t}`, the step iterated in (3.2).
-/
theorem hasDerivAt_parisiStepPi_param (x : Fin n → ℝ) (u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => parisiStepPi n m v (A u) x)
      (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
        * tiltWeightPi n m v (A u₀) x z ∂(piGauss n)) u₀ := by
  classical
  by_cases hm : m = 0
  · have hfun : (fun u => parisiStepPi n m v (A u) x)
        = fun u => ∫ z, A u (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext u; rw [parisiStepPi, if_pos hm]
    have hval : (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (A u₀) x z ∂(piGauss n))
        = ∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show A' u₀ (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v (A u₀) x z
          = A' u₀ (fun i => x i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun, hval]
    exact hasDerivAt_integral_param_pi x u₀ hD hD' hderiv hmeas hmeas' hb hb'
  · have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD hb hmeas x u₀
    have hfun : (fun u => parisiStepPi n m v (A u) x)
        = fun u => (1 / m) * Real.log
            (∫ z, Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n)) := by
      funext u; rw [parisiStepPi, if_neg hm]
    have hI := hasDerivAt_integral_exp_param_pi (A := A) (A' := A') (m := m) (v := v)
      (C := C) (D := D) (C' := C') (D' := D') x u₀ hD hD' hderiv hmeas hmeas' hb hb'
    have hfin := (hI.log hIpos.ne').const_mul (1 / m)
    rw [hfun]
    refine hfin.congr_deriv ?_
    rw [integral_const_mul]
    rw [show (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (A u₀) x z ∂(piGauss n))
        = ∫ z, (A' u₀ (fun i => x i + Real.sqrt v * z i)
            * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
          ∂(piGauss n) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show A' u₀ (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v (A u₀) x z
            = A' u₀ (fun i => x i + Real.sqrt v * z i)
              * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i))
              / (∫ w, Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
        rw [tiltWeightPi, if_neg hm, mul_div_assoc]))]
    rw [integral_div]
    field_simp

end ChainRule

end Targets
end SpinGlass
