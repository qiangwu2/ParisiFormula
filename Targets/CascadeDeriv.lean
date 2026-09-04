/-
# Differentiating a cascade level: the tilted (Gibbs) chain rule

New work for the ParisiFormula project (not vendored).

## What this file is for

Half 2 of Target 3 is the sign of `φ'(t)` for Guerra's interpolating cascade.  The
interpolation is arranged (see `Targets/CascadeEndpoint.lean` §8) so that `t` enters in one
place only, the base

  `base_t(y) = log ∑_σ exp (√t·U(σ) + ∑_i σ_i (√(1-t)·y_i + h))`,

with the level variances held fixed.  Differentiating `φ(t)` then means pushing `d/dt`
through `k+2` nested smoothing levels down to the base.

**This file supplies the rule for one level.**  The point is that the derivative of

  `(1/m) log ∫ exp (m · A_u(x + √v z)) dγ(z)`

with respect to the parameter `u` is the *tilted average* of `∂_u A_u`:

  `∫ (∂_u A_u)(x + √v z) · W(z) dγ(z)`,   `W(z) = exp (m A_u(x + √v z)) / ∫ exp (m A_u …)`,

and that the `m = 0` branch obeys the same formula with `W ≡ 1`.  The two branches therefore
unify, which is what makes the nested derivative computable: chaining the rule over the
levels turns `dφ/dt` into a nested tilted average — the Gibbs average over the cascade tree,
which is exactly the object `⟨·⟩_t` that Guerra's remainder
`-(β²/4) ∑_p (m_{p+1} - m_p) 𝔼⟨(R_{1,2} - q_p)²⟩` is written in.

The hypotheses are uniform-in-`u` linear growth bounds on `A` and on `∂_u A`, which is what
the domination in `hasDerivAt_integral_of_dominated_loc_of_deriv_le` needs; because they are
uniform, the neighbourhood in that lemma can be taken to be all of `ℝ`.
-/
import Targets.CascadeEndpoint

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

/-! ## 1. Integrability of the dominating functions -/

/-- `(a + b|z|) e^{c|z|}` is Gaussian-integrable: the two pieces are
`integrable_exp_abs_mul_stdGaussian` and `integrable_abs_mul_exp_abs_stdGaussian`. -/
theorem integrable_poly_mul_exp_abs (a b c : ℝ) :
    Integrable (fun z : ℝ => (a + b * |z|) * Real.exp (c * |z|)) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => a * Real.exp (c * |z|)) (gaussianReal 0 1) :=
    (integrable_exp_abs_mul_stdGaussian c).const_mul a
  have h2 : Integrable (fun z : ℝ => b * (|z| * Real.exp (c * |z|))) (gaussianReal 0 1) :=
    (integrable_abs_mul_exp_abs_stdGaussian c).const_mul b
  refine (h1.add h2).congr ?_
  filter_upwards with z
  show a * Real.exp (c * |z|) + b * (|z| * Real.exp (c * |z|))
      = (a + b * |z|) * Real.exp (c * |z|)
  ring

/-! ## 2. The tilted weight of one level -/

/--
The tilted (Gibbs) weight attached to one smoothing level.  For `m ≠ 0` it is the
exponential tilt normalised to a probability density; for `m = 0` — where the level is a
plain average — it is `1`.  Writing both branches this way is what lets the chain rule below
be stated uniformly.
-/
noncomputable def tiltWeight (m v : ℝ) (A : ℝ → ℝ) (x z : ℝ) : ℝ :=
  if m = 0 then 1
  else Real.exp (m * A (x + Real.sqrt v * z)) /
        ∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1)

/-- The tilted weight is non-negative. -/
theorem tiltWeight_nonneg {m v : ℝ} {A : ℝ → ℝ} (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (x z : ℝ) : 0 ≤ tiltWeight m v A x z := by
  unfold tiltWeight
  split
  · exact zero_le_one
  · exact div_nonneg (Real.exp_pos _).le (smoothing_integral_pos hA hmeas x).le

/-! ## 3. The chain rule for one level -/

section ChainRule

variable {A A' : ℝ → ℝ → ℝ} {m v C D C' D' : ℝ}

/-- Uniform growth transported to the shifted argument. -/
private theorem shift_bound (hD : 0 ≤ D) (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (x v : ℝ) (u z : ℝ) :
    |A u (x + Real.sqrt v * z)| ≤ (C + D * |x|) + (D * Real.sqrt v) * |z| := by
  refine (hb u _).trans ?_
  have h : |x + Real.sqrt v * z| ≤ |x| + Real.sqrt v * |z| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
  nlinarith [abs_nonneg z, Real.sqrt_nonneg v]

/--
**The `m = 0` branch.**  Differentiating under a plain Gaussian average: the derivative is
the plain average of the derivative, i.e. the tilted average with weight `1`.
-/
theorem hasDerivAt_integral_param (x u₀ : ℝ) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => ∫ z, A u (x + Real.sqrt v * z) ∂(gaussianReal 0 1))
      (∫ z, A' u₀ (x + Real.sqrt v * z) ∂(gaussianReal 0 1)) u₀ := by
  classical
  have hbint : Integrable
      (fun z : ℝ => (C' + D' * |x|) + (D' * Real.sqrt v) * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_abs_stdGaussian.const_mul _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => A u (x + Real.sqrt v * z))
    (F' := fun u z => A' u (x + Real.sqrt v * z))
    (bound := fun z => (C' + D' * |x|) + (D' * Real.sqrt v) * |z|)
    (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ hbint ?_).2
  · filter_upwards with u
    exact ((hmeas u).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).aestronglyMeasurable
  · exact integrable_of_hasLinearGrowth hA0 (hmeas u₀) x v
  · exact ((hmeas' u₀).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs]
    exact shift_bound hD' hb' x v u z
  · filter_upwards with z u _
    exact hderiv u (x + Real.sqrt v * z)


/--
**The `m ≠ 0` branch, inner step.**  Differentiating under the exponential average.
-/
theorem hasDerivAt_integral_exp_param (x u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => ∫ z, Real.exp (m * A u (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      (∫ z, m * (A' u₀ (x + Real.sqrt v * z)
        * Real.exp (m * A u₀ (x + Real.sqrt v * z))) ∂(gaussianReal 0 1)) u₀ := by
  classical
  set K : ℝ := Real.exp (|m| * (C + D * |x|)) with hK
  set a0 : ℝ := |m| * (C' + D' * |x|) * K with ha0
  set b0 : ℝ := |m| * (D' * Real.sqrt v) * K with hb0
  set c0 : ℝ := |m| * (D * Real.sqrt v) with hc0
  have hbint : Integrable (fun z : ℝ => (a0 + b0 * |z|) * Real.exp (c0 * |z|))
      (gaussianReal 0 1) := integrable_poly_mul_exp_abs _ _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => Real.exp (m * A u (x + Real.sqrt v * z)))
    (F' := fun u z => m * (A' u (x + Real.sqrt v * z)
      * Real.exp (m * A u (x + Real.sqrt v * z))))
    (bound := fun z => (a0 + b0 * |z|) * Real.exp (c0 * |z|))
    (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ hbint ?_).2
  · filter_upwards with u
    exact (Real.continuous_exp.measurable.comp
      (((hmeas u).comp
        ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m)).aestronglyMeasurable
  · exact integrable_exp_mul_of_hasLinearGrowth hA0 (hmeas u₀) m x v
  · exact ((((hmeas' u₀).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).mul
      (Real.continuous_exp.measurable.comp
        (((hmeas u₀).comp
          ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m))).const_mul
      m).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    -- `|m| · |A'| · exp (m A) ≤ (a0 + b0|z|) · exp (c0 |z|)`
    have h1 : |A' u (x + Real.sqrt v * z)|
        ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| := shift_bound hD' hb' x v u z
    have h2 : Real.exp (m * A u (x + Real.sqrt v * z)) ≤ K * Real.exp (c0 * |z|) := by
      have hle : m * A u (x + Real.sqrt v * z)
          ≤ |m| * ((C + D * |x|) + (D * Real.sqrt v) * |z|) := by
        have hmm : m * A u (x + Real.sqrt v * z) ≤ |m * A u (x + Real.sqrt v * z)| :=
          le_abs_self _
        have : |m * A u (x + Real.sqrt v * z)| = |m| * |A u (x + Real.sqrt v * z)| := abs_mul _ _
        nlinarith [shift_bound hD hb x v u z, abs_nonneg m]
      calc Real.exp (m * A u (x + Real.sqrt v * z))
          ≤ Real.exp (|m| * ((C + D * |x|) + (D * Real.sqrt v) * |z|)) := Real.exp_le_exp.2 hle
        _ = K * Real.exp (c0 * |z|) := by
            rw [hK, hc0, ← Real.exp_add]; ring_nf
    have hKpos : 0 < K := Real.exp_pos _
    have hexppos : 0 < Real.exp (c0 * |z|) := Real.exp_pos _
    have hbn : (0 : ℝ) ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| :=
      le_trans (abs_nonneg _) h1
    calc |m| * (|A' u (x + Real.sqrt v * z)| * Real.exp (m * A u (x + Real.sqrt v * z)))
        ≤ |m| * (((C' + D' * |x|) + (D' * Real.sqrt v) * |z|)
            * (K * Real.exp (c0 * |z|))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg m)
          exact mul_le_mul h1 h2 (Real.exp_pos _).le hbn
      _ = (a0 + b0 * |z|) * Real.exp (c0 * |z|) := by rw [ha0, hb0]; ring
  · filter_upwards with z u _
    have hd := ((hderiv u (x + Real.sqrt v * z)).const_mul m).exp
    exact hd.congr_deriv (by ring)

/--
**The tilted (Gibbs) chain rule for one cascade level.**

The derivative of a smoothing level with respect to a parameter of the function being
smoothed is the *tilted average* of the derivative.  Both branches of `parisiStep` obey the
same formula: for `m ≠ 0` the weight is the exponential tilt, for `m = 0` it is `1`.

Chaining this over the `k+2` levels is what turns `dφ/dt` into a nested tilted average — the
Gibbs average over the cascade tree.
-/
theorem hasDerivAt_parisiStep_param (x u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => parisiStep m v (A u) x)
      (∫ z, A' u₀ (x + Real.sqrt v * z)
        * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1)) u₀ := by
  classical
  by_cases hm : m = 0
  · have hfun : (fun u => parisiStep m v (A u) x)
        = fun u => ∫ z, A u (x + Real.sqrt v * z) ∂(gaussianReal 0 1) := by
      funext u; rw [parisiStep, if_pos hm]
    have hval : (∫ z, A' u₀ (x + Real.sqrt v * z)
          * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1))
        = ∫ z, A' u₀ (x + Real.sqrt v * z) ∂(gaussianReal 0 1) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show A' u₀ (x + Real.sqrt v * z) * tiltWeight m v (A u₀) x z
          = A' u₀ (x + Real.sqrt v * z)
      rw [tiltWeight, if_pos hm, mul_one]
    rw [hfun, hval]
    exact hasDerivAt_integral_param x u₀ hD' hderiv hmeas hmeas' hb' hA0
  · have hIpos : 0 < ∫ z, Real.exp (m * A u₀ (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      smoothing_integral_pos hA0 (hmeas u₀) x
    have hfun : (fun u => parisiStep m v (A u) x)
        = fun u => (1 / m) * Real.log
            (∫ z, Real.exp (m * A u (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) := by
      funext u; rw [parisiStep, if_neg hm]
    have hI := hasDerivAt_integral_exp_param (A := A) (A' := A') (m := m) (v := v)
      (C := C) (D := D) (C' := C') (D' := D')
      x u₀ hD hD' hderiv hmeas hmeas' hb hb' hA0
    have hlog := hI.log hIpos.ne'
    have hfin := hlog.const_mul (1 / m)
    rw [hfun]
    refine hfin.congr_deriv ?_
    -- `(1/m) · (∫ m (A' e)) / I  =  ∫ A' · (e / I)`
    rw [integral_const_mul]
    rw [show (∫ z, A' u₀ (x + Real.sqrt v * z)
          * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1))
        = ∫ z, (A' u₀ (x + Real.sqrt v * z)
            * Real.exp (m * A u₀ (x + Real.sqrt v * z)))
            / (∫ w, Real.exp (m * A u₀ (x + Real.sqrt v * w)) ∂(gaussianReal 0 1))
          ∂(gaussianReal 0 1) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show A' u₀ (x + Real.sqrt v * z) * tiltWeight m v (A u₀) x z
            = A' u₀ (x + Real.sqrt v * z) * Real.exp (m * A u₀ (x + Real.sqrt v * z))
              / (∫ w, Real.exp (m * A u₀ (x + Real.sqrt v * w)) ∂(gaussianReal 0 1))
        rw [tiltWeight, if_neg hm, mul_div_assoc]))]
    rw [integral_div]
    field_simp

end ChainRule

end Targets
end SpinGlass
