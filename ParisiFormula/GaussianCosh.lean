/-
# Gaussian integrals of `cosh` and `log cosh`

New work for the ParisiFormula project (not vendored).

These are the analytic ingredients of **Target 2a** (`parisiFunctional_rsScheme`), the
replica-symmetric sanity check of the Parisi functional in `Targets/Milestones.lean`.

The three facts needed there are:

* `integral_cosh_add_mul_stdGaussian` : `∫ cosh (x + σ z) dγ(z) = cosh x · exp (σ²/2)`.
  This is what turns the `m = 1` smoothing step `T_{1, β²(1-q)}` applied to `log cosh`
  into `log cosh x + β²(1-q)/2`.

* `integrable_log_cosh_stdGaussian` : `z ↦ log cosh (a z + b)` is `γ`-integrable, which
  is what lets the `m = 0` step be split as
  `∫ (log cosh (h + c z) + const) dγ = ∫ log cosh (h + c z) dγ + const`.

* `integral_reflect_stdGaussian` : `∫ f (b - a z) dγ = ∫ f (b + a z) dγ`.
  This is needed because `√(β² q) = |β| √q`, while Target 2a is stated with `β √q` and
  *no* sign hypothesis on `β`; the two agree under the (symmetric) Gaussian.

Throughout, `γ = gaussianReal 0 1` is the standard Gaussian on `ℝ`.
-/
import ParisiFormula.AnnealedBound
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass

/-! ## 1. The Gaussian exponential moment -/

/-- `∫ exp (t z) dγ(z) = exp (t²/2)` for the standard Gaussian `γ`. -/
theorem integral_exp_mul_stdGaussian (t : ℝ) :
    (∫ z, Real.exp (t * z) ∂(gaussianReal 0 1)) = Real.exp (t ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id_eq] at h
  rw [h]
  norm_num

/-- `exp (t · )` is `γ`-integrable. -/
theorem integrable_exp_mul_stdGaussian (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t * z)) (gaussianReal 0 1) :=
  integrable_exp_mul_gaussianReal t

/-! ## 2. The Gaussian integral of `cosh` -/

/--
**The key Gaussian `cosh` integral**: `∫ cosh (x + σ z) dγ(z) = cosh x · exp (σ²/2)`.

This is the identity behind the `m = 1` replica-symmetric smoothing step.
-/
theorem integral_cosh_add_mul_stdGaussian (x σ : ℝ) :
    (∫ z, Real.cosh (x + σ * z) ∂(gaussianReal 0 1))
      = Real.cosh x * Real.exp (σ ^ 2 / 2) := by
  have hpt : ∀ z : ℝ, Real.cosh (x + σ * z)
      = Real.exp x / 2 * Real.exp (σ * z)
        + Real.exp (-x) / 2 * Real.exp (-σ * z) := by
    intro z
    rw [Real.cosh_eq]
    rw [show x + σ * z = x + σ * z from rfl]
    rw [Real.exp_add, show -(x + σ * z) = -x + -σ * z by ring, Real.exp_add]
    ring
  have hint1 : Integrable (fun z : ℝ => Real.exp x / 2 * Real.exp (σ * z))
      (gaussianReal 0 1) := (integrable_exp_mul_stdGaussian σ).const_mul _
  have hint2 : Integrable (fun z : ℝ => Real.exp (-x) / 2 * Real.exp (-σ * z))
      (gaussianReal 0 1) := (integrable_exp_mul_stdGaussian (-σ)).const_mul _
  calc
    (∫ z, Real.cosh (x + σ * z) ∂(gaussianReal 0 1))
        = ∫ z, (Real.exp x / 2 * Real.exp (σ * z)
              + Real.exp (-x) / 2 * Real.exp (-σ * z)) ∂(gaussianReal 0 1) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z, Real.exp x / 2 * Real.exp (σ * z) ∂(gaussianReal 0 1))
          + ∫ z, Real.exp (-x) / 2 * Real.exp (-σ * z) ∂(gaussianReal 0 1) :=
          integral_add hint1 hint2
    _ = Real.exp x / 2 * Real.exp (σ ^ 2 / 2)
          + Real.exp (-x) / 2 * Real.exp ((-σ) ^ 2 / 2) := by
          rw [integral_const_mul, integral_const_mul,
              integral_exp_mul_stdGaussian σ, integral_exp_mul_stdGaussian (-σ)]
    _ = Real.cosh x * Real.exp (σ ^ 2 / 2) := by
          rw [Real.cosh_eq]
          rw [show (-σ) ^ 2 = σ ^ 2 by ring]
          ring

/-! ## 3. Integrability of `log cosh` -/

/-- `0 ≤ log (cosh y)`, since `1 ≤ cosh y`. -/
theorem log_cosh_nonneg (y : ℝ) : 0 ≤ Real.log (Real.cosh y) :=
  Real.log_nonneg (Real.one_le_cosh y)

/-- `log (cosh y) ≤ |y|`, since `cosh y ≤ exp |y|`. -/
theorem log_cosh_le_abs (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
  have hcosh : Real.cosh y ≤ Real.exp |y| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
    have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.2 (neg_le_abs y)
    linarith
  calc
    Real.log (Real.cosh y) ≤ Real.log (Real.exp |y|) :=
      Real.log_le_log (Real.cosh_pos y) hcosh
    _ = |y| := Real.log_exp _

/--
`z ↦ log cosh (b + a z)` is continuous.  (`fun_prop` cannot do this on its own: `Real.log`
is not continuous at `0`, so it needs `cosh > 0`.)
-/
theorem continuous_log_cosh_affine (a b : ℝ) :
    Continuous (fun z : ℝ => Real.log (Real.cosh (b + a * z))) :=
  (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => ne_of_gt (Real.cosh_pos _))

/-- `z ↦ z` is `γ`-integrable. -/
theorem integrable_id_stdGaussian :
    Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (le_refl 1)

/-- `z ↦ log cosh (b + a z)` is `γ`-integrable, by `0 ≤ log cosh y ≤ |y|`. -/
theorem integrable_log_cosh_stdGaussian (a b : ℝ) :
    Integrable (fun z : ℝ => Real.log (Real.cosh (b + a * z))) (gaussianReal 0 1) := by
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => Real.log (Real.cosh (b + a * z))) (gaussianReal 0 1) :=
    (continuous_log_cosh_affine a b).aestronglyMeasurable
  have hdom : Integrable (fun z : ℝ => |b + a * z|) (gaussianReal 0 1) :=
    ((integrable_const b).add (integrable_id_stdGaussian.const_mul a)).abs
  refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg _)]
  exact log_cosh_le_abs _

/-! ## 4. Reflection symmetry of the standard Gaussian -/

/--
`∫ f (b + a z) dγ(z) = ∫ f (b - a z) dγ(z)`: the standard Gaussian is symmetric.

Needed because `√(β² q) = |β| √q`, while Target 2a is stated with `β √q` and no sign
hypothesis on `β`.
-/
theorem integral_reflect_stdGaussian {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    (∫ z, f (b + a * z) ∂(gaussianReal 0 1))
      = ∫ z, f (b + -a * z) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hcont : Continuous (fun z : ℝ => f (b + a * z)) :=
    hf.comp (continuous_const.add (continuous_const.mul continuous_id))
  calc
    (∫ z, f (b + a * z) ∂(gaussianReal 0 1))
        = ∫ z, f (b + a * z) ∂((gaussianReal 0 1).map (fun x : ℝ => -x)) := by
          rw [hmap]
    _ = ∫ z, f (b + a * -z) ∂(gaussianReal 0 1) := by
          rw [integral_map measurable_neg.aemeasurable hcont.aestronglyMeasurable]
    _ = ∫ z, f (b + -a * z) ∂(gaussianReal 0 1) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          show f (b + a * -z) = f (b + -a * z)
          congr 1
          ring

/-! ## 5. Gaussian rescaling -/

/--
**Rescaling a standard Gaussian**: `∫ f (x + √v z) dγ_{0,1}(z) = ∫ f (x + w) dγ_{0,v}(w)`.

This is the identity that reconciles `Targets.parisiStep` (which smooths against the
*standard* Gaussian after scaling the variable by `√v`) with `SpinGlass.Parisi.T` (which
smooths against `γ_{0,v}` directly).
-/
theorem integral_comp_sqrt_mul_gaussianReal (v : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f)
    (x : ℝ) :
    (∫ z, f (x + Real.sqrt (v : ℝ) * z) ∂(gaussianReal 0 1))
      = ∫ w, f (x + w) ∂(gaussianReal 0 v) := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z)
      = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    -- `congr 1` splits into the mean and variance components; this avoids having to
    -- match `NNReal.mk` syntactically (proof terms are handled by irrelevance).
    congr 1
    · ring
    · rw [mul_one]
      exact NNReal.coe_injective (by simpa using Real.sq_sqrt v.coe_nonneg)
  have hcomp : Measurable (fun w : ℝ => f (x + w)) := hf.comp (measurable_const_add x)
  have h := integral_map (μ := gaussianReal (0 : ℝ) 1)
    (φ := fun z : ℝ => Real.sqrt (v : ℝ) * z) (by fun_prop)
    (f := fun w : ℝ => f (x + w)) hcomp.aestronglyMeasurable
  rw [hmap] at h
  exact h.symm

/-! ## 6. Linear growth and the integrability it buys

Target 2b's inductive engine (`Targets.parisiStep_dist_le`) carries integrability
hypotheses.  Discharging them for `parisiF` at every level is the "moderate growth" item of
Phase 2 in `docs/ROADMAP.md`.  The right invariant is *linear* growth: the base of the Parisi
recursion is `log cosh`, which satisfies `0 ≤ log cosh y ≤ |y|`, and each smoothing step
preserves linear growth.
-/

/-- `exp (a |z|)` is `γ`-integrable, for every real `a`. -/
theorem integrable_exp_abs_mul_stdGaussian (a : ℝ) :
    Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 1) := by
  have hdom : Integrable
      (fun z : ℝ => Real.exp (a * z) + Real.exp (-a * z)) (gaussianReal 0 1) :=
    (integrable_exp_mul_stdGaussian a).add (integrable_exp_mul_stdGaussian (-a))
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 1) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have : 0 < Real.exp (-a * z) := Real.exp_pos _
    linarith
  · rw [abs_of_neg hz, show a * -z = -a * z by ring]
    have : 0 < Real.exp (a * z) := Real.exp_pos _
    linarith

/-- `A` has at most linear growth: `|A y| ≤ C + D |y|` for some `C, D ≥ 0`. -/
def HasLinearGrowth (A : ℝ → ℝ) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ y, |A y| ≤ C + D * |y|

/-- The base of the Parisi recursion has linear growth: `|log cosh y| ≤ |y|`. -/
theorem hasLinearGrowth_log_cosh :
    HasLinearGrowth (fun y => Real.log (Real.cosh y)) := by
  refine ⟨0, 1, le_rfl, zero_le_one, fun y => ?_⟩
  rw [abs_of_nonneg (log_cosh_nonneg y)]
  simpa using log_cosh_le_abs y

/-- A linearly growing measurable function is `γ`-integrable along `z ↦ x + √v z`. -/
theorem integrable_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x v : ℝ) :
    Integrable (fun z : ℝ => A (x + Real.sqrt v * z)) (gaussianReal 0 1) := by
  obtain ⟨C, D, hC, hD, hbound⟩ := hA
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ => A (x + Real.sqrt v * z)) (gaussianReal 0 1) :=
    (hmeas.comp (measurable_const_add x |>.comp (measurable_id.const_mul _)))
      |>.aestronglyMeasurable
  have hdom : Integrable
      (fun z : ℝ => (C + D * |x|) + (D * |Real.sqrt v|) * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add
      ((integrable_id_stdGaussian.abs).const_mul _)
  refine hdom.mono' hmeas' (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs]
  refine (hbound (x + Real.sqrt v * z)).trans ?_
  have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
    calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
      _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
  nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]

/-- The exponential of a linearly growing measurable function is `γ`-integrable. -/
theorem integrable_exp_mul_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m x v : ℝ) :
    Integrable (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) := by
  obtain ⟨C, D, hC, hD, hbound⟩ := hA
  set a : ℝ := |m| * (D * |Real.sqrt v|) with ha
  set b : ℝ := |m| * (C + D * |x|) with hb
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) :=
    ((Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_const_add x |>.comp (measurable_id.const_mul _))).const_mul m))
      |>.aestronglyMeasurable
  have hdom : Integrable
      (fun z : ℝ => Real.exp b * Real.exp (a * |z|)) (gaussianReal 0 1) :=
    (integrable_exp_abs_mul_stdGaussian a).const_mul _
  refine hdom.mono' hmeas' (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
    calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
      _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
  have h1 : m * A (x + Real.sqrt v * z) ≤ |m| * |A (x + Real.sqrt v * z)| := by
    calc m * A (x + Real.sqrt v * z) ≤ |m * A (x + Real.sqrt v * z)| := le_abs_self _
      _ = |m| * |A (x + Real.sqrt v * z)| := abs_mul _ _
  have h2 : |A (x + Real.sqrt v * z)| ≤ C + D * (|x| + |Real.sqrt v| * |z|) := by
    refine (hbound (x + Real.sqrt v * z)).trans ?_
    nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]
  have h3 : |m| * |A (x + Real.sqrt v * z)| ≤ |m| * (C + D * (|x| + |Real.sqrt v| * |z|)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg m)
  have h4 : |m| * (C + D * (|x| + |Real.sqrt v| * |z|)) = b + a * |z| := by
    rw [ha, hb]; ring
  linarith

/-! ## 7. `log cosh` is 1-Lipschitz

Linear growth (§6) buys integrability.  For Target 2b one also needs *Lipschitz* control:
when the scheme parameter `q_p` moves, the variance of the smoothing step moves, and the
argument `x + √v z` moves by `(√v - √v') z` — which is not uniformly small, so
`parisiStep_dist_le` cannot be applied to it unless the function being smoothed is Lipschitz.

The base of the Parisi recursion is 1-Lipschitz, and (via `parisiStep_dist_le`, applied after
translating the argument) the smoothing step does not increase the Lipschitz constant.  So
every level `F_p` of the recursion is 1-Lipschitz.
-/

/-- `cosh a ≤ cosh b · exp |a - b|`. -/
theorem cosh_le_cosh_mul_exp_abs (a b : ℝ) :
    Real.cosh a ≤ Real.cosh b * Real.exp |a - b| := by
  rw [Real.cosh_eq, Real.cosh_eq]
  rcases le_or_gt b a with hab | hab
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    have e1 : Real.exp b * Real.exp (a - b) = Real.exp a := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-b) * Real.exp (a - b) = Real.exp (a - 2 * b) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : (Real.exp b + Real.exp (-b)) / 2 * Real.exp (a - b)
        = (Real.exp a + Real.exp (a - 2 * b)) / 2 := by
      rw [div_mul_eq_mul_div, add_mul, e1, e2]
    rw [hexp]
    have h : Real.exp (-a) ≤ Real.exp (a - 2 * b) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · rw [abs_of_neg (by linarith : a - b < 0)]
    have e1 : Real.exp b * Real.exp (-(a - b)) = Real.exp (2 * b - a) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-b) * Real.exp (-(a - b)) = Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : (Real.exp b + Real.exp (-b)) / 2 * Real.exp (-(a - b))
        = (Real.exp (2 * b - a) + Real.exp (-a)) / 2 := by
      rw [div_mul_eq_mul_div, add_mul, e1, e2]
    rw [hexp]
    have h : Real.exp a ≤ Real.exp (2 * b - a) :=
      Real.exp_le_exp.2 (by linarith)
    linarith

/-- **`log cosh` is 1-Lipschitz.**  This is the base case of the Lipschitz induction. -/
theorem log_cosh_dist_le (a b : ℝ) :
    |Real.log (Real.cosh a) - Real.log (Real.cosh b)| ≤ |a - b| := by
  have hone : ∀ u w : ℝ,
      Real.log (Real.cosh u) - Real.log (Real.cosh w) ≤ |u - w| := by
    intro u w
    have h := Real.log_le_log (Real.cosh_pos u) (cosh_le_cosh_mul_exp_abs u w)
    rw [Real.log_mul (ne_of_gt (Real.cosh_pos w)) (Real.exp_ne_zero _), Real.log_exp] at h
    linarith
  refine abs_le.2 ⟨?_, hone a b⟩
  have h := hone b a
  rw [abs_sub_comm] at h
  linarith

/-! ## 8. Shifting a Lipschitz function by a Gaussian

The remaining quantitative input for Target 2b is a bound on `|T_{m,w} A - A|` for small
variance `w`, which via the semigroup law `Parisi.T_add` controls a change of the scheme
parameter `q_p`.

This section proves the `m = 0` case, which is also the *mean* term of the general case:
writing `g z = A (x + √w z) - A x`, the general bound is `|𝔼 g| + |m| L² w / 2`, with the
second term coming from the Herbst bound of §`GaussianConcentration1D` and the first from
the estimate here.
-/

/--
**Shifting a Lipschitz function by a centred Gaussian moves its mean by at most
`L √w 𝔼|Z|`.**

This is exactly the `m = 0` branch of `parisiStep`, and simultaneously the mean term of the
`m ≠ 0` branch.
-/
theorem abs_integral_shift_sub_le {A : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x w : ℝ) :
    |(∫ z, A (x + Real.sqrt w * z) ∂(gaussianReal 0 1)) - A x|
      ≤ L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := by
  classical
  have hint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z)) (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth hA hmeas x w
  have hdom : Integrable
      (fun z : ℝ => L * Real.sqrt w * |z|) (gaussianReal 0 1) :=
    (integrable_id_stdGaussian.abs).const_mul _
  have hpt : ∀ z : ℝ, |A (x + Real.sqrt w * z) - A x| ≤ L * Real.sqrt w * |z| := by
    intro z
    have h := hLip (x + Real.sqrt w * z) x
    have hrw : |x + Real.sqrt w * z - x| = Real.sqrt w * |z| := by
      rw [show x + Real.sqrt w * z - x = Real.sqrt w * z by ring, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg w)]
    rw [hrw] at h
    calc |A (x + Real.sqrt w * z) - A x| ≤ L * (Real.sqrt w * |z|) := h
      _ = L * Real.sqrt w * |z| := by ring
  calc |(∫ z, A (x + Real.sqrt w * z) ∂(gaussianReal 0 1)) - A x|
      = |∫ z, (A (x + Real.sqrt w * z) - A x) ∂(gaussianReal 0 1)| := by
        rw [integral_sub hint (integrable_const _)]
        simp [probReal_univ]
    _ ≤ ∫ z, |A (x + Real.sqrt w * z) - A x| ∂(gaussianReal 0 1) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (gaussianReal 0 1))
            (f := fun z => A (x + Real.sqrt w * z) - A x)
    _ ≤ ∫ z, L * Real.sqrt w * |z| ∂(gaussianReal 0 1) :=
        integral_mono (hint.sub (integrable_const _)).abs hdom hpt
    _ = L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := integral_const_mul _ _


end SpinGlass
