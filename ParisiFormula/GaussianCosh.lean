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
    Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (le_refl 1)
  simpa [id] using h

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
          rw [show a * -z = -a * z by ring]

end SpinGlass
