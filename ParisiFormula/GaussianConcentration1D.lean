/-
# One-dimensional Gaussian concentration

New work for the ParisiFormula project (not vendored).

RSAT proves the Herbst sub-Gaussian bound for Lipschitz functions of a Gaussian vector,
`SYK.product_standardGaussian_mgf_le` (note: RSAT's concentration file is in the `SYK`
namespace, not `SpinGlass`), but states it on

  `standardGaussianMeasureOnEuclidean ι = (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)`.

`Targets.parisiStep` smooths against `gaussianReal 0 1` on `ℝ`, so we need the same bound
there.  This file transports it along the singleton index `Unit`.

## Why the sharp form is needed

Target 2b must control a change of the *variance* `v` in `T_{m,v}`.  Via the semigroup law
(`SpinGlass.Parisi.T_add`) that reduces to bounding `|T_{m,w} A - A|` for small `w`, i.e.

  `(1/m) log 𝔼[exp (m g)]`,  `g = A (x + √w Z) - A x`,  `|g| ≤ L √w |Z|`.

The naive bound `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)` contributes `(log 2)/m`, which **blows up as
`m → 0`** — fatal, since an RSB scheme may have arbitrarily small `m_p`.  The sub-Gaussian
form `𝔼[exp (a (|Z| - 𝔼|Z|))] ≤ exp (a²/2)` has `(1/m) log (…) = O(1)` instead, which is
what keeps the eventual Lipschitz constant uniform in `k`.
-/
import ParisiFormula.GaussianCosh
import Lemmas.SpinGlass.gaussian_concentration

open MeasureTheory ProbabilityTheory Real

-- RSAT's concentration results live in the `SYK` namespace, not `SpinGlass`.
open SYK

open scoped BigOperators NNReal

namespace SpinGlass

/-! ## 1. Transporting integrals along the singleton index -/

/-- The measure-preserving identification `(Unit → ℝ) ≃ᵐ ℝ` for the Gaussian. -/
theorem measurePreserving_funUnique_gaussian :
    MeasurePreserving (MeasurableEquiv.funUnique Unit ℝ)
      (Measure.pi fun _ : Unit => gaussianReal 0 1) (gaussianReal 0 1) :=
  measurePreserving_funUnique (gaussianReal 0 1) Unit

/--
Integrals against the one-dimensional Euclidean Gaussian are integrals against
`gaussianReal 0 1`.
-/
theorem integral_standardGaussianOnEuclidean_unit (G : EuclideanSpace ℝ Unit → ℝ)
    (hG : Measurable G) :
    (∫ x, G x ∂(standardGaussianMeasureOnEuclidean Unit))
      = ∫ z : ℝ, G (WithLp.toLp 2 (fun _ : Unit => z)) ∂(gaussianReal 0 1) := by
  classical
  rw [standardGaussianMeasureOnEuclidean, integral_map]
  · -- now an integral over `Measure.pi fun _ : Unit => gaussianReal 0 1`
    have hfun : ∀ y : Unit → ℝ,
        G (WithLp.toLp 2 y)
          = (fun z : ℝ => G (WithLp.toLp 2 (fun _ : Unit => z)))
              (MeasurableEquiv.funUnique Unit ℝ y) := by
      intro y
      have : (fun _ : Unit => y default) = y := by
        funext u
        simp [Unique.eq_default u]
      simp [MeasurableEquiv.funUnique, this]
    calc (∫ y, G (WithLp.toLp 2 y) ∂(Measure.pi fun _ : Unit => gaussianReal 0 1))
        = ∫ y, (fun z : ℝ => G (WithLp.toLp 2 (fun _ : Unit => z)))
            (MeasurableEquiv.funUnique Unit ℝ y)
            ∂(Measure.pi fun _ : Unit => gaussianReal 0 1) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hfun)
      _ = ∫ z : ℝ, G (WithLp.toLp 2 (fun _ : Unit => z)) ∂(gaussianReal 0 1) :=
          measurePreserving_funUnique_gaussian.integral_comp' _
  · exact (WithLp.measurableEquiv 2 _).measurable.aemeasurable
  · exact hG.aestronglyMeasurable

/-! ## 2. Lipschitz functions on the one-dimensional Euclidean space -/

/-- `dist` on `EuclideanSpace ℝ Unit` is the absolute difference of the single coordinate. -/
theorem dist_euclidean_unit (x y : EuclideanSpace ℝ Unit) :
    dist x y = |x default - y default| := by
  rw [EuclideanSpace.dist_eq]
  rw [Finset.sum_unique_nonempty] <;> simp [Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- A Lipschitz `f : ℝ → ℝ` lifts to a Lipschitz function on `EuclideanSpace ℝ Unit`. -/
theorem lipschitzWith_euclidean_unit {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x : EuclideanSpace ℝ Unit => f (x default)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_euclidean_unit x y, Real.dist_eq]
  simpa [Real.dist_eq] using hf.dist_le_mul (x default) (y default)

/-! ## 3. The one-dimensional Herbst bound -/

/--
**Sub-Gaussian moment generating function for a Lipschitz function of a standard Gaussian**,
in one dimension:

  `𝔼[exp (t (f Z - 𝔼 f Z))] ≤ exp (L² t² / 2)`.

Transported from RSAT's `product_standardGaussian_mgf_le` along the singleton index.
-/
theorem gaussianReal_mgf_le_of_lipschitz (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal f) (hmeas : Measurable f) (t : ℝ) :
    mgf (fun z : ℝ => f z - ∫ y : ℝ, f y ∂(gaussianReal 0 1)) (gaussianReal 0 1) t
      ≤ Real.exp (L ^ 2 * t ^ 2 / 2) := by
  classical
  set F : EuclideanSpace ℝ Unit → ℝ := fun x => f (x default) with hFdef
  have hFmeas : Measurable F := hmeas.comp (by fun_prop)
  have hFlip : LipschitzWith L.toNNReal F := lipschitzWith_euclidean_unit hLip
  -- the two means agree
  have hmean : (∫ x, F x ∂(standardGaussianMeasureOnEuclidean Unit))
      = ∫ y : ℝ, f y ∂(gaussianReal 0 1) := by
    rw [integral_standardGaussianOnEuclidean_unit F hFmeas]
    simp [hFdef]
  -- and so do the two mgfs
  have hmgf : mgf (fun x => F x - ∫ y, F y ∂(standardGaussianMeasureOnEuclidean Unit))
      (standardGaussianMeasureOnEuclidean Unit) t
      = mgf (fun z : ℝ => f z - ∫ y : ℝ, f y ∂(gaussianReal 0 1)) (gaussianReal 0 1) t := by
    simp only [mgf]
    rw [integral_standardGaussianOnEuclidean_unit
      (fun x => Real.exp (t * (F x - ∫ y, F y ∂(standardGaussianMeasureOnEuclidean Unit))))
      (by fun_prop)]
    simp [hFdef, hmean]
  rw [← hmgf]
  exact product_standardGaussian_mgf_le F L hL hFlip t

end SpinGlass
