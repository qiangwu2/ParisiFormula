import Targets.CoupledReplicaHeat

/-!
# Bounded parameter transport through arbitrary Gaussian field directions

The existing finite-dimensional parameter differentiation theorem supplies the
actual derivative. This adapter packages its growth, measurability, and uniform
bound so it can be iterated through frozen levels of a mixed Gaussian cascade.
No cutoff, sign, or ordering restriction is imposed on the field matrices.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n p : ℕ}

/-- A fixed arbitrary-direction Gaussian level preserves the full actual
parameter calculus package, with no loss in the derivative bound. Zero masses
and variances, independent fields, and opposite directions are all included. -/
theorem CoupledParamDeriv.linearStep
    {F G : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K mass variance : ℝ}
    (h : CoupledParamDeriv F G s K) (hs : IsOpen s)
    (hm : 0 ≤ mass) (hv : 0 ≤ variance) (A B : Fin p → Fin n → ℝ) :
    CoupledParamDeriv (fun a => coupledLinearStep mass variance A B (F a))
      (fun a => coupledLinearMean mass variance A B (F a) (G a)) s K := by
  obtain ⟨C, D, hD, hb⟩ := h.growth
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hDL : 0 ≤ D * L := mul_nonneg hD hL
  refine ⟨fun a ha x y => h.hasDerivAt_linearStep (hs.mem_nhds ha) mass variance A B x y,
    fun a ha => measurable_coupledLinearStep (h.measurable a ha) A B mass variance,
    fun a ha => measurable_coupledLinearMean (h.measurable a ha)
      (h.measurable_deriv a ha) A B mass variance,
    ⟨C + stepK p mass variance (D * L), D, hD, ?_⟩, ?_⟩
  · intro a ha x y
    have H := parisiStepPi_abs_le (C := C + D * (l1 x + l1 y)) hm hv hDL
      (coupled_linear_growth_bound hD (hb a ha) A B x y)
      ((h.growth_at ha).linear_input A B x y).measurable (0 : Fin p → ℝ)
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at H
    exact H.trans_eq (by ring)
  · intro a ha x y
    exact pairedTiltMean_abs_le ((h.growth_at ha).linear_input A B x y)
      ((h.measurable_deriv a ha).comp
        ((measurable_const.add (measurable_pairedFieldLinear A)).prodMk
          (measurable_const.add (measurable_pairedFieldLinear B))))
      (fun z => h.bound a ha _ _) 0

end SpinGlass.Targets
