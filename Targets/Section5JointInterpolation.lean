import Targets.CoupledJointInterpolation
import Targets.Section5InterpolationPath

/-!
# Joint differentiability on Talagrand's actual second-interpolation paths

This specializes the proved simultaneous chain rule to the actual left and
right variance profiles, with their different independent/shared cutoffs.
These are pointwise-in-disorder statements. Differentiation of the outer
Gaussian average and identification of the replica covariance formula are
separate obligations.
-/

open Real Filter Topology

namespace SpinGlass.Targets

variable {n k : ℕ}

/-- Actual left interpolation, jointly in time and both fields, at fixed disorder. -/
theorem differentiableAt_section5Interpolation_joint
    (s : RSBScheme k) (β : ℝ) (U : EnergySpace n) {r : ℕ} (hr : r ≤ k + 1)
    {m t u w : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) (hw : w ∈ Set.Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance s β t u r (k + 2 - j) q.1)
        (k + 3 - r) (constrainedPairFieldBase n (Real.sqrt (q.1 * t) • U) u)
        (k + 3) q.2.1 q.2.2) (w, x, y) := by
  apply differentiableAt_constrainedFieldCascade_joint
    (fun z => Real.sqrt (z * t) • U) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega)) (k + 3 - r) (k + 3)
    ((hasDerivAt_sqrt_mul_time ht.1 hw.1).differentiableAt.smul_const U)
  · intro j hj
    exact (hasDerivAt_section5InterpolationVariance s β t u r (k + 2 - j) w).differentiableAt
  · filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    intro j
    exact section5InterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩
  · intro j hj
    rcases section5InterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
      hr (by omega) ht hu hw.2 with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)

/-- The normalized left pressure integrand is genuinely differentiable in time.
This does not yet differentiate its outer disorder expectation. -/
theorem differentiableAt_section5Interpolation_integrand
    (s : RSBScheme k) (β h : ℝ) (U : EnergySpace n) {r : ℕ} (hr : r ≤ k + 1)
    {m t u w : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) (hw : w ∈ Set.Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    DifferentiableAt ℝ (fun z =>
      (1 / (n : ℝ)) * coupledFieldCascade n
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance s β t u r (k + 2 - j) z)
        (k + 3 - r) (constrainedPairFieldBase n (Real.sqrt (z * t) • U) u)
        (k + 3) (fun _ => h) (fun _ => h)) w := by
  have H := differentiableAt_section5Interpolation_joint s β U hr hm ht hu hw
    (fun _ => h) (fun _ => h)
  have hc : DifferentiableAt ℝ
      (fun z : ℝ => (z, (fun _ : Fin n => h), (fun _ : Fin n => h))) w :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  simpa only [Function.comp_def] using (H.comp w hc).const_mul (1 / (n : ℝ))

/-- Actual right interpolation, jointly in time and both fields, at fixed disorder. -/
theorem differentiableAt_section5RightInterpolation_joint
    (s : RSBScheme k) (β : ℝ) (U : EnergySpace n) {r : ℕ} (hr : r ≤ k + 1)
    {m t u w : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) (hw : w ∈ Set.Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) q.1)
        (k + 2 - r) (constrainedPairFieldBase n (Real.sqrt (q.1 * t) • U) u)
        (k + 3) q.2.1 q.2.2) (w, x, y) := by
  apply differentiableAt_constrainedFieldCascade_joint
    (fun z => Real.sqrt (z * t) • U) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega)) (k + 2 - r) (k + 3)
    ((hasDerivAt_sqrt_mul_time ht.1 hw.1).differentiableAt.smul_const U)
  · intro j hj
    exact (hasDerivAt_section5RightInterpolationVariance s β t u r (k + 2 - j) w).differentiableAt
  · filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    intro j
    exact section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩
  · intro j hj
    rcases section5RightInterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
      hr (by omega) ht hu hw.2 with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)

/-- The normalized right pressure integrand is genuinely differentiable in time.
This does not yet differentiate its outer disorder expectation. -/
theorem differentiableAt_section5RightInterpolation_integrand
    (s : RSBScheme k) (β h : ℝ) (U : EnergySpace n) {r : ℕ} (hr : r ≤ k + 1)
    {m t u w : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) (hw : w ∈ Set.Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    DifferentiableAt ℝ (fun z =>
      (1 / (n : ℝ)) * coupledFieldCascade n
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) z)
        (k + 2 - r) (constrainedPairFieldBase n (Real.sqrt (z * t) • U) u)
        (k + 3) (fun _ => h) (fun _ => h)) w := by
  have H := differentiableAt_section5RightInterpolation_joint s β U hr hm ht hu hw
    (fun _ => h) (fun _ => h)
  have hc : DifferentiableAt ℝ
      (fun z : ℝ => (z, (fun _ : Fin n => h), (fun _ : Fin n => h))) w :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  simpa only [Function.comp_def] using (H.comp w hc).const_mul (1 / (n : ℝ))

end SpinGlass.Targets
