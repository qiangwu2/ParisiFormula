import Targets.MixedJointInterpolation
import Targets.Section5InterleavedZero

/-!
# Actual interior differentiation of the tagged integrand

Every active-face hypothesis of the general mixed joint theorem is discharged
for Talagrand's actual tagged paths. Frozen zero variances are kept, not
approximated by positive ones. The outer average and trace-plus-heat
identification are separate obligations.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The genuine tagged integrand is differentiable throughout the open second
time interval. Physical time zero and both overlap signs are included. -/
theorem differentiableAt_section5InterleavedIntegrand {k n : ℕ} (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun a =>
      mixedVectorListCascade n (section5TaggedMode r j (decide (u < 0)))
        (section5TaggedMass s r j) (section5TaggedPathVariance s β t |u| j a)
        (List.ofFn (section5Interleaving s r j))
        (constrainedPairFieldBase n (Real.sqrt (a * t) • U) u) x y) w := by
  let N := (k + 2) + (k + 3)
  let tag : ℕ → Section5MassTag k := fun i =>
    section5Interleaving s r j ⟨N - 1 - i, by omega⟩
  let mode := fun i => section5TaggedMode r j (decide (u < 0)) (tag i)
  let m := fun i => section5TaggedMass s r j (tag i)
  let v := fun i a => section5TaggedPathVariance s β t |u| j a (tag i)
  have hU : DifferentiableAt ℝ (fun a : ℝ => Real.sqrt (a * t) • U) w := by
    rcases ht.1.eq_or_lt with hz | hp
    · simp only [← hz, mul_zero, Real.sqrt_zero, zero_smul]
      exact differentiableAt_const _
    · exact (((Real.hasDerivAt_sqrt (mul_pos hw.1 hp).ne').differentiableAt).comp w
        ((differentiableAt_id).mul_const t)).smul_const U
  have hm (i : ℕ) : 0 ≤ m i := (section5TaggedMass_mem_Icc s r hj (tag i)).1
  have hv (i : ℕ) : DifferentiableAt ℝ (v i) w := by
    dsimp [v]
    cases tag i <;> dsimp [section5TaggedPathVariance] <;> fun_prop
  have hnonneg : ∀ᶠ a in 𝓝 w, ∀ i, 0 ≤ v i a := by
    filter_upwards [Iio_mem_nhds hw.2] with a ha i
    exact section5TaggedPathVariance_nonneg s β ht hj hu ha.le (tag i)
  have hface (i : ℕ) : 0 < v i w ∨ (v i =ᶠ[𝓝 w] fun _ => 0) := by
    rcases section5TaggedPathVariance_pos_or_eq_zero s β ht hj hu hw.2 (tag i) with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := hasDerivAt_mixedConstrainedCascade_path_fderiv
    (fun a => Real.sqrt (a * t) • U) u mode m v hm N hU
    (fun i _ => hv i) hnonneg (fun i _ => hface i) x y
  apply H.differentiableAt.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro a
  exact congrFun (congrFun
    (mixedVectorListCascade_ofFn n (show 0 < N by omega)
      (section5TaggedMode r j (decide (u < 0))) (section5TaggedMass s r j)
      (section5TaggedPathVariance s β t |u| j a) (section5Interleaving s r j)
      (constrainedPairFieldBase n (Real.sqrt (a * t) • U) u)) x) y

end SpinGlass.Targets
