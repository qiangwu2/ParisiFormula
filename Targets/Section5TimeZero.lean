import Targets.Section5LambdaUPrime
import Targets.Section4StationarityTerminal

/-!
# The constrained overlap deficit at time zero

At time zero the second interpolation is constant, for every attainable
overlap, not only an overlap between adjacent trial values.  Its actual
lambda tilt therefore gives a quadratic deficit directly.  Stationarity
identifies the centre of that deficit with the original trial overlap.

This treats the zero-time boundary separately from strict mixed-Gaussian
comparisons, whose active-variance hypotheses fail at time zero.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]

/-- The second interpolation is constant when the original time is zero.
This identity has no restriction on the constrained overlap. -/
theorem section5Interpolation_time_zero {n k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m u w : ℝ) :
    section5Interpolation n s β h U r m 0 u w =
      section5Interpolation n s β h U r m 0 u 0 := by
  simp only [section5Interpolation, section5InterpolationVariance, mul_zero,
    zero_mul, add_zero, Real.sqrt_zero, zero_smul]

/-- At time zero the original constrained pressure is the actual field
endpoint, even when the overlap lies outside the neighbouring interval. -/
theorem constrainedPhi_time_zero_eq_fieldEndpoint
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) (m u : ℝ) :
    constrainedPhi n s β h U (k + 2 - r) 0 u =
      section5FieldEndpoint n s β h u r m 0 := by
  rw [← section5Interpolation_one n s β h U hr0 hr m u (t := 0) (by norm_num),
    section5Interpolation_time_zero, section5Interpolation_zero, zero_mul]

/-- The actual zero-time constrained pressure has a quadratic deficit about
its actual baseline lambda slope.  The overlap is any attainable real value;
neither a neighbouring-interval hypothesis nor disorder regularity is needed. -/
theorem constrainedPhi_time_zero_le_guerraPsi_Q
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n s β h U (k + 2 - r) 0 u ≤
      2 * guerraPsi s β h 0 -
        (section4TVarianceQ s β h r (s.m (r - 1)) 0 - u) ^ 2 / 2 := by
  have hv : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (by
      simpa only [Nat.sub_add_cancel hr0] using s.q_mono (r - 1) (by omega)))⟩
  obtain ⟨l, hl⟩ := section5V_baseline_lambda_gain_Q s β h hr0 hr hv u
  rw [constrainedPhi_time_zero_eq_fieldEndpoint s β h U hr0 hr (s.m (r - 1)) u]
  have H := section5FieldEndpoint_le hn s β h u hr (m := s.m (r - 1))
    (s.m_nonneg (by omega)) hv hu l
  unfold guerraPsi
  nlinarith

/-- The zero-time deficit, with an explicitly identified endpoint slope. -/
theorem constrainedPhi_time_zero_le_guerraPsi_of_Q
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : ∃ σ τ : Config n, overlap n σ τ = u)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r) :
    constrainedPhi n s β h U (k + 2 - r) 0 u ≤
      2 * guerraPsi s β h 0 - (u - s.q r) ^ 2 / 2 := by
  have H := constrainedPhi_time_zero_le_guerraPsi_Q hn s β h U hr0 hr hu
  rw [hQ] at H
  nlinarith

/-- Original fixed-level minimality and genuine all-level stationarity give
the zero-time quadratic bound for every attainable overlap.  This includes
the initial and terminal trial levels and the zero initial-overlap face. -/
theorem constrainedPhi_time_zero_le_guerraPsi_of_min
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {u : ℝ} (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n s β h U (k + 2 - r) 0 u ≤
      2 * guerraPsi s β h 0 - (u - s.q r) ^ 2 / 2 := by
  exact constrainedPhi_time_zero_le_guerraPsi_of_Q hn s β h U hr0 hr hu
    (section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ
      hm hleft hright hmin)

/-- At time zero every attainable overlap distinct from the stationary trial
overlap has a strict deficit in the original constrained pressure. -/
theorem constrainedPhi_time_zero_lt_guerraPsi_of_min
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {u : ℝ} (hu : ∃ σ τ : Config n, overlap n σ τ = u) (hne : u ≠ s.q r) :
    constrainedPhi n s β h U (k + 2 - r) 0 u < 2 * guerraPsi s β h 0 := by
  have H := constrainedPhi_time_zero_le_guerraPsi_of_min hn s β h U hr0 hr hβ
    hm hleft hright hmin hu
  have hp : 0 < (u - s.q r) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  linarith

end SpinGlass.Targets
