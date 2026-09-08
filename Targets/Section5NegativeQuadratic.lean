import Targets.Section5NegativeCompact

/-!
# Quadratic assembly on a compact negative-overlap trial

The negative-overlap compact adapter supplies a uniform additive scalar gap.
Since both the physical overlap and every trial overlap lie in `[-1, 1]`, that
gap immediately gives the quadratic form required by Theorem 2.4 on the
compact region.  This is one genuine regional piece of the global assembly;
it does not assert the missing positive-side cover.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A compact negative-overlap trial interval has one finite-size-uniform
quadratic deficit about the physical trial overlap. -/
theorem exists_uniform_quadratic_bound_negative_trial
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0)
    (htrial : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j)) :
    ∃ K > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - (z.2 - s.q r) ^ 2 / K := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_constrainedPhi_negative_trial (Ω := Ω)
    s β h hβ hr0 hr hj0 hj hm hq hQ ht₀ hS ht hu htrial
  let K : ℝ := 4 / δ
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by norm_num) hδ
  refine ⟨K, hK, ?_⟩
  intro z hz n hn sk hatt
  have Hgap := hgap z hz hn sk hatt
  have hqlo : 0 ≤ s.q r := s.q_nonneg (by omega)
  have hqhi : s.q r ≤ 1 := s.q_le_one (by omega)
  obtain ⟨σ, τ, hστ⟩ := hatt
  have huabs : |z.2| ≤ 1 := by
    rw [← hστ]
    exact abs_overlap_le_one hn σ τ
  have hqabs : |s.q r| ≤ 1 := by
    rw [abs_of_nonneg hqlo]
    exact hqhi
  have hdiff : |z.2 - s.q r| ≤ 2 := by
    calc
      |z.2 - s.q r| = |z.2 + (-(s.q r))| := by rw [sub_eq_add_neg]
      _ ≤ |z.2| + |-(s.q r)| := abs_add_le _ _
      _ = |z.2| + |s.q r| := by rw [abs_neg]
      _ ≤ 2 := by linarith
  have hsq : (z.2 - s.q r) ^ 2 ≤ 4 := by
    rw [← sq_abs]
    have habs : 0 ≤ |z.2 - s.q r| := abs_nonneg _
    nlinarith [sq_nonneg (|z.2 - s.q r| - 2)]
  have hquad : (z.2 - s.q r) ^ 2 / K ≤ δ := by
    apply (div_le_iff₀ hK).2
    have hmul : δ * K = 4 := by
      dsimp [K]
      field_simp [ne_of_gt hδ]
    rw [hmul]
    exact hsq
  linarith

end SpinGlass.Targets
