import Targets.Section5PhysicalNeighborWitness
import Targets.Section5CompactTube
import Targets.Section5OffDiagonalCompact

/-!
# Left physical-neighbor crossing with an off-diagonal bound

At the physical endpoint `v = q_(r-1)`, the scalar witness supplied by the
minimizing scheme is uniformized in a compact time slice.  An off-diagonal
finite-volume estimate can then carry that endpoint witness to constrained
overlaps `u` near `v`; its mismatch loss is absorbed by shrinking the tube.
The off-diagonal finite-volume estimate is kept as an explicit hypothesis,
since the derivative API and the covariance algebra do not identify that
transport automatically.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_left_physical_neighbor_offDiagonal
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hoffdiag : ∀ {t u : ℝ}, t ∈ Icc (0 : ℝ) t₀ → u ∈ Icc (-1 : ℝ) 1 →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      ∀ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∀ ℓ : ℝ,
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t -
          section5LeftComparisonDeficit s β h r m ℓ
            (t, u) + C * (u - s.q (r - 1)) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      |u - s.q (r - 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let I : Type := {p : ℝ × ℝ // p.1 ∈ Icc (s.m (r - 1) / 2) (s.m r)}
  let f : I → (ℝ × ℝ) → ℝ := fun i z =>
    section5LeftComparisonDeficit s β h r i.1.1 i.1.2 z
  have hf : ∀ i : I, Continuous (f i) := by
    intro i
    have hm0 : 0 ≤ i.1.1 := by
      exact (div_nonneg (s.m_nonneg (p := r - 1) (by omega)) (by norm_num)).trans
        i.2.1
    have H := continuous_section5LeftComparisonDeficit s β h hr hm0 i.1.2
    exact H.comp (by fun_prop)
  have hpos : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ i : I, 0 < f i (t, s.q (r - 1)) := by
    intro t ht
    obtain ⟨m, hm, ℓ, hℓ⟩ := exists_section5LeftComparison_witness_at_physical_neighbor
      s β h ε hr0 hr hβ hmass hq hright ⟨ht.1, ht.2⟩ ht₀ hmin hnear hsmall hfar
    refine ⟨⟨(m, ℓ), hm⟩, ?_⟩
    simpa [f] using hℓ
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Icc (0 : ℝ) t₀)
      isCompact_Icc f hf (s.q (r - 1)) hpos
  let ρ : ℝ := min 1 (min ρ₀ (δ₀ / (4 * (C + 1))))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    refine lt_min (by norm_num) (lt_min hρ₀ ?_)
    exact div_pos hδ₀ (by positivity)
  have hρle1 : ρ ≤ 1 := min_le_left _ _
  have hρle0 : ρ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρleδ : ρ ≤ δ₀ / (4 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, δ₀ / 2, by positivity, ?_⟩
  intro t ht u hu htu n hn sk hatt
  obtain ⟨i, hi⟩ := Htube t ht u (htu.trans hρle0)
  have hm : i.1.1 ∈ Icc (s.m (r - 1) / 2) (s.m r) := i.2
  have H := hoffdiag ht hu hn sk hatt i.1.1 hm i.1.2
  have hsq : (u - s.q (r - 1)) ^ 2 ≤ ρ := by
    rw [← sq_abs]
    have hmul := mul_self_le_mul_self (abs_nonneg (u - s.q (r - 1))) htu
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
    nlinarith
  have hCρ : C * (u - s.q (r - 1)) ^ 2 ≤ δ₀ / 4 := by
    have hden : 0 < C + 1 := by linarith
    have hmul : C * ρ ≤ C * (δ₀ / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hρleδ hC
    have hfrac : C * (δ₀ / (4 * (C + 1))) ≤ δ₀ / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      have hfrac' : C * δ₀ / (C + 1) ≤ δ₀ := by
        apply (div_le_iff₀ hden).2
        nlinarith
      calc
        C * (δ₀ / (4 * (C + 1))) * 4 = C * δ₀ / (C + 1) := by field_simp
        _ ≤ δ₀ := hfrac'
    exact (mul_le_mul_of_nonneg_left hsq hC).trans (hmul.trans hfrac)
  have hscalar : δ₀ ≤ section5LeftComparisonDeficit s β h r i.1.1 i.1.2
      (t, u) := by
    simpa [f] using hi
  linarith

end SpinGlass.Targets
