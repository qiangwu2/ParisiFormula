import Targets.Section5OutsideIntervals
import Targets.Section5InterleavedBound

/-!
# Actual outside-neighbor free-energy gaps without trial-index assumptions

First-crossing selection supplies the trial index and positive witness
variances, including exact breakpoint overlaps. The resulting positive
deficit is fixed before the system size and disorder. These statements
retain the actual relevant physical overlap gap, strictly ordered masses,
positive interpolation time, and the present trial range through `q_(k+1)`.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Genuine left outside-neighbor improvement, including all nonnegative
breakpoint overlaps, with no supplied trial index or witness variances. -/
theorem exists_constrainedPhi_gap_left_outside
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hu0 : 0 ≤ u) (hu : u < s.q (r - 1))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q (r - 1) < s.q r) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  obtain ⟨j, hj0, hjr, _, huj, hju⟩ :=
    section5OutsideLeft_exists_interval s hr0 hr hu0 hu
  have habs : |u| = u := abs_of_nonneg hu0
  have huI : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j) := by
    rw [habs]
    exact ⟨huj, hju.le⟩
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hbv : 0 < t * (β ^ 2 * (s.q j - |u|)) := by
    rw [habs]
    exact mul_pos ht.1 (mul_pos hβsq (sub_pos.mpr hju))
  have hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1))) :=
    mul_pos (sub_pos.mpr ht.2) (mul_pos hβsq (sub_pos.mpr hq))
  obtain ⟨δ, hδ, _, hbound⟩ := exists_constrainedPhi_interleaved_gap_left_outside
    (Ω := Ω) s β h ⟨ht.1.le, ht.2.le⟩ hr hj0 hjr huI hm hbv hcv
  exact ⟨δ, hδ, hbound⟩

/-- Genuine right outside-neighbor improvement up to `q_(k+1)`, including
every upper trial breakpoint, with no supplied trial-index hypotheses. -/
theorem exists_constrainedPhi_gap_right_outside
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hu : s.q (r + 1) < u) (hutop : u ≤ s.q (k + 1))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q r < s.q (r + 1)) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  obtain ⟨j, _, hrj, hj, hju, huj⟩ :=
    section5OutsideRight_exists_interval s hr hu hutop
  have hu0 : 0 ≤ u := by
    have hq0 := s.q_mono' (r + 1) (by omega) 0 (Nat.zero_le _)
    rw [s.q_zero] at hq0
    exact (hq0.trans_lt hu).le
  have habs : |u| = u := abs_of_nonneg hu0
  have huI : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j) := by
    rw [habs]
    exact ⟨hju.le, huj⟩
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    mul_pos (sub_pos.mpr ht.2) (mul_pos hβsq (sub_pos.mpr hq))
  have hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1))) := by
    rw [habs]
    exact mul_pos ht.1 (mul_pos hβsq (sub_pos.mpr hju))
  obtain ⟨δ, hδ, _, hbound⟩ := exists_constrainedPhi_interleaved_gap_right_outside
    (Ω := Ω) s β h ⟨ht.1.le, ht.2.le⟩ hr0 hj hrj huI hm hbv hcv
  exact ⟨δ, hδ, hbound⟩

end SpinGlass.Targets
