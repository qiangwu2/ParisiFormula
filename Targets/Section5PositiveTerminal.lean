import Targets.Section5InterleavedMassPair
import Targets.Section5OutsideIntervals
import Targets.Section5TerminalPadding

/-!
# The complete positive right outside-neighbor range

Exact terminal padding makes the final trial interval available to the
existing interleaved construction. First-crossing selection includes trial
breakpoints. Strictness uses only a pair of original masses, never strict
mass monotonicity or minimality of the redundantly padded scheme. Both the
constrained free energy and the comparison function are transported back
exactly, with the deficit chosen before the system size and disorder.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Positive right outside-neighbor improvement over the full overlap range,
including the final interval and every breakpoint. No assumption is made
about optimality or strict masses of the padded scheme. -/
theorem exists_constrainedPhi_gap_right_outside_full
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hu : s.q (r + 1) < u) (hu1 : u ≤ 1)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q r < s.q (r + 1)) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  have hpU : s.padOneLast.q (r + 1) < u := by
    simpa only [s.padOneLast_q (p := r + 1) (by omega)] using hu
  have hpTop : u ≤ s.padOneLast.q (k + 1 + 1) := by
    simpa only [show k + 1 + 1 = k + 2 by omega,
      s.padOneLast_q (p := k + 2) le_rfl, s.q_top] using hu1
  obtain ⟨j, _, hrj, hj, hjU, huj⟩ :=
    section5OutsideRight_exists_interval s.padOneLast (by omega) hpU hpTop
  have hu0 : 0 ≤ u := by
    have hq0 := s.q_mono' (r + 1) (by omega) 0 (Nat.zero_le _)
    rw [s.q_zero] at hq0
    exact (hq0.trans_lt hu).le
  have habs : |u| = u := abs_of_nonneg hu0
  have hpI : |u| ∈ Set.Icc (s.padOneLast.q (j - 1)) (s.padOneLast.q j) := by
    rw [habs]
    exact ⟨hjU.le, huj⟩
  have hmass : s.padOneLast.m r < s.padOneLast.m (j - 1) := by
    rw [s.padOneLast_m hr, s.padOneLast_m (p := j - 1) (by omega)]
    exact hm (show (⟨r, by omega⟩ : Fin (k + 2)) < ⟨j - 1, by omega⟩ by
      change r < j - 1
      omega)
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hbv : 0 < (1 - t) *
      (β ^ 2 * (s.padOneLast.q (r + 1) - s.padOneLast.q r)) := by
    rw [s.padOneLast_q (p := r + 1) (by omega), s.padOneLast_q (p := r) (by omega)]
    exact mul_pos (sub_pos.mpr ht.2) (mul_pos hβsq (sub_pos.mpr hq))
  have hcv : 0 < t * (β ^ 2 * (|u| - s.padOneLast.q (j - 1))) := by
    rw [habs]
    exact mul_pos ht.1 (mul_pos hβsq (sub_pos.mpr hjU))
  obtain ⟨δ, hδ, _, hbound⟩ := exists_constrainedPhi_interleaved_gap_right_of_mass_lt
    (Ω := Ω) s.padOneLast β h ⟨ht.1.le, ht.2.le⟩ hr0 hj hrj hpI hmass hbv hcv
  refine ⟨δ, hδ, ?_⟩
  intro n hn sk hatt
  have H := hbound hn sk hatt
  simpa only [show k + 1 + 2 - r = (k + 2 - r) + 1 by omega,
    constrainedPhi_padOneLast, guerraPsi_padOneLast] using H

end SpinGlass.Targets
