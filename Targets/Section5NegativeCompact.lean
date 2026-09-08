import Targets.Section5InterleavedCompact
import Targets.Section5InterleavedNegative
import Targets.Section5TerminalPadding

/-!
# Compact negative-overlap bounds away from physical time zero

The signed interleaved scalar comparison is continuous on each trial strip.
On a compact set with time bounded below by a positive number, its checked
strict negative endpoint supplies a fixed zero-lambda witness.  This is the
compact component needed for the negative-overlap assembly; the separate
physical-time-zero neighborhood is intentionally not hidden here.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A compact negative trial region with positive physical time has one
size-independent strict deficit.  The theorem is stated for the actual
trial range, so it does not assume continuity of the constrained free energy
or of the attainable-overlap set. -/
theorem exists_uniform_constrainedPhi_negative_compact
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr : 2 ≤ r) (hrk : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2)
    {η t₀ : ℝ} (hη : 0 < η) (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc η t₀)
    (huneg : ∀ z ∈ S, z.2 < 0)
    (hu : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hpos : ∀ z ∈ S, ∃ ℓ : ℝ,
      0 < section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ := by
    intro z hz
    have htime : z.1 ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_lt_of_le hη (ht z hz).1,
        (ht z hz).2.trans_lt ht₀⟩
    have H := section5InterleavedScalarV_zero_lt_negative s β h hβ htime hr
      hj0 hj hm hq (huneg z hz) (hu z hz)
    refine ⟨0, ?_⟩
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    exact sub_pos.mpr H
  exact exists_uniform_constrainedPhi_gap_on_compact_trial (Ω := Ω) s β h
    (by omega) hrk hj0 hj hS
    (fun z hz => ⟨by linarith [(ht z hz).1], by linarith [(ht z hz).2]⟩) hu hpos

/-- The same compact argument after terminal padding, where the final trial
interval has index `k+2` and the original constrained free energy is recovered
by exact padding identities. -/
theorem exists_uniform_constrainedPhi_negative_terminal_compact_padded
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr : 2 ≤ r) (hrk : r ≤ k + 1)
    (hm : 0 < s.m 1) (hq : s.q 1 < s.q 2)
    {η t₀ : ℝ} (hη : 0 < η) (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc η t₀)
    (huneg : ∀ z ∈ S, z.2 < 0)
    (hu : ∀ z ∈ S, |z.2| ∈ Ioc (s.q (k + 1)) 1) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let sp := s.padOneLast
  have hspq (p : ℕ) (hp : p ≤ k + 2) : sp.q p = s.q p := s.padOneLast_q hp
  have htrial : ∀ z ∈ S, |z.2| ∈ Icc (sp.q ((k + 2) - 1)) (sp.q (k + 2)) := by
    intro z hz
    rw [show (k + 2) - 1 = k + 1 by omega,
      hspq (k + 1) (by omega), hspq (k + 2) (by omega), s.q_top]
    exact ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hpos : ∀ z ∈ S, ∃ ℓ : ℝ,
      0 < section5InterleavedLambdaDeficit sp β h r (k + 2) z.1 z.2 ℓ := by
    intro z hz
    have htime : z.1 ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_lt_of_le hη (ht z hz).1,
        (ht z hz).2.trans_lt ht₀⟩
    have hspm : 0 < sp.m 1 := by
      change 0 < s.padOneLast.m 1
      simpa only [s.padOneLast_m (p := 1) (by omega)] using hm
    have hspqgap : sp.q 1 < sp.q 2 := by
      simpa only [sp, s.padOneLast_q (p := 1) (by omega),
        s.padOneLast_q (p := 2) (by omega)] using hq
    have H := section5InterleavedScalarV_zero_lt_negative sp β h hβ htime hr
      (by omega) (by omega) hspm hspqgap (huneg z hz) (htrial z hz)
    refine ⟨0, ?_⟩
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    exact sub_pos.mpr H
  obtain ⟨δ, hδ, H⟩ := exists_uniform_constrainedPhi_gap_on_compact_trial (Ω := Ω)
    sp β h (by omega) (by omega) (by omega) (by omega) hS
    (fun z hz => ⟨le_trans (le_of_lt hη) (ht z hz).1,
      le_trans (ht z hz).2 ht₀.le⟩) htrial hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  have Hp := H z hz hn sk hatt
  simpa only [show (k + 1) + 2 - r = (k + 2 - r) + 1 by omega,
    sp, constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hp

end SpinGlass.Targets
