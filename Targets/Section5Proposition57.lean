import Targets.Section5NegativeInitialAssembly
import Targets.Section5NegativeTerminal
import Targets.Section5PositiveTerminal
import Targets.Section5OutsideBound
import Targets.Section5ZeroInitialNegative
import Targets.Section5Smallness
import Targets.Section5TimeZero

/-!
# Proposition 5.7 for the reduced schemes in Talagrand's argument

All outside-neighbor overlaps are included: both signs, every breakpoint,
the final trial interval, zero first overlap and physical time zero. The
positive deficit is chosen before the system size and Gaussian disorder.
The final theorem chooses the Section 5 near-optimality tolerance before
the scheme, retaining the original fixed-level minimality hypothesis.

This is a pointwise-in-time-and-overlap strict bound. The compact uniform
quadratic estimate in Theorem 2.4 is a separate remaining obligation.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Adjacent strict mass gaps of a reduced scheme give the finite strict
monotonicity used by the interleaved comparison. -/
theorem RSBScheme.strictMono_mass_of_adjacent (s : RSBScheme k)
    (hm : ∀ p, p ≤ k → s.m p < s.m (p + 1)) :
    StrictMono (fun p : Fin (k + 2) => s.m p) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro p
  exact hm p (by omega)

private theorem negative_first_positive_gap
    (s : RSBScheme k) (β h ε : ℝ) {t t₀ u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (htt₀ : t ≤ t₀) (ht₀ : t₀ < 1)
    (hm : s.m 0 < s.m 1) (hq1 : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (huneg : u < 0) (hutop : |u| ≤ 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  by_cases hu1 : |u| ≤ s.q 1
  · apply exists_constrainedPhi_initial_signed_gap s β h ε hβ hm hright
      ⟨ht.1.le, htt₀⟩ ht₀ (u := u) _ hmin hnear hsmall
    rw [abs_of_neg huneg] at hu1
    exact ⟨by linarith, huneg⟩
  · have hq : s.q 1 < s.q 2 := hright.resolve_right (by
      intro he
      exact hu1 (by simpa only [he] using hutop))
    exact exists_constrainedPhi_gap_negative_first_beyond s β h hβ ht
      (by simpa only [s.m_zero] using hm) hq1 hq huneg (lt_of_not_ge hu1) hutop

private theorem negative_first_zero_gap
    (s : RSBScheme k) (β h ε : ℝ) {t t₀ u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (htt₀ : t ≤ t₀) (ht₀ : t₀ < 1)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : s.q 1 = 0) (hq2 : 0 < s.q 2) (huneg : u < 0) (hutop : |u| ≤ 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  have hm : s.m 0 < s.m 1 := hmass 0 (Nat.zero_le k)
  have habs : |u| = -u := abs_of_neg huneg
  by_cases hu2 : |u| ≤ s.q 2
  · obtain ⟨δ, hδ, H⟩ := exists_constrainedPhi_negative_initial_zero_neighbor
      (Ω := Ω) s β h ε hβ hq hm hq2 ht₀ ⟨ht.1.le, htt₀⟩
        ⟨by rw [habs] at hu2; linarith, huneg⟩ hmin hnear hsmall
    refine ⟨δ, hδ, ?_⟩
    intro n hn sk hatt
    obtain ⟨σ, τ, hστ⟩ := hatt
    exact H hn sk ⟨⟨(σ, τ), hστ⟩⟩
  · have hqgap : s.q 1 < s.q (1 + 1) := by simpa only [hq] using hq2
    obtain ⟨δ, hδ, H⟩ := exists_constrainedPhi_gap_right_outside_full
      (Ω := Ω) s β h (r := 1) (u := -u) hβ ht le_rfl (by omega)
        (by simpa only [habs] using lt_of_not_ge hu2)
        (by simpa only [habs] using hutop) (s.strictMono_mass_of_adjacent hmass) hqgap
    refine ⟨δ, hδ, ?_⟩
    intro n hn sk hatt
    obtain ⟨σ, τ, hστ⟩ := hatt
    letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
    obtain ⟨p⟩ := constrainedPair_nonempty_neg (n := n) u
    rw [constrainedPhi_initial_zero_reflection_of_min s β h sk hβ hq hm hqgap hmin]
    simpa only [show k + 2 - 1 = k + 1 by omega] using H hn sk ⟨p.1.1, p.1.2, p.2⟩

/-- The complete outside-neighbor strict free-energy bound for reduced
schemes, under the two common quantitative Section 5 smallness conditions.
The deficit is uniform in system size and disorder, but not yet in `(t,u)`. -/
theorem exists_constrainedPhi_gap_outside_of_reduced_min
    (s : RSBScheme k) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (-1) 1) (hout : u < s.q (r - 1) ∨ s.q (r + 1) < u)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  have hm : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega)
  have hd := s.overlap_directions_of_strict hqstrict hr0 hr
  have hutop : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hqu : u ≠ s.q r := by
    intro he
    rcases hout with hl | hh
    · exact (not_lt_of_ge (s.q_mono' r (by omega) (r - 1) (by omega))) (he ▸ hl)
    · exact (not_lt_of_ge (s.q_mono' (r + 1) (by omega) r (by omega))) (he ▸ hh)
  by_cases htzero : t = 0
  · subst t
    refine ⟨(u - s.q r) ^ 2 / 2,
      div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hqu)) (by norm_num), ?_⟩
    intro n hn sk hatt
    exact constrainedPhi_time_zero_le_guerraPsi_of_min hn s β h sk.U hr0 hr hβ
      hm hd.1 hd.2 hmin hatt
  have htime : t ∈ Set.Ioo 0 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2.trans_lt ht₀⟩
  by_cases huneg : u < 0
  · by_cases hr1 : r = 1
    · subst r
      have hm1 : s.m 0 < s.m 1 := hmass 0 (Nat.zero_le k)
      have hright := (s.overlap_directions_of_strict hqstrict (r := 1) le_rfl (by omega)).2
      have H : ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
          (∃ σ τ : Config n, overlap n σ τ = u) →
          constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
        by_cases hqzero : s.q 1 = 0
        · have hq2 : 0 < s.q 2 := by rcases hright with H | H <;> linarith
          exact negative_first_zero_gap s β h ε hβ htime ht.2 ht₀ hmass hqzero hq2
            huneg hutop hmin hnear hfar
        · have hq1 : 0 < s.q 1 :=
            lt_of_le_of_ne (s.q_nonneg (p := 1) (by omega)) (Ne.symm hqzero)
          exact negative_first_positive_gap s β h ε hβ htime ht.2 ht₀ hm1 hq1 hright
            huneg hutop hmin hnear hsmall
      simpa only [show k + 2 - 1 = k + 1 by omega] using H
    · exact exists_constrainedPhi_gap_negative_all_trials s β h hβ htime (by omega) hr
        (by simpa only [s.m_zero] using hmass 0 (Nat.zero_le k))
        (hqstrict 1 le_rfl (by omega)) huneg hutop
  · have hu0 : 0 ≤ u := le_of_not_gt huneg
    rcases hout with hl | hh
    · have hq : s.q (r - 1) < s.q r := hd.1.resolve_right (by
        intro he
        have H := s.q_mono' r (by omega) (r - 1) (by omega)
        rw [he] at H
        linarith)
      exact exists_constrainedPhi_gap_left_outside s β h hβ htime hr0 hr hu0 hl
        (s.strictMono_mass_of_adjacent hmass) hq
    · have hq : s.q r < s.q (r + 1) := hd.2.resolve_right (by
        intro he
        have H := s.q_mono' (r + 1) (by omega) r (by omega)
        rw [he] at H
        linarith [hu.2])
      exact exists_constrainedPhi_gap_right_outside_full s β h hβ htime hr0 hr hh hu.2
        (s.strictMono_mass_of_adjacent hmass) hq

/-- Proposition 5.7 in the exact-covariance SK setting used by the main
argument: a common positive accuracy is chosen before all reduced minimizing
schemes, and each outside-neighbor point has a positive size-independent gap.
No remaining interpolation, boundary, or signed estimate is assumed. -/
theorem talagrand_proposition_5_7 (β h : ℝ) (hβ : β ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ r, 1 ≤ r → r ≤ k + 1 → ∀ t ∈ Set.Icc 0 t₀,
      ∀ u ∈ Set.Icc (-1) 1, (u < s.q (r - 1) ∨ s.q (r + 1) < u) →
      ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  obtain ⟨ε, hε, hsmall, hfar⟩ := exists_section5_common_accuracy β hβ ht₀
  exact ⟨ε, hε, fun s hm hq hnear hmin _ hr0 hr _ ht _ hu hout =>
    exists_constrainedPhi_gap_outside_of_reduced_min s β h ε hβ hm hq hr0 hr ht ht₀ hu hout
      hmin hnear hsmall hfar⟩

end SpinGlass.Targets
