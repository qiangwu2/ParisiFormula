import Targets.Section5AdjacentCompact
import Targets.Section5InterleavedStrict

/-!
# Physical-neighbor endpoint glue

The adjacent-band argument already handles nonphysical breakpoints.  At a
physical breakpoint `q (r-1)`, the outside trial is the left trial while the
same physical level is represented by the next trial.  This file isolates
that one missing endpoint input: once scalar positivity is supplied at the
physical boundary, the existing continuous gluing and compactness argument
gives the uniform finite-size gap on the whole closed neighboring band.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A closed left physical-neighbor band is uniformly strict provided the
scalar endpoint at `q_(r-1)` has a positive witness.  Away from that endpoint
the witness is the already proved outside-neighbor obstruction; at time zero
the minimizing-scheme lambda gain handles every point.  The endpoint
hypothesis is deliberately explicit: it is the sole physical-neighbor input
not established by the current strict-order obstruction.
-/
theorem exists_uniform_constrainedPhi_gap_on_left_physical_neighbor
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q (r - 1) < s.q r)
    (hqright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu0 : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (r - 2)) (s.q (r - 1)))
    (hboundary : ∀ z ∈ S, z.2 = s.q (r - 1) → ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue
        (j := r - 1) s β h r ℓ z) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hj0 : 1 ≤ r - 1 := by omega
  have hj : (r - 1) + 1 ≤ k + 1 := by omega
  have hmass : s.m (r - 1) < s.m r := by
    have hfin : (⟨r - 1, by omega⟩ : Fin (k + 2)) < ⟨r, by omega⟩ := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact hm hfin
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue
        (j := r - 1) s β h r ℓ z := by
    intro z hz
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
        s β h (r := r) (j := r - 1) (by omega) hr (by omega) hβ hmass
        (Or.inl hq) hqright hmin z.2
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
      have hle : z.2 ≤ s.q (r - 1) := by
        exact (hu z hz).2
      rw [if_pos hle, section5InterleavedLambdaDeficit, htzero]
      have hsq : 0 < (z.2 - s.q r) ^ 2 / 2 := by
        exact div_pos (sq_pos_of_ne_zero (by
          intro heq
          have hzq : z.2 = s.q r := sub_eq_zero.mp heq
          have : s.q r ≤ s.q (r - 1) := by simpa [hzq] using hle
          exact (not_le_of_gt hq) this)) (by norm_num)
      linarith [H]
    · have htpos : z.1 ∈ Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      by_cases huend : z.2 = s.q (r - 1)
      · exact hboundary z hz huend
      · have hle : z.2 < s.q (r - 1) := by
          exact lt_of_le_of_ne (hu z hz).2 huend
        have htrial : |z.2| ∈ Icc (s.q ((r - 1) - 1)) (s.q (r - 1)) := by
          rw [abs_of_nonneg (hu0 z hz)]
          exact ⟨(hu z hz).1, hle.le⟩
        have hbv : 0 < z.1 * (β ^ 2 * (s.q (r - 1) - |z.2|)) := by
          rw [abs_of_nonneg (hu0 z hz)]
          exact mul_pos htpos.1
            (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hle))
        have hcv : 0 < (1 - z.1) *
            (β ^ 2 * (s.q r - s.q (r - 1))) :=
          mul_pos (sub_pos.mpr htpos.2)
            (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq))
        have H := section5InterleavedScalarV_zero_lt_left_outside
          s β h (r := r) (j := r - 1) ⟨htpos.1.le, htpos.2.le⟩ hr hj0 (by omega)
          htrial hm hbv hcv
        refine ⟨0, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_pos hle.le, section5InterleavedLambdaDeficit]
        simpa only [zero_mul, add_zero] using (sub_pos.mpr H)
  apply exists_uniform_constrainedPhi_gap_on_adjacent_trial s β h
    (r := r) (j := r - 1) (by omega) hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    hu0 (fun z hz => by
      exact ⟨(hu z hz).1, (hu z hz).2.trans
        (by
          have hidx : r - 1 + 1 = r := by omega
          rw [hidx]
          exact hq.le)⟩) hpos

end SpinGlass.Targets
