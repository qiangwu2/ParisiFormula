import Targets.Section5FarRight

/-!
# The physical right-neighbor endpoint

At the endpoint `u = q_(r+1)`, the overlap still belongs to the closed
physical right interval `[q_r,q_(r+1)]`.  The right mass-or-lambda estimate
therefore gives a genuine size/disorder-uniform deficit whenever Talagrand's
usual quadratic smallness inequality is available.  This isolates the
endpoint from the one-sided outside-trial region, where the outside scalar
witness has a vanishing endpoint factor.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_constrainedPhi_gap_right_at_physical_neighbor
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmass : s.m (r - 1) < s.m r)
    (hq : s.q r < s.q (r + 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (s.q (r + 1) - s.q r) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = s.q (r + 1)) →
      constrainedPhi n s β h sk.U (k + 2 - r) t (s.q (r + 1)) ≤
        2 * guerraPsi s β h t - δ := by
  obtain ⟨δ, hδ, H⟩ := exists_constrainedPhi_right_gap_uniform_in_size (Ω := Ω)
    s β h ε hr0 hr hmass ht ⟨hq.le, le_rfl⟩ hmin hnear hsmall
  refine ⟨δ, hδ, ?_⟩
  intro n hn sk hatt
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n (s.q (r + 1))) := ⟨⟨(σ, τ), hστ⟩⟩
  exact H hn sk inferInstance

end SpinGlass.Targets
