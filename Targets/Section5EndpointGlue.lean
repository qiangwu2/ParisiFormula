import Targets.Section5AdjacentCompact

/-!
# Right-endpoint gluing on one closed trial band

For compact covers it is useful to assign a common breakpoint to the next
trial interval.  This keeps the band closed while avoiding an open endpoint;
continuity follows from the exact adjacent scalar identity.
-/

open MeasureTheory ProbabilityTheory Real Set Topology

namespace SpinGlass.Targets

noncomputable def section5InterleavedLambdaDeficit_rightEndpointGlue {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ} (ℓ : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 < s.q j then
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ
  else
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ

set_option maxHeartbeats 10000000 in
theorem continuousOn_section5InterleavedLambdaDeficit_rightEndpointGlue
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ}
    (hj : j + 1 ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (section5InterleavedLambdaDeficit_rightEndpointGlue
      (j := j) s β h r ℓ)
      {z : ℝ × ℝ | z.2 ∈ Icc (s.q (j - 1)) (s.q j)} := by
  let S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ∈ Icc (s.q (j - 1)) (s.q j)}
  let p : (ℝ × ℝ) → Prop := fun z => z.2 < s.q j
  let f : (ℝ × ℝ) → ℝ := fun z =>
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ
  let g : (ℝ × ℝ) → ℝ := fun z =>
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ
  have hclosed : IsClosed {z : ℝ × ℝ | ¬ p z} := by
    dsimp [p]
    simpa only [not_lt] using
      (isClosed_le (continuous_const : Continuous (fun _ : ℝ × ℝ => s.q j)) continuous_snd)
  have hf : ContinuousOn f (S ∩ closure {z | p z}) := by
    apply (continuousOn_section5InterleavedLambdaDeficit_trial s β h r
      (j := j) (by omega) ℓ).mono
    intro z hz
    have hle : z.2 ≤ s.q j := by
      exact closure_lt_subset_le continuous_snd continuous_const hz.2
    have hnon : 0 ≤ z.2 :=
      (s.q_nonneg (p := j - 1) (by omega)).trans hz.1.1
    change |z.2| ∈ Icc (s.q (j - 1)) (s.q j)
    rw [abs_of_nonneg hnon]
    exact ⟨hz.1.1, hle⟩
  have hg : ContinuousOn g (S ∩ closure {z | ¬ p z}) := by
    apply (continuousOn_section5InterleavedLambdaDeficit_trial s β h r
      (j := j + 1) (by omega) ℓ).mono
    intro z hz
    have hge : s.q j ≤ z.2 := by
      have hclosed' : IsClosed {z : ℝ × ℝ | s.q j ≤ z.2} :=
        isClosed_le continuous_const continuous_snd
      have hmem : z ∈ {z : ℝ × ℝ | s.q j ≤ z.2} :=
        hclosed'.closure_subset (by simpa [p, not_lt] using hz.2)
      exact hmem
    have hnon : 0 ≤ z.2 :=
      (s.q_nonneg (p := j - 1) (by omega)).trans hz.1.1
    change |z.2| ∈ Icc (s.q ((j + 1) - 1)) (s.q (j + 1))
    rw [abs_of_nonneg hnon]
    exact ⟨hge, by
      calc
        z.2 ≤ s.q j := hz.1.2
        _ ≤ s.q (j + 1) := s.q_mono' (j + 1) (by omega) j (by omega)⟩
  have hboundary : ∀ z ∈ S ∩ frontier {z | p z}, f z = g z := by
    intro z hz
    have heq : z.2 = s.q j := by
      exact frontier_lt_subset_eq continuous_snd continuous_const hz.2
    dsimp [f, g]
    rw [heq]
    exact section5InterleavedLambdaDeficit_adjacent_boundary s β h r
      (j := j) hj z.1 ℓ
  have H := ContinuousOn.if (s := S) (p := p) (f := f) (g := g)
    hboundary hf hg
  change ContinuousOn (fun z => if p z then f z else g z) S at H
  change ContinuousOn (fun z => if z.2 < s.q j then
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ else
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ) S
  exact H

end SpinGlass.Targets
