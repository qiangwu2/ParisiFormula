import Targets.Section5OffDiagonalAlgebra
import Targets.Section5CompactWitness

/-!
# Compact endpoint crossing with an off-diagonal mismatch

An off-diagonal covariance estimate may compare a constrained overlap `u` with
a trial endpoint `v`.  This adapter makes the topological step explicit: a
strict continuous scalar deficit at `u = v`, together with a quadratic
`C * (u-v)^2` mismatch loss, gives one uniform additive gap on a small closed
rectangle around that endpoint.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

theorem exists_uniform_gap_on_off_diagonal_crossing_rectangle
    {F B D : ℝ × ℝ → ℝ} {v t₀ C : ℝ}
    (ht₀ : 0 ≤ t₀) (hC : 0 ≤ C)
    (hcont : ContinuousOn D
      (Icc (0 : ℝ) t₀ ×ˢ Icc (v - 1) (v + 1)))
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) t₀, 0 < D (t, v))
    (hbound : ∀ z ∈ Icc (0 : ℝ) t₀ ×ˢ Icc (v - 1) (v + 1),
      F z ≤ B z - D z + C * (z.2 - v) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ z ∈ Icc (0 : ℝ) t₀ ×ˢ Icc (v - 1) (v + 1),
      |z.2 - v| ≤ ρ → F z ≤ B z - δ := by
  let R : Set (ℝ × ℝ) := Icc (0 : ℝ) t₀ ×ˢ Icc (v - 1) (v + 1)
  let E : Set (ℝ × ℝ) := Icc (0 : ℝ) t₀ ×ˢ ({v} : Set ℝ)
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hE : IsCompact E := isCompact_Icc.prod isCompact_singleton
  have hER : E ⊆ R := by
    intro z hz
    constructor
    · exact hz.1
    · rcases hz.2 with rfl
      constructor <;> linarith
  have hcontE : ContinuousOn D E := hcont.mono hER
  obtain ⟨d₀, hd₀, hD₀⟩ := exists_uniform_positive_of_compact_witnesses hE
    (fun (_ : Unit) z => D z)
    (fun _ => hcontE)
    (fun z hz => by
      refine ⟨(), ?_⟩
      rcases hz with ⟨hzt, hzv⟩
      rcases hzv with rfl
      exact hendpoint z.1 hzt)
  have hUC : UniformContinuousOn D R :=
    hR.uniformContinuousOn_of_continuous hcont
  obtain ⟨γ, hγ, hγD⟩ := (Metric.uniformContinuousOn_iff.mp hUC)
    (d₀ / 2) (by positivity)
  let ρ : ℝ := min 1 (min (γ / 2) (d₀ / (4 * (C + 1))))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    refine lt_min (by norm_num) (lt_min (by positivity) ?_)
    exact div_pos hd₀ (by positivity)
  have hρle1 : ρ ≤ 1 := min_le_left _ _
  have hρleγ : ρ ≤ γ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρleD : ρ ≤ d₀ / (4 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, d₀ / 4, by positivity, ?_⟩
  intro z hz hzu
  have hzR : z ∈ R := hz
  have hzE : (z.1, v) ∈ E := ⟨hz.1, by simp⟩
  have hdist : dist (z.1, v) z < γ := by
    rw [Prod.dist_eq]
    refine max_lt (by simp [hγ]) ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt hzu (lt_of_le_of_lt hρleγ (half_lt_self hγ))
  have hDclose := hγD (z.1, v) (hER hzE) z hzR hdist
  have hDclose' : |D (z.1, v) - D z| < d₀ / 2 := by
    simpa only [Real.dist_eq] using hDclose
  have hDendpoint : d₀ ≤ D (z.1, v) := by
    obtain ⟨_, ht⟩ := hz.1
    exact hD₀ (z.1, v) ⟨hz.1, by simp⟩ |>.choose_spec
  have hDgap : d₀ / 2 < D z := by
    have h := abs_lt.mp hDclose'
    linarith
  have hCρ : C * (z.2 - v) ^ 2 ≤ d₀ / 4 := by
    have hdiff : |z.2 - v| ≤ ρ := hzu
    have hsq : (z.2 - v) ^ 2 ≤ ρ := by
      rw [← sq_abs]
      have hρnon : 0 ≤ ρ := hρ.le
      have habsnon : 0 ≤ |z.2 - v| := abs_nonneg _
      have hmul := mul_self_le_mul_self habsnon hdiff
      have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
      nlinarith
    have hCρ' : C * ρ ≤ d₀ / 4 := by
      have hden : 0 < C + 1 := by linarith
      have hmul : C * ρ ≤ C * (d₀ / (4 * (C + 1))) :=
        mul_le_mul_of_nonneg_left hρleD hC
      have hfrac : C * (d₀ / (4 * (C + 1))) ≤ d₀ / 4 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
        have hfrac' : C * d₀ / (C + 1) ≤ d₀ := by
          apply (div_le_iff₀ hden).2
          nlinarith
        calc
          C * (d₀ / (4 * (C + 1))) * 4 = C * d₀ / (C + 1) := by field_simp
          _ ≤ d₀ := hfrac'
      exact hmul.trans hfrac
    calc
      C * (z.2 - v) ^ 2 ≤ C * ρ :=
        mul_le_mul_of_nonneg_left hsq hC
      _ ≤ d₀ / 4 := hCρ'
  have H := hbound z hz
  linarith

end SpinGlass.Targets
