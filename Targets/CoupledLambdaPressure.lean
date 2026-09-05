/-
# The lambda comparison for the abstract SK pressure

This averages the deterministic Section 5 construction over the actual SK
disorder. Integrability is proved from the lambda stability bound. The result
does not yet supply the second interpolation or the parameter variation needed
to improve the bound to Theorem 2.4.
-/
import Targets.CoupledLambda
import Targets.CoupledOuterExpectation

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}

/-- Pressure of the actual unrestricted lambda-interacting cascade. -/
noncomputable def lambdaCoupledPhi (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (d : ℕ) (t ℓ : ℝ) : ℝ :=
  (1 / n) * ∫ ω, coupledCascade n s β d (lambdaCoupledBase n (U ω) h t ℓ) (k + 2) 0 0 ∂ℙ

theorem measurable_lambdaCoupledBase_joint (h t ℓ : ℝ) :
    Measurable (fun p : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      lambdaCoupledBase n p.1 h t ℓ p.2.1 p.2.2) := by
  unfold lambdaCoupledBase guerraH
  fun_prop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurable_lambdaCoupledCascade_top (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t ℓ : ℝ) (d : ℕ) :
    Measurable (fun ω =>
      coupledCascade n s β d (lambdaCoupledBase n (sk.U ω) h t ℓ) (k + 2) 0 0) := by
  have H := measurable_coupledCascade_joint s β d (k + 2)
    (A := fun U => lambdaCoupledBase n U h t ℓ) (measurable_lambdaCoupledBase_joint h t ℓ)
  exact H.comp (f := fun ω => (sk.U ω, ((0 : Fin n → ℝ), (0 : Fin n → ℝ))))
    (sk.hU.repr_measurable.prodMk (measurable_const.prodMk measurable_const))

theorem integrable_lambdaCoupledCascade_top (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ℓ : ℝ) (d : ℕ) :
    Integrable (fun ω =>
      coupledCascade n s β d (lambdaCoupledBase n (sk.U ω) h t ℓ) (k + 2) 0 0) ℙ := by
  have hi := (integrable_coupledCascade_top sk s ht d).norm.add (integrable_const (n * |ℓ|))
  refine hi.mono' (measurable_lambdaCoupledCascade_top sk s t ℓ d).aestronglyMeasurable ?_
  filter_upwards with ω
  have H := lambdaCoupledCascade_dist_le s β (sk.U ω) h ℓ 0 ht d (k + 2) 0 0
  simp only [lambdaCoupledBase_zero_fun, sub_zero] at H
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have ha := abs_add_le
    (coupledCascade n s β d (lambdaCoupledBase n (sk.U ω) h t ℓ) (k + 2) 0 0 -
      coupledCascade n s β d (coupledBase n (sk.U ω) h t) (k + 2) 0 0)
    (coupledCascade n s β d (coupledBase n (sk.U ω) h t) (k + 2) 0 0)
  rw [sub_add_cancel] at ha
  linarith

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- At zero coupling this is the unrestricted pressure of Lemma 2.7. -/
theorem lambdaCoupledPhi_zero (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (d : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    lambdaCoupledPhi n s β h U d t 0 = 2 * guerraPhi n s β h U t := by
  simpa only [lambdaCoupledPhi, lambdaCoupledBase_zero_fun, coupledPhi] using
    coupledPhi_eq_two_guerraPhi n s β h U d ht

/-- The Section 5 overlap penalty holds after all Gaussian and disorder averages. -/
theorem constrainedPhi_le_lambdaCoupledPhi (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (u ℓ : ℝ) (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    constrainedPhi n s β h sk.U d t u ≤ lambdaCoupledPhi n s β h sk.U d t ℓ - ℓ * u := by
  have hi := integrable_lambdaCoupledCascade_top sk s ht ℓ d
  have H := integral_mono (integrable_constrainedCascade_top sk s hn ht u hu d hd)
    ((integrable_const (-ℓ * n * u)).add hi)
    (fun ω => constrainedCascade_le_lambda hn s β (sk.U ω) h u ℓ ht hu d (k + 2) 0 0)
  simp only [Pi.add_apply] at H
  rw [integral_add (integrable_const _) hi] at H
  simp only [integral_const, probReal_univ, one_smul] at H
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have H' := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ (1 / (n : ℝ)))
  unfold constrainedPhi lambdaCoupledPhi
  calc
    _ ≤ (1 / (n : ℝ)) * (-ℓ * n * u + ∫ ω,
        coupledCascade n s β d (lambdaCoupledBase n (sk.U ω) h t ℓ) (k + 2) 0 0 ∂ℙ) := H'
    _ = _ := by field_simp; ring

/-- After normalization the lambda Lipschitz constant is one, independent of N and t. -/
theorem lambdaCoupledPhi_dist_le (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ℓ μ : ℝ) (d : ℕ) :
    |lambdaCoupledPhi n s β h sk.U d t ℓ - lambdaCoupledPhi n s β h sk.U d t μ| ≤ |ℓ - μ| := by
  have hi := (integrable_lambdaCoupledCascade_top sk s ht ℓ d).sub
    (integrable_lambdaCoupledCascade_top sk s ht μ d)
  have H := (norm_integral_le_integral_norm _).trans
    (integral_mono hi.norm (integrable_const (n * |ℓ - μ|)) (fun ω => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using!
        lambdaCoupledCascade_dist_le s β (sk.U ω) h ℓ μ ht d (k + 2) 0 0))
  simp only [Pi.sub_apply] at H
  rw [integral_sub (integrable_lambdaCoupledCascade_top sk s ht ℓ d)
    (integrable_lambdaCoupledCascade_top sk s ht μ d)] at H
  simp only [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at H
  unfold lambdaCoupledPhi
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (n : ℝ)))]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  calc
    _ ≤ (1 / (n : ℝ)) * (n * |ℓ - μ|) := mul_le_mul_of_nonneg_left H (by positivity)
    _ = |ℓ - μ| := by field_simp

end SpinGlass.Targets
