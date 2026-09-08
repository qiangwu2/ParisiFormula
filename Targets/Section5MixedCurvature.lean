import Targets.Section5MixedCascade
import Targets.Section5InterleavedScalarCore
import Targets.CoupledLambdaCurvature

/-!
# Lambda curvature for the genuine mixed scalar cascade

The mixed recursion used by the interleaved comparison has the same sharp
`E ≤ 1 - D²` invariant as the ordinary split cascade.  This file supplies
the second-derivative recursion and its induction; it is independent of any
strict-order argument and remains valid when masses or variances vanish.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]

noncomputable def mixedScalarCascadeDD (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) : ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ l x => GTFrame.fLbaseDD l x
  | j + 1 => match mode j with
    | .independent =>
      GTFrame.finiteStepDD (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j))
        (GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j)
          (mixedScalarCascadeD mode m v j))
        (GTFrame.finiteStepDD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j)
          (mixedScalarCascadeD mode m v j) (mixedScalarCascadeDD mode m v j))
    | .shared =>
      GTFrame.finiteStepDD (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p))
        (mixedScalarCascade mode m v j) (mixedScalarCascadeD mode m v j)
        (mixedScalarCascadeDD mode m v j)
    | .opposite =>
      GTFrame.finiteStepDD (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => -Real.sqrt (v j p))
        (mixedScalarCascade mode m v j) (mixedScalarCascadeD mode m v j)
        (mixedScalarCascadeDD mode m v j)

theorem mixedScalarCascade_unitCurvature
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, m j ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) :
    UnitLambdaCurvature (mixedScalarCascade mode m v j)
      (mixedScalarCascadeD mode m v j) (mixedScalarCascadeDD mode m v j) := by
  induction j with
  | zero => exact unitLambdaCurvature_terminal
  | succ j ih =>
    simp only [mixedScalarCascade, mixedScalarCascadeD, mixedScalarCascadeDD]
    cases mode j with
    | independent =>
      have hi := ih.finiteStep (GTFrame.expMoments_gaussianReal 0 1) (hm j)
        (continuous_const : Continuous (fun _ : P => (0 : ℝ))) (hv j).sqrt
      exact hi.finiteStep (GTFrame.expMoments_gaussianReal 0 1) (hm j)
        (hv j).sqrt (continuous_const : Continuous (fun _ : P => (0 : ℝ)))
    | shared =>
      exact ih.finiteStep (GTFrame.expMoments_gaussianReal 0 1) (hm j)
        (hv j).sqrt (hv j).sqrt
    | opposite =>
      exact ih.finiteStep (GTFrame.expMoments_gaussianReal 0 1) (hm j)
        (hv j).sqrt (hv j).sqrt.neg

theorem hasDerivAt_mixedScalarCascade_lambda
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, m j ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun z => mixedScalarCascade mode m v j p z x)
      (mixedScalarCascadeD mode m v j p l x) l :=
  (mixedScalarCascade_unitCurvature mode m v hm hv j).triple.good.hasDeriv p l x

/- The curvature invariant gives the same optimized lambda square gain for the
actual interleaved scalar family.  In particular, this remains available at a
physical-neighbor endpoint where the order-obstruction variance is zero. -/
theorem section5InterleavedScalarV_lambda_gain
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r j : ℕ)
    (hj : j ≤ k + 1) (t u₀ u : ℝ) :
    ∃ l : ℝ, section5InterleavedScalarV s β h r j t u₀ l - l * u ≤
      section5InterleavedScalarV s β h r j t u₀ 0 -
        (deriv (section5InterleavedScalarV s β h r j t u₀) 0 - u) ^ 2 / 2 := by
  let mode := section5ReverseMode s r j (decide (u₀ < 0))
  let mass := section5ReverseMass s r j
  let variance := fun i (_ : Unit) => section5ReverseVariance s β t |u₀| r j i
  let N := (k + 2) + (k + 3)
  let f := section5InterleavedScalarV s β h r j t u₀
  let D := fun l => mixedScalarCascadeD mode mass variance N () l (h,h)
  have hmass : ∀ i, mass i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact section5TaggedMass_mem_Icc s r hj (section5ReverseTag s r j i)
  have hcurv := mixedScalarCascade_unitCurvature mode mass variance hmass
    (fun _ => continuous_const) N
  have hdef : ∀ l, f l = mixedScalarCascade mode mass variance N () l (h,h) := by
    intro l
    rfl
  have hd (l : ℝ) : HasDerivAt f (D l) l := by
    change HasDerivAt (fun z => mixedScalarCascade mode mass variance N () z (h,h))
      (mixedScalarCascadeD mode mass variance N () l (h,h)) l
    exact hcurv.triple.good.hasDeriv () l (h,h)
  have hderiv : deriv f = D := by
    funext l
    exact (hd l).deriv
  have hD (l : ℝ) : HasDerivAt D
      (mixedScalarCascadeDD mode mass variance N () l (h,h)) l := by
    change HasDerivAt
      (fun z => mixedScalarCascadeD mode mass variance N () z (h,h))
      (mixedScalarCascadeDD mode mass variance N () l (h,h)) l
    exact hcurv.triple.derivD () l (h,h)
  have hsecond (l : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) l) l := by
    rw [hderiv, (hD l).deriv]
    exact hD l
  have hbound (l : ℝ) : deriv (deriv f) l ≤ 1 := by
    rw [hderiv, (hD l).deriv]
    exact (hcurv.sharp () l (h,h)).trans (sub_le_self _ (sq_nonneg _))
  have hfirst (l : ℝ) : HasDerivAt f (deriv f l) l := by
    rw [hderiv]
    exact hd l
  have H := quadratic_upper_of_second_le_one
    hfirst hsecond hbound (u - deriv f 0)
  refine ⟨u - deriv f 0, ?_⟩
  change f (u - deriv f 0) - (u - deriv f 0) * u ≤
    f 0 - (deriv f 0 - u) ^ 2 / 2
  nlinarith

end SpinGlass.Targets
