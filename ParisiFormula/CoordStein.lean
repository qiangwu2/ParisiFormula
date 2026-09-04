/-
# Coordinate Stein identity for a Gaussian-Hilbert vector, from line derivatives

New work for the ParisiFormula project (not vendored).

For the SK disorder `U = ∑ᵢ cᵢ wᵢ` (RSAT's `IsGaussianHilbert`), Talagrand's (3.1) in the form
needed for the proof of Theorem 2.1 is

  `𝔼[cᵢ Φ(U)] = τᵢ 𝔼[(∂_{wᵢ}Φ)(U)]`,

where `∂_{wᵢ}Φ` is the derivative of `Φ` along the line `z + t·wᵢ`.  RSAT proves this for
Fréchet-`C¹` test functions of moderate growth (`stein_coord_with_param`).  The cascade
functional is only known to be differentiable *along lines*, with the derivative along `wᵢ`
supplied by the tilted chain rule, so this file re-derives the identity from that alone:

* the coordinate `cᵢ` is independent of the complementary coordinates
  (`indep_coord_complement`) and Gaussian of variance `τᵢ` (`c_gauss`);
* the law of the pair is the product (`map_pair_eq_prod_of_indep`), and integrability
  transports (`integrable_phi_on_mapY_prod_gauss`) — RSAT's helpers, which need no
  differentiability;
* Stein on the product along the second coordinate is `stein_prod_of_hasDerivAt`.

The degenerate case `τᵢ = 0` (which does occur: the SK covariance `(Nβ²/2)R²` has a kernel,
e.g. `U(σ) = U(-σ)`) is handled separately — then `cᵢ = 0` a.s. and both sides vanish.
-/
import ParisiFormula.GaussianStein
import Lemmas.SpinGlass.Gaussian_IBP_Hilbert

open MeasureTheory ProbabilityTheory Real
open PhysLean.Probability.GaussianIBP

open scoped NNReal InnerProductSpace

namespace SpinGlass

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- A zero-variance Gaussian coordinate vanishes almost surely. -/
theorem ae_eq_zero_of_map_eq_dirac {X : Ω → ℝ} (hX : Measurable X)
    (hlaw : Measure.map X (ℙ : Measure Ω) = Measure.dirac 0) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), X ω = 0 := by
  rw [ae_iff]
  have h : (ℙ : Measure Ω) {ω | ¬ X ω = 0} = Measure.map X ℙ ({0}ᶜ) := by
    rw [Measure.map_apply hX (measurableSet_singleton (0 : ℝ)).compl]
    rfl
  rw [h, hlaw, Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl]
  simp

/--
**Coordinate Stein identity from line derivatives.**  For `g` Gaussian-Hilbert with basis `w`,
coordinates `c` and variances `τ`, and `Φ, Φ'` with `Φ'` the derivative of `Φ` along every
line in direction `wᵢ`:

  `∫ cᵢ Φ(g) = τᵢ ∫ Φ'(g)`.
-/
theorem stein_coord_of_hasDerivAt {g : Ω → H} (hg : IsGaussianHilbert g) [DecidableEq hg.ι]
    (i : hg.ι) {Φ Φ' : H → ℝ}
    (hline : ∀ z : H, ∀ x : ℝ,
      HasDerivAt (fun t => Φ (z + t • hg.w i)) (Φ' (z + x • hg.w i)) x)
    (hΦm : Measurable Φ) (hΦ'm : Measurable Φ')
    (hint1 : Integrable (fun ω => hg.c i ω * Φ (g ω)) (ℙ : Measure Ω))
    (hint2 : Integrable (fun ω => Φ (g ω)) (ℙ : Measure Ω))
    (hint3 : Integrable (fun ω => Φ' (g ω)) (ℙ : Measure Ω)) :
    ∫ ω, hg.c i ω * Φ (g ω) ∂ℙ = (hg.τ i : ℝ) * ∫ ω, Φ' (g ω) ∂ℙ := by
  classical
  set X : Ω → ℝ := hg.c i with hXdef
  set Y : Ω → (CoordLine.Comp hg.ι i → ℝ) := fun ω j => hg.c j.1 ω with hYdef
  have hX_meas : Measurable X := hg.c_meas i
  have hY_meas : Measurable Y := measurable_pi_iff.mpr (fun j => hg.c_meas j.1)
  have hXlaw : Measure.map X (ℙ : Measure Ω) = gaussianReal 0 (hg.τ i) := hg.c_gauss i
  by_cases hτ : hg.τ i = 0
  · -- degenerate direction: `cᵢ = 0` a.s.
    have hzero : ∀ᵐ ω ∂(ℙ : Measure Ω), X ω = 0 := by
      refine ae_eq_zero_of_map_eq_dirac hX_meas ?_
      rw [hXlaw, hτ, gaussianReal_zero_var]
    have hL : (∫ ω, hg.c i ω * Φ (g ω) ∂ℙ) = 0 := by
      have h0 : (∫ ω, hg.c i ω * Φ (g ω) ∂ℙ) = ∫ ω, (0 : ℝ) ∂(ℙ : Measure Ω) := by
        refine integral_congr_ae ?_
        filter_upwards [hzero] with ω hω
        show hg.c i ω * Φ (g ω) = 0
        rw [show hg.c i ω = X ω from rfl, hω, zero_mul]
      rw [h0, integral_zero]
    rw [hL, hτ]
    simp
  · have hIndep : IndepFun Y X (ℙ : Measure Ω) := by
      have := ProbabilityTheory.indep_coord_complement (hg := hg) (i := i)
      rw [coord_eq_c (g := g) hg] at this
      exact this
    have hdecomp : ∀ ω, g ω = CoordLine.buildAlong (w := hg.w) i (Y ω) (X ω) :=
      CoordLine.g_decomp_along (ι := hg.ι) (hg := hg) i
    -- continuity/measurability of the rebuilt vector in the pair
    have hbuild_meas : Measurable (fun p : (CoordLine.Comp hg.ι i → ℝ) × ℝ =>
        CoordLine.buildAlong (w := hg.w) i p.1 p.2) := by
      have hsum : Continuous (fun p : (CoordLine.Comp hg.ι i → ℝ) × ℝ =>
          ∑ j : CoordLine.Comp hg.ι i, (p.1 j) • hg.w j.1) := by
        refine continuous_finset_sum _ (fun j _ => ?_)
        exact ((continuous_apply j).comp continuous_fst).smul continuous_const
      have h2 : Continuous (fun p : (CoordLine.Comp hg.ι i → ℝ) × ℝ => p.2 • hg.w i) :=
        continuous_snd.smul continuous_const
      exact (hsum.add h2).measurable
    set φ : (CoordLine.Comp hg.ι i → ℝ) × ℝ → ℝ :=
      fun p => p.2 * Φ (CoordLine.buildAlong (w := hg.w) i p.1 p.2) with hφdef
    set ψ₀ : (CoordLine.Comp hg.ι i → ℝ) × ℝ → ℝ :=
      fun p => Φ (CoordLine.buildAlong (w := hg.w) i p.1 p.2) with hψ₀def
    set ψ : (CoordLine.Comp hg.ι i → ℝ) × ℝ → ℝ :=
      fun p => Φ' (CoordLine.buildAlong (w := hg.w) i p.1 p.2) with hψdef
    have hφ_meas : Measurable φ := measurable_snd.mul (hΦm.comp hbuild_meas)
    have hψ₀_meas : Measurable ψ₀ := hΦm.comp hbuild_meas
    have hψ_meas : Measurable ψ := hΦ'm.comp hbuild_meas
    -- the integrands on `Ω`, rewritten through the decomposition
    have hφΩ : (fun ω => hg.c i ω * Φ (g ω)) = fun ω => φ (Y ω, X ω) := by
      funext ω; simp only [hφdef, ← hdecomp ω]; rfl
    have hψ₀Ω : (fun ω => Φ (g ω)) = fun ω => ψ₀ (Y ω, X ω) := by
      funext ω; simp only [hψ₀def, ← hdecomp ω]
    have hψΩ : (fun ω => Φ' (g ω)) = fun ω => ψ (Y ω, X ω) := by
      funext ω; simp only [hψdef, ← hdecomp ω]
    -- transport to the product law
    have hmap := map_pair_eq_prod_of_indep Y X hY_meas hX_meas hIndep
    have hchgφ : (∫ ω, φ (Y ω, X ω) ∂ℙ)
        = ∫ p, φ p ∂((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) := by
      rw [integral_pair_change_of_variables Y X hY_meas hX_meas hφ_meas, hmap, hXlaw]
    have hchgψ : (∫ ω, ψ (Y ω, X ω) ∂ℙ)
        = ∫ p, ψ p ∂((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) := by
      rw [integral_pair_change_of_variables Y X hY_meas hX_meas hψ_meas, hmap, hXlaw]
    have hφprod : Integrable φ ((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) :=
      integrable_phi_on_mapY_prod_gauss Y X hY_meas hX_meas hIndep (hg.τ i) hXlaw hφ_meas
        (by rw [← hφΩ]; exact hint1)
    have hψ₀prod : Integrable ψ₀ ((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) :=
      integrable_phi_on_mapY_prod_gauss Y X hY_meas hX_meas hIndep (hg.τ i) hXlaw hψ₀_meas
        (by rw [← hψ₀Ω]; exact hint2)
    have hψprod : Integrable ψ ((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) :=
      integrable_psi_on_mapY_prod_gauss Y X hY_meas hX_meas hIndep (hg.τ i) hXlaw hψ_meas
        (by rw [← hψΩ]; exact hint3)
    -- the line derivative in the rebuilt coordinates
    have hd : ∀ (y : CoordLine.Comp hg.ι i → ℝ) (x : ℝ),
        HasDerivAt (fun t => ψ₀ (y, t)) (ψ (y, x)) x := by
      intro y x
      show HasDerivAt (fun t => Φ ((∑ j : CoordLine.Comp hg.ι i, (y j) • hg.w j.1) + t • hg.w i))
        (Φ' ((∑ j : CoordLine.Comp hg.ι i, (y j) • hg.w j.1) + x • hg.w i)) x
      exact hline _ x
    haveI : SFinite (Measure.map Y (ℙ : Measure Ω)) := Measure.instSFiniteMap ℙ Y
    have hstein := stein_prod_of_hasDerivAt (Measure.map Y ℙ) (hg.τ i) hτ ψ₀ ψ hd hψ₀prod
      (by simpa [hφdef, hψ₀def] using hφprod) hψprod
    calc (∫ ω, hg.c i ω * Φ (g ω) ∂ℙ)
        = ∫ ω, φ (Y ω, X ω) ∂ℙ := by rw [hφΩ]
      _ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) := hchgφ
      _ = (hg.τ i : ℝ) * ∫ p, ψ p ∂((Measure.map Y ℙ).prod (gaussianReal 0 (hg.τ i))) := by
          simpa [hφdef, hψ₀def] using hstein
      _ = (hg.τ i : ℝ) * ∫ ω, ψ (Y ω, X ω) ∂ℙ := by rw [hchgψ]
      _ = (hg.τ i : ℝ) * ∫ ω, Φ' (g ω) ∂ℙ := by rw [hψΩ]

end SpinGlass
