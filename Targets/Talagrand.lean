/-
# Talagrand's proof of the Parisi formula: the structure of §2, in Lean

New work for the ParisiFormula project (not vendored).

## What this file is

The top-down skeleton of Talagrand (Annals 2006) §2, with Targets 3 and 4 *derived* from the
two analytic cores of the paper rather than assumed separately.  The point is legibility:
after this file, every remaining `sorry` on the critical path is a named theorem of the
paper, and the deduction of the Parisi formula from those theorems is machine-checked.

## The objects (Talagrand (2.1)–(2.4), (2.18))

* `guerraBase` — (2.2), `F_{k+1,t} = log ∑_σ exp H_t(σ)`, with the cascade Gaussians `y`
  left as a free argument;
* `guerraPhi` — (2.4), `φ(t) = (1/N) 𝔼 F_{1,t}`, obtained by pushing `guerraBase` through
  the `k+2` levels of `cascadeT` and averaging over the disorder.  As in (2.1), `√(1-t)`
  multiplies the cascade field *inside the base*, so the level variances are fixed and the
  tilted chain rule pushes `d/dt` straight to the base — Talagrand's (3.2);
* `guerraPsi` — (2.18), `ψ(t) = φ(0) - (t/2) ∑_ℓ m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))`.  For the SK
  model `ξ(x) = β²x²/2`, so `θ(q) = β²q²/2` and the sum is exactly the correction term of
  `parisiFunctional`; hence `ψ(1) = 𝒫_k(m,q)` on the nose (`guerraPsi_one`).

## The two cores

* `guerra_identity` — **Theorem 2.1** (Guerra's identity, (2.10)–(2.11)): on `(0,1)`,
  `φ'(t) = ψ'(t) - Rem(t)` with `0 ≤ Rem(t) ≤ β²`.  The remainder is
  `(β²/4) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ((R_{1,2} - q_ℓ)²)`; it is stated abstractly here because
  only its sign and size are consumed downstream.  No `c(N)` error term appears: our
  covariance kernel is exactly `(Nβ²/2) R²`.
* `talagrand_theorem_2_2` — **Theorem 2.2**: for `t₀ < 1` there is `ε > 0` such that, for any
  scheme that is `ε`-optimal (2.16) and minimises at its own level (2.17),
  `φ_N(t) → ψ(t)` for every `t ≤ t₀`.  This is the content of the paper's §3–§5 (Proposition
  2.3, the coupled-replica overlap concentration) and is the remaining large item.

## The derivations

* `guerra_rsb_bound` (Target 3) from Theorem 2.1: `Rem ≥ 0` makes `φ - ψ` non-increasing, so
  `φ(1) ≤ ψ(1)`, i.e. `free_entropy ≤ 𝒫_k(m,q)`, via `guerraPhi_one`, `guerraPhi_zero`.
* `parisi_formula` (Target 4) from Theorems 2.1 and 2.2 together with the minimiser of
  Target 2b-i, exactly as Talagrand deduces Theorem 1.1 on p. 229–230: `|φ'| ≤ L` gives
  `φ_N(1) ≥ φ_N(t₀) - L(1-t₀)`, Theorem 2.2 gives `φ_N(t₀) → ψ(t₀) ≥ 𝒫`, and `t₀ < 1` is
  arbitrary.  The upper half is Target 3'.
-/
import ParisiFormula.CoordStein
import Targets.CascadeDerivPi

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## 1. Talagrand's (2.1)–(2.4): the interpolation

`t` enters **only through the base** — exactly as in (2.1), where `√(1-t)` multiplies the
cascade Gaussians — so that the level variances are fixed and the tilted chain rule of
`Targets/CascadeDeriv.lean` pushes `d/dt` straight down to the base, which is Talagrand's
(3.2).  The cascade is evaluated at `0`; the external field `h` sits inside `H_t`.
-/

/-- (2.1): `H_t(σ) = √t H(σ) + ∑_i σ_i (h + √(1-t) y_i)`, with the cascade field `y` free. -/
noncomputable def guerraH (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ)
    (σ : Config n) : ℝ :=
  Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)

/-- (2.2): `F_{k+1,t}(y) = log ∑_σ exp H_t(σ)`. -/
noncomputable def guerraBase (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, Real.exp (guerraH n U h t y σ))

/-- (2.4): `φ(t) = (1/N) 𝔼 F_{1,t}` — the base pushed through the `k+2` cascade levels (fixed
variances), evaluated at `0`, averaged over the disorder. -/
noncomputable def guerraPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, cascadeT n s β 1 (guerraBase n (U ω) h t) (k + 2) 0 ∂ℙ

/-- The correction term of the Parisi functional, `(1/2) ∑_ℓ m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))` with
`θ(q) = β²q²/2`. -/
noncomputable def parisiCorrection {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℝ :=
  (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)

/-- (2.18): `ψ(t) = φ(0) - t · (correction)`.  Written with the closed form of `φ(0)` so that
it is visibly independent of `N` and of the disorder. -/
noncomputable def guerraPsi {k : ℕ} (s : RSBScheme k) (β h t : ℝ) : ℝ :=
  Real.log 2 + parisiF s β (k + 2) h - t * parisiCorrection s β

/-! ## 2. Endpoints and elementary facts -/

theorem guerraPsi_one {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    guerraPsi s β h 1 = parisiFunctional s β h := by
  rw [guerraPsi, parisiCorrection, parisiFunctional, one_mul]

theorem parisiCorrection_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    0 ≤ parisiCorrection s β := by
  unfold parisiCorrection
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun p hp => ?_)
  rw [Finset.mem_range] at hp
  have hm := s.m_nonneg (p := p + 1) (by omega)
  have hq := s.q_mono (p + 1) (by omega)
  have hq0 := s.q_nonneg (p := p + 1) (by omega)
  exact mul_nonneg hm (by nlinarith)

theorem parisiCorrection_le {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiCorrection s β ≤ β ^ 2 / 4 := by
  unfold parisiCorrection
  have := sum_correction_le_one s
  have hb : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
  nlinarith

/-- At `t = 0` there is no interaction: the base is the spin sum of `CascadeEndpoint` §4,
translated by the external field. -/
theorem guerraBase_zero (n : ℕ) (U : EnergySpace n) (h : ℝ) :
    guerraBase n U h 0
      = fun y => (fun w : Fin n → ℝ => ∑ i, Real.log (2 * Real.cosh (w i)))
          (y + fun _ => h) := by
  funext y
  show guerraBase n U h 0 y = ∑ i, Real.log (2 * Real.cosh ((y + fun _ : Fin n => h) i))
  have hH : ∀ σ : Config n,
      guerraH n U h 0 y σ = ∑ i, spin n σ i * (y + fun _ : Fin n => h) i := by
    intro σ
    simp only [guerraH, Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul,
      Pi.add_apply]
  simp only [guerraBase, hH]
  exact log_spinSum_exp _

/-- At `t = 1` the base is `log Z_N`, independent of the cascade field. -/
theorem guerraBase_one (n : ℕ) (β : ℝ) (U : EnergySpace n) (h : ℝ) :
    guerraBase n U h 1 = fun _ => Real.log (skZ (N := n) (β := β) (h := h) U) := by
  funext y
  have hmag : ∀ σ : Config n, (∑ i, spin n σ i * h) = h * magnetization n σ := by
    intro σ
    rw [magnetization, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hH : ∀ σ : Config n, guerraH n U h 1 y σ = U σ + h * magnetization n σ := by
    intro σ
    simp only [guerraH, Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, zero_add]
    rw [hmag σ]
  simp only [guerraBase, hH, skZ_eq]

/-- **(2.14): `φ(0) = log 2 + X_0`.** -/
theorem guerraPhi_zero {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 0 = Real.log 2 + parisiF s β (k + 2) h := by
  have hfun : ∀ ω, cascadeT n s β 1 (guerraBase n (U ω) h 0) (k + 2) 0
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    intro ω
    rw [guerraBase_zero,
      cascadeT_shift n s β 1 (fun w : Fin n → ℝ => ∑ i, Real.log (2 * Real.cosh (w i)))
        (fun _ => h), zero_add, cascadeT_one_scale]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint : (∫ ω, cascadeT n s β 1 (guerraBase n (U ω) h 0) (k + 2) 0 ∂ℙ)
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun), integral_const, probReal_univ,
      one_smul]
  rw [guerraPhi, hint]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

/-- **The `t = 1` endpoint: `φ(1)` is the free entropy.** -/
theorem guerraPhi_one {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 1 = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) U := by
  have hfun : ∀ ω, cascadeT n s β 1 (guerraBase n (U ω) h 1) (k + 2) 0
      = Real.log (skZ (N := n) (β := β) (h := h) (U ω)) := by
    intro ω
    rw [guerraBase_one n β, cascadeT_const]
  rw [guerraPhi, free_entropy, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  show (1 / (n : ℝ)) * cascadeT n s β 1 (guerraBase n (U ω) h 1) (k + 2) 0
      = free_energy_density (N := n) (skEnergy (N := n) (β := β) (h := h) (U ω))
  rw [hfun ω, free_energy_density]
  rfl

/-! ## 2b. The derivative of the base: `∂_t F_{k+1,t} = ⟨∂_t H_t⟩_t`

The first line of Talagrand's proof of Theorem 2.1 (§3, between (3.1) and (3.6)).  Since the
base is `log` of a *finite* sum of exponentials, its `t`-derivative is a finite Gibbs
average — no integration by parts is involved yet.  For `0 < t < 1`,

  `∂_t H_t(σ) = H(σ)/(2√t) - (∑_i σ_i y_i)/(2√(1-t))`,

and these two terms are what (3.7) calls `I` and (3.8) calls `∑_p II(p)`.
-/

/-- The finite Gibbs average `⟨f⟩ = ∑_σ f(σ) e^{E(σ)} / ∑_σ e^{E(σ)}` for the energy `E`
(Talagrand's `⟨·⟩_t` with `E = H_t`). -/
noncomputable def gibbsAvg {n : ℕ} (E f : Config n → ℝ) : ℝ :=
  (∑ σ, Real.exp (E σ) * f σ) / ∑ σ, Real.exp (E σ)

/-- `∂_t H_t(σ)` for `0 < t < 1`. -/
noncomputable def guerraHDeriv (n : ℕ) (U : EnergySpace n) (t : ℝ) (y : Fin n → ℝ)
    (σ : Config n) : ℝ :=
  U σ / (2 * Real.sqrt t) - (∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))

theorem hasDerivAt_guerraH (n : ℕ) (U : EnergySpace n) (h : ℝ) (y : Fin n → ℝ) (σ : Config n)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => guerraH n U h t y σ) (guerraHDeriv n U t y σ) t := by
  have ht0 : t ≠ 0 := ht.1.ne'
  have ht1 : 1 - t ≠ 0 := (sub_pos.2 ht.2).ne'
  have h1 : HasDerivAt (fun t => Real.sqrt t * U σ) (1 / (2 * Real.sqrt t) * U σ) t :=
    (Real.hasDerivAt_sqrt ht0).mul_const (U σ)
  have hs : HasDerivAt (fun t => Real.sqrt (1 - t)) (1 / (2 * Real.sqrt (1 - t)) * (-1)) t :=
    (Real.hasDerivAt_sqrt ht1).comp t ((hasDerivAt_id t).const_sub 1)
  have h2 : HasDerivAt (fun t => ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h))
      (∑ i, spin n σ i * (1 / (2 * Real.sqrt (1 - t)) * (-1) * y i)) t := by
    refine HasDerivAt.fun_sum (fun i _ => ?_)
    exact ((hs.mul_const (y i)).add_const h).const_mul _
  refine (h1.add h2).congr_deriv ?_
  unfold guerraHDeriv
  have hsum : (∑ i, spin n σ i * (1 / (2 * Real.sqrt (1 - t)) * (-1) * y i))
      = -((∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  ring

/-- **`∂_t F_{k+1,t} = ⟨∂_t H_t⟩_t`**: the derivative of the base is the Gibbs average of
`∂_t H_t`. -/
theorem hasDerivAt_guerraBase (n : ℕ) (U : EnergySpace n) (h : ℝ) (y : Fin n → ℝ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => guerraBase n U h t y)
      (gibbsAvg (guerraH n U h t y) (guerraHDeriv n U t y)) t := by
  have hsum : HasDerivAt (fun t => ∑ σ : Config n, Real.exp (guerraH n U h t y σ))
      (∑ σ : Config n, Real.exp (guerraH n U h t y σ) * guerraHDeriv n U t y σ) t :=
    HasDerivAt.fun_sum (fun σ _ => (hasDerivAt_guerraH n U h y σ ht).exp)
  have hpos : 0 < ∑ σ : Config n, Real.exp (guerraH n U h t y σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  exact hsum.log hpos.ne'

/-! ## 2b-i. Differentiating the base along the disorder

The disorder part of Gaussian integration by parts varies `U` along one basis direction.
This is the base case for pushing that line derivative through the cascade, just as
`hasDerivAt_guerraBase` is the base case for pushing the `t`-derivative through it.
-/

/-- The derivative of the base along the affine disorder line `U + u • V`.

The direction enters `guerraH` with coefficient `√t`, so the answer is `√t` times the
finite Gibbs average of `V` at the perturbed disorder.  No assumption on `t` is needed.
-/
noncomputable def guerraBaseUDeriv (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  Real.sqrt t * gibbsAvg (guerraH n U h t y) V

theorem hasDerivAt_guerraBase_Uline (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun u => guerraBase n (U + u • V) h t y)
      (guerraBaseUDeriv n (U + r • V) V h t y) r := by
  have hH : ∀ σ : Config n,
      HasDerivAt (fun u => guerraH n (U + u • V) h t y σ) (Real.sqrt t * V σ) r := by
    intro σ
    have heq : (fun u => guerraH n (U + u • V) h t y σ) =
        fun u => Real.sqrt t * U σ
          + u * (Real.sqrt t * V σ)
          + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h) := by
      funext u
      simp only [guerraH, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      congr 1
      ring
    rw [heq]
    simpa using (((hasDerivAt_const r (Real.sqrt t * U σ)).add
      ((hasDerivAt_id r).mul_const (Real.sqrt t * V σ))).add_const
        (∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)))
  have hsum : HasDerivAt
      (fun u => ∑ σ : Config n, Real.exp (guerraH n (U + u • V) h t y σ))
      (∑ σ : Config n,
        Real.exp (guerraH n (U + r • V) h t y σ) * (Real.sqrt t * V σ)) r :=
    HasDerivAt.fun_sum (fun σ _ => (hH σ).exp)
  have hpos : 0 < ∑ σ : Config n, Real.exp (guerraH n (U + r • V) h t y σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  refine (hsum.log hpos.ne').congr_deriv ?_
  unfold guerraBaseUDeriv
  unfold gibbsAvg
  have hnum :
      (∑ σ : Config n,
        Real.exp (guerraH n (U + r • V) h t y σ) * (Real.sqrt t * V σ)) =
        Real.sqrt t *
          ∑ σ : Config n, Real.exp (guerraH n (U + r • V) h t y σ) * V σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring
  rw [hnum]
  ring

/-! ## 2c. Bounds on the base and its derivative

What the level induction needs of `F_{k+1,t}`: measurability in `y`, `ℓ¹` growth with
constants uniform in `t ∈ [0,1]`, `ℓ¹`-Lipschitzness with constant `1`, and `ℓ¹` growth of
`∂_t F_{k+1,t}` with constants uniform for `t` away from the endpoints.  All elementary: the
base is `log` of a finite sum of exponentials.
-/

/-- `∂_t F_{k+1,t}` as a function of the cascade field. -/
noncomputable def guerraBaseDeriv (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) : ℝ :=
  gibbsAvg (guerraH n U h t y) (guerraHDeriv n U t y)

/-- `∑_σ |U σ|`, a crude size for the disorder. -/
noncomputable def uAbs (n : ℕ) (U : EnergySpace n) : ℝ := ∑ σ : Config n, |U σ|

theorem uAbs_nonneg (n : ℕ) (U : EnergySpace n) : 0 ≤ uAbs n U :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_uAbs (n : ℕ) (U : EnergySpace n) (σ : Config n) : |U σ| ≤ uAbs n U :=
  Finset.single_le_sum (fun τ _ => abs_nonneg (U τ)) (Finset.mem_univ σ)

theorem abs_spin (n : ℕ) (σ : Config n) (i : Fin n) : |spin n σ i| = 1 := by
  unfold spin; split <;> simp

/-- `log ∑_σ e^{f σ}` is within `log card + ∑_σ |f σ|` of `0`. -/
theorem abs_log_sum_exp_le {n : ℕ} (f : Config n → ℝ) :
    |Real.log (∑ σ : Config n, Real.exp (f σ))|
      ≤ Real.log (Fintype.card (Config n)) + ∑ σ, |f σ| := by
  have hpos : 0 < ∑ σ : Config n, Real.exp (f σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hcard : (0 : ℝ) < Fintype.card (Config n) := by exact_mod_cast Fintype.card_pos
  have hup : (∑ σ : Config n, Real.exp (f σ))
      ≤ Fintype.card (Config n) * Real.exp (∑ σ, |f σ|) := by
    calc (∑ σ : Config n, Real.exp (f σ)) ≤ ∑ _σ : Config n, Real.exp (∑ τ, |f τ|) := by
          refine Finset.sum_le_sum fun σ _ => Real.exp_le_exp.2 ?_
          exact (le_abs_self _).trans
            (Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ))
      _ = Fintype.card (Config n) * Real.exp (∑ τ, |f τ|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlow : Real.exp (-(∑ σ, |f σ|)) ≤ ∑ σ : Config n, Real.exp (f σ) := by
    obtain ⟨σ₀⟩ := (inferInstance : Nonempty (Config n))
    calc Real.exp (-(∑ σ, |f σ|)) ≤ Real.exp (f σ₀) := by
          refine Real.exp_le_exp.2 ?_
          have := Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ₀)
          linarith [neg_abs_le (f σ₀)]
      _ ≤ ∑ σ : Config n, Real.exp (f σ) :=
          Finset.single_le_sum (fun τ _ => (Real.exp_pos (f τ)).le) (Finset.mem_univ σ₀)
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    have hc : 0 ≤ Real.log (Fintype.card (Config n)) :=
      Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    linarith
  · have := Real.log_le_log hpos hup
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    exact this

/-- `log ∑ e^{f}` is `1`-Lipschitz in the sup norm of `f`. -/
theorem abs_log_sum_exp_sub_le {n : ℕ} {f g : Config n → ℝ} {ε : ℝ}
    (hε : ∀ σ, |f σ - g σ| ≤ ε) :
    |Real.log (∑ σ : Config n, Real.exp (f σ))
      - Real.log (∑ σ : Config n, Real.exp (g σ))| ≤ ε := by
  have hf : 0 < ∑ σ : Config n, Real.exp (f σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hg : 0 < ∑ σ : Config n, Real.exp (g σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have h1 : (∑ σ : Config n, Real.exp (f σ)) ≤ Real.exp ε * ∑ σ, Real.exp (g σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hε σ)).2])
  have h2 : (∑ σ : Config n, Real.exp (g σ)) ≤ Real.exp ε * ∑ σ, Real.exp (f σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hε σ)).1])
  have hl1 := Real.log_le_log hf h1
  have hl2 := Real.log_le_log hg h2
  rw [Real.log_mul (Real.exp_pos _).ne' hg.ne', Real.log_exp] at hl1
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hl2
  rw [abs_le]
  constructor <;> linarith

/-- A Gibbs average is bounded by the `ℓ¹` size of the observable. -/
theorem abs_gibbsAvg_le {n : ℕ} (E f : Config n → ℝ) : |gibbsAvg E f| ≤ ∑ σ, |f σ| := by
  unfold gibbsAvg
  have hpos : 0 < ∑ σ : Config n, Real.exp (E σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ σ, Real.exp (E σ) * f σ| ≤ ∑ σ, |Real.exp (E σ) * f σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ, Real.exp (E σ) * |f σ| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∑ σ, Real.exp (E σ) * ∑ τ, |f τ| := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ))
          (Real.exp_pos _).le
    _ = (∑ τ, |f τ|) * ∑ σ, Real.exp (E σ) := by rw [← Finset.sum_mul, mul_comm]

/-- The disorder-direction derivative has a bound independent of the cascade field. -/
theorem abs_guerraBaseUDeriv_le (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) :
    |guerraBaseUDeriv n U V h t y| ≤ Real.sqrt t * uAbs n V := by
  unfold guerraBaseUDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    (by simpa [uAbs] using abs_gibbsAvg_le (guerraH n U h t y) V)
    (Real.sqrt_nonneg t)

/-- `|H_t(σ)| ≤ |U σ| + ∑ᵢ|yᵢ| + n|h|` for `0 ≤ t ≤ 1`. -/
theorem abs_guerraH_le (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : Fin n → ℝ) (σ : Config n) :
    |guerraH n U h t y σ| ≤ |U σ| + (l1 y + n * |h|) := by
  have hst : Real.sqrt t ≤ 1 := by
    have := Real.sqrt_le_sqrt ht1; rwa [Real.sqrt_one] at this
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith); rwa [Real.sqrt_one] at this
  unfold guerraH
  refine (abs_add_le _ _).trans ?_
  have h1 : |Real.sqrt t * U σ| ≤ |U σ| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
    nlinarith [abs_nonneg (U σ)]
  have h2 : |∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)| ≤ l1 y + n * |h| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i, |spin n σ i * (Real.sqrt (1 - t) * y i + h)| ≤ |y i| + |h| := by
      intro i
      rw [abs_mul, abs_spin, one_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [abs_nonneg (y i)]
    calc (∑ i, |spin n σ i * (Real.sqrt (1 - t) * y i + h)|) ≤ ∑ i, (|y i| + |h|) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = l1 y + n * |h| := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  linarith

theorem guerraH_sub (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y y' : Fin n → ℝ) (σ : Config n) :
    guerraH n U h t y σ - guerraH n U h t y' σ
      = Real.sqrt (1 - t) * ∑ i, spin n σ i * (y i - y' i) := by
  unfold guerraH
  rw [Finset.mul_sum]
  have hsplit : ∀ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)
      - spin n σ i * (Real.sqrt (1 - t) * y' i + h)
      = Real.sqrt (1 - t) * (spin n σ i * (y i - y' i)) := fun i => by ring
  calc Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)
        - (Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y' i + h))
      = ∑ i, (spin n σ i * (Real.sqrt (1 - t) * y i + h)
          - spin n σ i * (Real.sqrt (1 - t) * y' i + h)) := by
        rw [Finset.sum_sub_distrib]; ring
    _ = ∑ i, Real.sqrt (1 - t) * (spin n σ i * (y i - y' i)) :=
        Finset.sum_congr rfl fun i _ => hsplit i

theorem abs_guerraHDeriv_le (n : ℕ) (U : EnergySpace n) (t : ℝ) (y : Fin n → ℝ) (σ : Config n) :
    |guerraHDeriv n U t y σ|
      ≤ |U σ| / (2 * Real.sqrt t) + l1 y / (2 * Real.sqrt (1 - t)) := by
  unfold guerraHDeriv
  refine (abs_sub _ _).trans ?_
  have hd1 : (0 : ℝ) ≤ 2 * Real.sqrt t := by positivity
  have hd2 : (0 : ℝ) ≤ 2 * Real.sqrt (1 - t) := by positivity
  have h1 : |U σ / (2 * Real.sqrt t)| = |U σ| / (2 * Real.sqrt t) := by
    rw [abs_div, abs_of_nonneg hd1]
  have h2 : |(∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))|
      ≤ l1 y / (2 * Real.sqrt (1 - t)) := by
    rw [abs_div, abs_of_nonneg hd2]
    refine div_le_div_of_nonneg_right ?_ hd2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [abs_mul, abs_spin, one_mul]
  linarith

/-! Measurability in the cascade field. -/

theorem measurable_guerraH (n : ℕ) (U : EnergySpace n) (h t : ℝ) (σ : Config n) :
    Measurable (fun y : Fin n → ℝ => guerraH n U h t y σ) := by
  unfold guerraH
  refine measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul ((measurable_const.mul (measurable_pi_apply i)).add measurable_const)

theorem measurable_guerraHDeriv (n : ℕ) (U : EnergySpace n) (t : ℝ) (σ : Config n) :
    Measurable (fun y : Fin n → ℝ => guerraHDeriv n U t y σ) := by
  unfold guerraHDeriv
  refine measurable_const.sub ?_
  exact (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)).div_const _

theorem measurable_guerraBase (n : ℕ) (U : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBase n U h t) := by
  unfold guerraBase
  exact Real.measurable_log.comp
    (Finset.measurable_sum _ fun σ _ => Real.measurable_exp.comp (measurable_guerraH n U h t σ))

theorem measurable_guerraBaseDeriv (n : ℕ) (U : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBaseDeriv n U h t) := by
  unfold guerraBaseDeriv gibbsAvg
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH n U h t σ)).mul (measurable_guerraHDeriv n U t σ)
  · exact Finset.measurable_sum _ fun σ _ => Real.measurable_exp.comp (measurable_guerraH n U h t σ)

/-- The disorder-direction derivative is measurable in the cascade field. -/
theorem measurable_guerraBaseUDeriv (n : ℕ) (U V : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBaseUDeriv n U V h t) := by
  unfold guerraBaseUDeriv gibbsAvg
  refine measurable_const.mul (Measurable.div ?_ ?_)
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH n U h t σ)).mul measurable_const
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH n U h t σ)

/-! The three bounds the induction consumes. -/

/-- `ℓ¹` growth of the base, uniform in `t ∈ [0,1]`. -/
theorem abs_guerraBase_le (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : Fin n → ℝ) :
    |guerraBase n U h t y|
      ≤ (Real.log (Fintype.card (Config n)) + uAbs n U + Fintype.card (Config n) * (n * |h|))
        + Fintype.card (Config n) * l1 y := by
  refine (abs_log_sum_exp_le _).trans ?_
  have : (∑ σ : Config n, |guerraH n U h t y σ|)
      ≤ uAbs n U + Fintype.card (Config n) * (l1 y + n * |h|) := by
    calc (∑ σ : Config n, |guerraH n U h t y σ|)
        ≤ ∑ σ : Config n, (|U σ| + (l1 y + n * |h|)) :=
          Finset.sum_le_sum fun σ _ => abs_guerraH_le n U h ht0 ht1 y σ
      _ = uAbs n U + Fintype.card (Config n) * (l1 y + n * |h|) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uAbs]
  linarith

/-- The base is `1`-Lipschitz in `ℓ¹`, for `t ≤ 1`. -/
theorem guerraBase_lipschitz (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (y y' : Fin n → ℝ) :
    |guerraBase n U h t y - guerraBase n U h t y'| ≤ 1 * l1 (y - y') := by
  unfold guerraBase
  refine abs_log_sum_exp_sub_le fun σ => ?_
  rw [guerraH_sub, one_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith); rwa [Real.sqrt_one] at this
  have hsum : |∑ i, spin n σ i * (y i - y' i)| ≤ l1 (y - y') := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [abs_mul, abs_spin, one_mul, Pi.sub_apply]
  nlinarith [abs_nonneg (∑ i, spin n σ i * (y i - y' i)), Real.sqrt_nonneg (1 - t)]

/-- `ℓ¹` growth of `∂_t F_{k+1,t}`, with constants controlled by `1/(2√t)`, `1/(2√(1-t))`. -/
theorem abs_guerraBaseDeriv_le (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) :
    |guerraBaseDeriv n U h t y|
      ≤ uAbs n U / (2 * Real.sqrt t)
        + (Fintype.card (Config n) / (2 * Real.sqrt (1 - t))) * l1 y := by
  refine (abs_gibbsAvg_le _ _).trans ?_
  calc (∑ σ : Config n, |guerraHDeriv n U t y σ|)
      ≤ ∑ σ : Config n, (|U σ| / (2 * Real.sqrt t) + l1 y / (2 * Real.sqrt (1 - t))) :=
        Finset.sum_le_sum fun σ _ => abs_guerraHDeriv_le n U t y σ
    _ = uAbs n U / (2 * Real.sqrt t)
          + (Fintype.card (Config n) / (2 * Real.sqrt (1 - t))) * l1 y := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_div, uAbs]
        ring

/-! ## 2d. Talagrand's (3.2): the derivative through the cascade

`∂_t F_{ℓ,t} = 𝔼_ℓ W_ℓ ∂_t F_{ℓ+1,t}`, iterated: the derivative of the cascade at level `j` is
the nested tilted average `guerraD j` of the base derivative.  The induction carries, on a
neighbourhood `talNbhd t₀` of the differentiation point, measurability in the cascade
field, `ℓ¹` growth and `ℓ¹`-Lipschitzness of the level, and `ℓ¹` growth of its derivative —
exactly the hypotheses of `hasDerivAt_parisiStepPi_param`.
-/

/-- Joint measurability of the shift `(x, z) ↦ x + √v z`. -/
theorem measurable_shift_prod (n : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + Real.sqrt v * p.2 i) :=
  measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

/-- `x ↦ parisiStepPi n m v A x` is measurable. -/
theorem measurable_parisiStepPi {n : ℕ} {A : (Fin n → ℝ) → ℝ} (hA : Measurable A) (m v : ℝ) :
    Measurable (fun x => parisiStepPi n m v A x) := by
  classical
  have hj : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A (fun i => p.1 i + Real.sqrt v * p.2 i)) := hA.comp (measurable_shift_prod n v)
  have hint0 : Measurable (fun x : Fin n → ℝ =>
      ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)) :=
    (hj.stronglyMeasurable.integral_prod_right').measurable
  have hint1 : Measurable (fun x : Fin n → ℝ =>
      ∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hj.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]; exact hint0
  · simp only [parisiStepPi, if_neg hm]
    exact (Real.measurable_log.comp hint1).const_mul _

/-- The tilted average `x ↦ ∫ g(x + √v z) W(z)` is measurable. -/
theorem measurable_tiltAvg {n : ℕ} {A g : (Fin n → ℝ) → ℝ} (hA : Measurable A) (hg : Measurable g)
    (m v : ℝ) :
    Measurable (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
      * tiltWeightPi n m v A x z ∂(piGauss n)) := by
  classical
  have hjg : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (fun i => p.1 i + Real.sqrt v * p.2 i)) := hg.comp (measurable_shift_prod n v)
  have hjA : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A (fun i => p.1 i + Real.sqrt v * p.2 i)) := hA.comp (measurable_shift_prod n v)
  have hI : Measurable (fun x : Fin n → ℝ =>
      ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hjA.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · have hfun : (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v A x z ∂(piGauss n))
        = fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z
          = g (fun i => x i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun]
    exact (hjg.stronglyMeasurable.integral_prod_right').measurable
  · have hfun : (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v A x z ∂(piGauss n))
        = fun x => ∫ z, (g (fun i => x i + Real.sqrt v * z i)
            * Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
            ∂(piGauss n) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z
          = (g (fun i => x i + Real.sqrt v * z i)
              * Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
      rw [tiltWeightPi, if_neg hm, mul_div_assoc]
    rw [hfun]
    have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (g (fun i => p.1 i + Real.sqrt v * p.2 i)
          * Real.exp (m * A (fun i => p.1 i + Real.sqrt v * p.2 i)))
          / (∫ w, Real.exp (m * A (fun i => p.1 i + Real.sqrt v * w i)) ∂(piGauss n))) :=
      (hjg.mul (Real.measurable_exp.comp (hjA.const_mul m))).div (hI.comp measurable_fst)
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The neighbourhood of `t₀ ∈ (0,1)` on which the induction runs. -/
def talNbhd (t₀ : ℝ) : Set ℝ := Set.Ioo (t₀ / 2) ((1 + t₀) / 2)

theorem talNbhd_mem_nhds {t₀ t : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ talNbhd t₀) :
    talNbhd t₀ ∈ 𝓝 t :=
  isOpen_Ioo.mem_nhds ht

theorem self_mem_talNbhd {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) : t₀ ∈ talNbhd t₀ :=
  ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩

theorem talNbhd_subset_Ioo {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    talNbhd t₀ ⊆ Set.Ioo (0 : ℝ) 1 := fun t ht =>
  ⟨by linarith [ht.1, ht₀.1], by linarith [ht.2, ht₀.2]⟩

/-- Talagrand's `∂_t F_{ℓ,t}`, defined top-down from the base derivative by tilted
averaging at each level — the right-hand side of (3.2) written level by level. -/
noncomputable def guerraD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (U : EnergySpace n) (h : ℝ) :
    ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun t => guerraBaseDeriv n U h t
  | j + 1 => fun t x => ∫ z,
      guerraD n s β U h j t
          (fun i => x i + Real.sqrt (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
        * tiltWeightPi n (s.m (k + 1 - j)) (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
            (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)

/-- The level variance is non-negative. -/
theorem levelVar_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    0 ≤ 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) := by
  rw [one_mul]
  refine mul_nonneg (sq_nonneg β) ?_
  rcases le_or_gt j (k + 1) with hj | hj
  · have hidx : k + 2 - j = (k + 1 - j) + 1 := by omega
    rw [hidx]
    linarith [s.q_mono (k + 1 - j) (by omega)]
  · have h1 : k + 2 - j = 0 := by omega
    have h2 : k + 1 - j = 0 := by omega
    rw [h1, h2]; simp

/--
**Talagrand's (3.2), level by level.**  On `talNbhd t₀`, level `j` of the cascade is
measurable, of `ℓ¹` growth, `ℓ¹`-Lipschitz, differentiable in `t` with derivative
`guerraD j`, and `guerraD j` is measurable and of `ℓ¹` growth.  The constants are uniform on
the neighbourhood **and affine in the size `uAbs n U` of the disorder, uniformly in `U`** —
which is what differentiating under the expectation over the disorder needs.
-/
theorem guerra_cascade_hasDerivAt {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (h : ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    ∃ a b D L a' b' D' : ℝ, 0 ≤ b ∧ 0 ≤ D ∧ 0 ≤ L ∧ 0 ≤ b' ∧ 0 ≤ D' ∧
    ∀ U : EnergySpace n,
    (∀ t ∈ talNbhd t₀, Measurable (cascadeT n s β 1 (guerraBase n U h t) j)) ∧
    (∀ t ∈ talNbhd t₀, Measurable (guerraD n s β U h j t)) ∧
    (∀ t ∈ talNbhd t₀, ∀ y,
        |cascadeT n s β 1 (guerraBase n U h t) j y| ≤ (a + b * uAbs n U) + D * l1 y) ∧
    (∀ t ∈ talNbhd t₀, ∀ y y',
        |cascadeT n s β 1 (guerraBase n U h t) j y - cascadeT n s β 1 (guerraBase n U h t) j y'|
          ≤ L * l1 (y - y')) ∧
    (∀ t ∈ talNbhd t₀, ∀ y, |guerraD n s β U h j t y| ≤ (a' + b' * uAbs n U) + D' * l1 y) ∧
    (∀ t ∈ talNbhd t₀, ∀ x, HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) j x)
        (guerraD n s β U h j t x) t) := by
  classical
  have hsub := talNbhd_subset_Ioo ht₀
  induction j with
  | zero =>
      have ht₀2 : 0 < t₀ / 2 := by linarith [ht₀.1]
      have h1t₀2 : 0 < (1 - t₀) / 2 := by linarith [ht₀.2]
      refine ⟨Real.log (Fintype.card (Config n)) + Fintype.card (Config n) * (n * |h|), 1,
        Fintype.card (Config n), 1, 0, 1 / (2 * Real.sqrt (t₀ / 2)),
        Fintype.card (Config n) / (2 * Real.sqrt ((1 - t₀) / 2)),
        zero_le_one, by positivity, zero_le_one, by positivity, by positivity, fun U => ?_⟩
      refine ⟨fun t _ => measurable_guerraBase n U h t, fun t _ => measurable_guerraBaseDeriv n U h t,
        fun t ht y => ?_, fun t ht y y' => ?_, fun t ht y => ?_, fun t ht x => ?_⟩
      · have := abs_guerraBase_le n U h (hsub ht).1.le (hsub ht).2.le y
        show |guerraBase n U h t y| ≤ _
        linarith
      · exact guerraBase_lipschitz n U h (hsub ht).1.le (hsub ht).2.le y y'
      · -- the derivative bound, with `1/(2√t)` monotone on the neighbourhood
        have hb := abs_guerraBaseDeriv_le n U h t y
        have hs1 : 2 * Real.sqrt (t₀ / 2) ≤ 2 * Real.sqrt t :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.1.le) (by norm_num)
        have hs2 : 2 * Real.sqrt ((1 - t₀) / 2) ≤ 2 * Real.sqrt (1 - t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [ht.2])) (by norm_num)
        have hp1 : 0 < 2 * Real.sqrt (t₀ / 2) := by positivity
        have hp2 : 0 < 2 * Real.sqrt ((1 - t₀) / 2) := by positivity
        have hA : uAbs n U / (2 * Real.sqrt t) ≤ uAbs n U / (2 * Real.sqrt (t₀ / 2)) :=
          div_le_div_of_nonneg_left (uAbs_nonneg n U) hp1 hs1
        have hB : (Fintype.card (Config n) : ℝ) / (2 * Real.sqrt (1 - t))
            ≤ Fintype.card (Config n) / (2 * Real.sqrt ((1 - t₀) / 2)) :=
          div_le_div_of_nonneg_left (by positivity) hp2 hs2
        have hB' := mul_le_mul_of_nonneg_right hB (l1_nonneg y)
        have hA' : uAbs n U / (2 * Real.sqrt (t₀ / 2))
            = (1 / (2 * Real.sqrt (t₀ / 2))) * uAbs n U := by ring
        show |guerraBaseDeriv n U h t y| ≤ _
        linarith
      · exact hasDerivAt_guerraBase n U h x (hsub ht)
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', ihU⟩ := ih
      set m : ℝ := s.m (k + 1 - j) with hm_def
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv_def
      have hm : 0 ≤ m := s.m_nonneg (by omega)
      have hv : 0 ≤ v := levelVar_nonneg s β j
      refine ⟨a + stepK n m v D, b, D, L,
        a' + (D' * Real.sqrt v)
          * (Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
              * ∫ z, l1 z * Real.exp ((|m| * L * Real.sqrt v) * l1 z) ∂(piGauss n)),
        b', D', hb, hD, hL, hb', hD', fun U => ?_⟩
      obtain ⟨hFm, hDm, hF, hLip, hD'b, hderiv⟩ := ihU U
      -- level `j+1` is one `N`-site step applied to level `j`
      have hstep : ∀ t, cascadeT n s β 1 (guerraBase n U h t) (j + 1)
          = fun x => parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x := by
        intro t; rfl
      have hDstep : ∀ t, guerraD n s β U h (j + 1) t
          = fun x => ∫ z, guerraD n s β U h j t (fun i => x i + Real.sqrt v * z i)
              * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n) := by
        intro t; rfl
      refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht y => ?_, fun t ht y y' => ?_,
        fun t ht y => ?_, fun t ht x => ?_⟩
      · rw [hstep]; exact measurable_parisiStepPi (hFm t ht) m v
      · rw [hDstep]; exact measurable_tiltAvg (hFm t ht) (hDm t ht) m v
      · rw [hstep]
        have := parisiStepPi_abs_le hm hv hD (hF t ht) (hFm t ht) y
        linarith
      · rw [hstep]
        exact parisiStepPi_lipschitz hD hL (hF t ht) (hFm t ht) (hLip t ht) y y'
      · rw [hDstep]
        have := abs_integral_mul_tiltWeightPi_le (m := m) (v := v) hL hD (hLip t ht) (hF t ht)
          (hFm t ht) (hDm t ht) hD' (hD'b t ht) y
        linarith
      · have hN := talNbhd_mem_nhds ht₀ ht
        show HasDerivAt (fun t => parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x)
          (∫ z, guerraD n s β U h j t (fun i => x i + Real.sqrt v * z i)
            * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)) t
        exact hasDerivAt_parisiStepPi_param (A := fun t => cascadeT n s β 1 (guerraBase n U h t) j)
          (A' := fun t => guerraD n s β U h j t) (m := m) (v := v)
          (C := a + b * uAbs n U) (D := D) (C' := a' + b' * uAbs n U) (D' := D') x hN hD hD'
          (fun u hu y => hderiv u hu y) hFm hDm hF hD'b

/-- **(3.2) at the top of the cascade**: `d/dt F_{1,t}(0) = guerraD (k+2) t 0`. -/
theorem hasDerivAt_cascade_top {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) (k + 2) 0)
      (guerraD n s β U h (k + 2) t 0) t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hU⟩ := guerra_cascade_hasDerivAt n s β h ht (k + 2)
  exact (hU U).2.2.2.2.2 t (self_mem_talNbhd ht) 0

/-- The size `uAbs` is controlled by the Hilbert norm: `|U σ| ≤ ‖U‖` coordinatewise. -/
theorem uAbs_le_card_mul_norm (n : ℕ) (U : EnergySpace n) :
    uAbs n U ≤ Fintype.card (Config n) * ‖U‖ := by
  unfold uAbs
  calc (∑ σ : Config n, |U σ|) ≤ ∑ _σ : Config n, ‖U‖ :=
        Finset.sum_le_sum fun σ _ => by
          have := PiLp.norm_apply_le U σ
          simpa [Real.norm_eq_abs] using this
    _ = Fintype.card (Config n) * ‖U‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The domination needed to differentiate under the expectation over the disorder**: on
`talNbhd t₀`, `|∂_t F_{1,t}(0)|` is bounded by an affine function of `‖U‖`, uniformly in `t`. -/
theorem abs_guerraD_top_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (h : ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ U : EnergySpace n, ∀ t ∈ talNbhd t₀,
      |guerraD n s β U h (k + 2) t 0| ≤ a + b * ‖U‖ := by
  obtain ⟨_, _, _, _, a', b', _, _, _, _, hb', _, hU⟩ :=
    guerra_cascade_hasDerivAt n s β h ht₀ (k + 2)
  refine ⟨a', b' * Fintype.card (Config n), by positivity, fun U t ht => ?_⟩
  have h1 := (hU U).2.2.2.2.1 t ht 0
  have h2 : l1 (0 : Fin n → ℝ) = 0 := by simp [l1]
  rw [h2, mul_zero, add_zero] at h1
  have h3 := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm n U) hb'
  nlinarith

/-! ## 2e. Differentiating `φ` under the expectation over the disorder

`φ(t) = (1/N) 𝔼_ω F_{1,t}(0)` with `F_{1,t}` depending on `ω` through `U ω`.  Two inputs:
measurability of `U ↦ F_{1,t}(0)` and of `U ↦ ∂_t F_{1,t}(0)` (an induction jointly in
`(U, x)`, the same parametric-integral argument as §2d), and the domination
`|∂_t F_{1,t}(0)| ≤ a + b‖U‖` of §2d with `‖U ω‖` integrable
(`integrable_norm_of_gaussian`).  Then `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
over `ℙ` gives `φ'(t) = (1/N) 𝔼_ω ∂_t F_{1,t}(0)`, i.e. Talagrand's (3.2) with the outer
expectation in place.
-/

/-- Coordinates of the energy space are measurable. -/
theorem measurable_coord (n : ℕ) (σ : Config n) : Measurable (fun U : EnergySpace n => U σ) := by
  have hc : Continuous (fun U : EnergySpace n =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Config n => ℝ) U) σ) :=
    (continuous_apply σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Config n => ℝ)).continuous
  exact hc.measurable

section Joint

variable {n : ℕ}

/-- The shift `((U, x), z) ↦ x + √v z`, jointly measurable. -/
theorem measurable_shift_joint (v : ℝ) :
    Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      fun i => q.1.2 i + Real.sqrt v * q.2 i) :=
  measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst.snd).add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

/-- One `N`-site level of a family `F U`, measurable jointly in `(U, x)`. -/
theorem measurable_parisiStepPi_joint {F : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => F p.1 p.2)) (m v : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => parisiStepPi n m v (F p.1) p.2) := by
  classical
  have hj : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hint0 : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, F p.1 (fun i => p.2 i + Real.sqrt v * z i) ∂(piGauss n)) :=
    (hj.stronglyMeasurable.integral_prod_right').measurable
  have hint1 : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hj.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]; exact hint0
  · simp only [parisiStepPi, if_neg hm]
    exact (Real.measurable_log.comp hint1).const_mul _

/-- The tilted average of a family `G U` against a family `F U`, jointly measurable. -/
theorem measurable_tiltAvg_joint {F G : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => F p.1 p.2))
    (hG : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => G p.1 p.2)) (m v : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
        * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n)) := by
  classical
  have hjG : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      G q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hjF : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hI : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hjF.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n))
        = fun p => ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext p
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show G p.1 (fun i => p.2 i + Real.sqrt v * z i) * tiltWeightPi n m v (F p.1) p.2 z
          = G p.1 (fun i => p.2 i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun]
    exact (hjG.stronglyMeasurable.integral_prod_right').measurable
  · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n))
        = fun p => ∫ z, (G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n))
            ∂(piGauss n) := by
      funext p
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show G p.1 (fun i => p.2 i + Real.sqrt v * z i) * tiltWeightPi n m v (F p.1) p.2 z
          = (G p.1 (fun i => p.2 i + Real.sqrt v * z i)
              * Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n))
      rw [tiltWeightPi, if_neg hm, mul_div_assoc]
    rw [hfun]
    have hjoint : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
        (G q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)
          * Real.exp (m * F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)))
          / (∫ w, Real.exp (m * F q.1.1 (fun i => q.1.2 i + Real.sqrt v * w i)) ∂(piGauss n))) :=
      (hjG.mul (Real.measurable_exp.comp (hjF.const_mul m))).div (hI.comp measurable_fst)
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_guerraH_joint (h t : ℝ) (σ : Config n) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraH n p.1 h t p.2 σ) := by
  unfold guerraH
  refine (measurable_const.mul ((measurable_coord n σ).comp measurable_fst)).add
    (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul
    ((measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).add measurable_const)

theorem measurable_guerraHDeriv_joint (t : ℝ) (σ : Config n) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraHDeriv n p.1 t p.2 σ) := by
  unfold guerraHDeriv
  refine (((measurable_coord n σ).comp measurable_fst).div_const _).sub ?_
  exact (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).div_const _

theorem measurable_guerraBase_joint (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraBase n p.1 h t p.2) := by
  unfold guerraBase
  exact Real.measurable_log.comp (Finset.measurable_sum _ fun σ _ =>
    Real.measurable_exp.comp (measurable_guerraH_joint h t σ))

theorem measurable_guerraBaseDeriv_joint (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraBaseDeriv n p.1 h t p.2) := by
  unfold guerraBaseDeriv gibbsAvg
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH_joint h t σ)).mul
        (measurable_guerraHDeriv_joint t σ)
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH_joint h t σ)

/-- Every level, and its derivative, is measurable jointly in `(U, x)`. -/
theorem measurable_cascade_joint {k : ℕ} (s : RSBScheme k) (β h t : ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
        cascadeT n s β 1 (guerraBase n p.1 h t) j p.2) ∧
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraD n s β p.1 h j t p.2) := by
  induction j with
  | zero => exact ⟨measurable_guerraBase_joint h t, measurable_guerraBaseDeriv_joint h t⟩
  | succ j ih =>
      obtain ⟨hF, hD⟩ := ih
      constructor
      · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
              cascadeT n s β 1 (guerraBase n p.1 h t) (j + 1) p.2)
            = fun p => parisiStepPi n (s.m (k + 1 - j))
                (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 := by
          funext p; rfl
        rw [hfun]
        exact measurable_parisiStepPi_joint
          (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j) hF _ _
      · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) => guerraD n s β p.1 h (j + 1) t p.2)
            = fun p => ∫ z, guerraD n s β p.1 h j t
                (fun i => p.2 i + Real.sqrt (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
                * tiltWeightPi n (s.m (k + 1 - j)) (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                    (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 z ∂(piGauss n) := by
          funext p; rfl
        rw [hfun]
        exact measurable_tiltAvg_joint
          (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
          (G := fun U => guerraD n s β U h j t) hF hD _ _

theorem measurable_cascade_top_U {k : ℕ} (s : RSBScheme k) (β h t : ℝ) :
    Measurable (fun U : EnergySpace n => cascadeT n s β 1 (guerraBase n U h t) (k + 2) 0) := by
  have hm := (measurable_cascade_joint (n := n) s β h t (k + 2)).1.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))
  exact hm

theorem measurable_guerraD_top_U {k : ℕ} (s : RSBScheme k) (β h t : ℝ) :
    Measurable (fun U : EnergySpace n => guerraD n s β U h (k + 2) t 0) := by
  have hm := (measurable_cascade_joint (n := n) s β h t (k + 2)).2.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))
  exact hm

end Joint

/--
**(3.2) with the expectation over the disorder**: for `0 < t < 1`,

  `φ'(t) = (1/N) 𝔼_ω [∂_t F_{1,t}(0)]`,

the outer expectation of the nested tilted average `guerraD (k+2)`.
-/
theorem hasDerivAt_guerraPhi {N : ℕ} (β h : ℝ) (sk : SKDisorder (Ω := Ω) N β h)
    {k : ℕ} (s : RSBScheme k) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi N s β h sk.U)
      ((1 / (N : ℝ)) * ∫ ω, guerraD N s β (sk.U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
  classical
  obtain ⟨a, b, hb, hbound⟩ := abs_guerraD_top_le N s β h ht₀ (k := k)
  obtain ⟨a₀, b₀, D, L, a', b', D', hb₀, -, -, -, -, hU⟩ :=
    guerra_cascade_hasDerivAt N s β h ht₀ (k + 2)
  have hUmeas : Measurable sk.U := sk.hU.repr_measurable
  have hnormint : Integrable (fun ω => ‖sk.U ω‖) (ℙ : Measure Ω) :=
    PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian sk.hU
  have hbint : Integrable (fun ω => a + b * ‖sk.U ω‖) (ℙ : Measure Ω) :=
    (integrable_const _).add (hnormint.const_mul _)
  have hs : talNbhd t₀ ∈ 𝓝 t₀ := talNbhd_mem_nhds ht₀ (self_mem_talNbhd ht₀)
  have hb2 : Integrable (fun ω => a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖))
      (ℙ : Measure Ω) :=
    (integrable_const _).add ((hnormint.const_mul _).const_mul _)
  have hF0 : Integrable
      (fun ω => cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0) (ℙ : Measure Ω) := by
    refine Integrable.mono hb2
      ((measurable_cascade_top_U s β h t₀).comp hUmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 := (hU (sk.U ω)).2.2.1 t₀ (self_mem_talNbhd ht₀) 0
    have h2 : l1 (0 : Fin N → ℝ) = 0 := by simp [l1]
    rw [h2, mul_zero, add_zero] at h1
    have h3 := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N (sk.U ω)) hb₀
    have hnn : 0 ≤ a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖) := by
      linarith [abs_nonneg (cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0)]
    show ‖cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0‖
        ≤ ‖a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  have hmain : HasDerivAt
      (fun t => ∫ ω, cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ)
      (∫ ω, guerraD N s β (sk.U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
      (F := fun t ω => cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0)
      (F' := fun t ω => guerraD N s β (sk.U ω) h (k + 2) t 0)
      (bound := fun ω => a + b * ‖sk.U ω‖) (s := talNbhd t₀) hs ?_ hF0 ?_ ?_ hbint ?_).2
    · filter_upwards [hs] with t ht
      exact ((measurable_cascade_top_U s β h t).comp hUmeas).aestronglyMeasurable
    · exact ((measurable_guerraD_top_U s β h t₀).comp hUmeas).aestronglyMeasurable
    · filter_upwards with ω t ht
      rw [Real.norm_eq_abs]
      exact hbound (sk.U ω) t ht
    · filter_upwards with ω t ht
      exact hasDerivAt_cascade_top N s β (sk.U ω) h (talNbhd_subset_Ioo ht₀ ht)
  show HasDerivAt (fun t => (1 / (N : ℝ))
      * ∫ ω, cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ) _ t₀
  exact hmain.const_mul (1 / (N : ℝ))

/-! ## 2f. Differentiating the cascade along the disorder

The coordinate Stein identity needs derivatives along the affine lines `U + u • V` in the
disorder space.  The base derivative is `guerraBaseUDeriv`; `guerraUD` pushes it through the
same normalized tilted averages as `guerraD`.  Since the base derivative is bounded
independently of the cascade field and every tilted weight integrates to one, this bound is
preserved exactly at every level.
-/

/-- The disorder-direction derivative propagated through `j` cascade levels. -/
noncomputable def guerraUD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h t : ℝ) : ℕ → (Fin n → ℝ) → ℝ
  | 0 => guerraBaseUDeriv n U V h t
  | j + 1 => fun x => ∫ z,
      guerraUD n s β U V h t j
          (fun i => x i + Real.sqrt
            (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
        * tiltWeightPi n (s.m (k + 1 - j))
            (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
            (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)

/-- The crude disorder size is subadditive along affine lines. -/
theorem uAbs_add_smul_le (n : ℕ) (U V : EnergySpace n) (u : ℝ) :
    uAbs n (U + u • V) ≤ uAbs n U + |u| * uAbs n V := by
  unfold uAbs
  calc
    (∑ σ : Config n, |(U + u • V) σ|)
        ≤ ∑ σ : Config n, (|U σ| + |u| * |V σ|) := by
          refine Finset.sum_le_sum (fun σ _ => ?_)
          simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_mul]
            using abs_add_le (U σ) (u * V σ)
    _ = (∑ σ : Config n, |U σ|) + |u| * ∑ σ : Config n, |V σ| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A fixed open neighborhood of a point on a disorder-coordinate line. -/
def guerraLineNbhd (r : ℝ) : Set ℝ := Set.Ioo (r - 1) (r + 1)

theorem guerraLineNbhd_mem_nhds (r : ℝ) : guerraLineNbhd r ∈ 𝓝 r :=
  isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩

theorem abs_le_abs_add_one_of_mem_guerraLineNbhd {r u : ℝ} (hu : u ∈ guerraLineNbhd r) :
    |u| ≤ |r| + 1 := by
  rw [abs_le]
  constructor
  · have hr := neg_abs_le r
    exact le_of_lt (by dsimp [guerraLineNbhd] at hu; linarith [hu.1])
  · have hr := le_abs_self r
    exact le_of_lt (by dsimp [guerraLineNbhd] at hu; linarith [hu.2])

/-- `guerraUD` is measurable in the cascade field, and its base bound is preserved at every
level because the tilted weights are normalized probability densities. -/
theorem guerraUD_measurable_and_bound {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ j : ℕ, Measurable (guerraUD n s β U V h t j) ∧
      ∀ x, |guerraUD n s β U V h t j x| ≤ Real.sqrt t * uAbs n V := by
  intro j
  induction j with
  | zero =>
      exact ⟨measurable_guerraBaseUDeriv n U V h t,
        abs_guerraBaseUDeriv_le n U V h t⟩
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      obtain ⟨hAmeas, -, hAbound, hAlip, -, -⟩ := hprops U
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      set m : ℝ := s.m (k + 1 - j) with hm
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv
      have hmeas : Measurable (guerraUD n s β U V h t (j + 1)) := by
        change Measurable (fun x => ∫ z,
          guerraUD n s β U V h t j (fun i => x i + Real.sqrt v * z i)
            * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z
          ∂(piGauss n))
        exact measurable_tiltAvg (hAmeas t htt) ih.1 m v
      refine ⟨hmeas, fun x => ?_⟩
      change |∫ z, guerraUD n s β U V h t j (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z
        ∂(piGauss n)| ≤ Real.sqrt t * uAbs n V
      have hbound := abs_integral_mul_tiltWeightPi_le
        (m := m) (v := v) (C := a + b * uAbs n U) (D := D) (L := L)
        hL hD (hAlip t htt) (hAbound t htt) (hAmeas t htt) ih.1
        (C' := Real.sqrt t * uAbs n V) (D' := 0) le_rfl
        (fun y => by simpa using ih.2 y) x
      simpa using hbound

/-- The full cascade has derivative `guerraUD` along every affine disorder line. -/
theorem hasDerivAt_cascade_Uline {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (x : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun u => cascadeT n s β 1 (guerraBase n (U + u • V) h t) j x)
      (guerraUD n s β (U + r • V) V h t j x) r := by
  induction j generalizing U x r with
  | zero => exact hasDerivAt_guerraBase_Uline n U V h t x r
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      set m : ℝ := s.m (k + 1 - j) with hm
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv
      have hs : guerraLineNbhd r ∈ 𝓝 r := guerraLineNbhd_mem_nhds r
      have hlinebound : ∀ u ∈ guerraLineNbhd r,
          uAbs n (U + u • V) ≤ uAbs n U + (|r| + 1) * uAbs n V := by
        intro u hu
        refine (uAbs_add_smul_le n U V u).trans ?_
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (abs_le_abs_add_one_of_mem_guerraLineNbhd hu) (uAbs_nonneg n V))
      change HasDerivAt
        (fun u => parisiStepPi n m v
          (cascadeT n s β 1 (guerraBase n (U + u • V) h t) j) x)
        (∫ z, guerraUD n s β (U + r • V) V h t j
            (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v
              (cascadeT n s β 1 (guerraBase n (U + r • V) h t) j) x z
          ∂(piGauss n)) r
      exact hasDerivAt_parisiStepPi_param
        (A := fun u => cascadeT n s β 1 (guerraBase n (U + u • V) h t) j)
        (A' := fun u => guerraUD n s β (U + u • V) V h t j)
        (m := m) (v := v)
        (C := (a + b * (uAbs n U + (|r| + 1) * uAbs n V))) (D := D)
        (C' := Real.sqrt t * uAbs n V) (D' := 0) x hs hD le_rfl
        (fun u _ y => ih (U := U) (x := y) (r := u))
        (fun u _ => (hprops (U + u • V)).1 t htt)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • V) V h ht j).1)
        (fun u hu y => by
          have hbu := (hprops (U + u • V)).2.2.1 t htt y
          have hmul := mul_le_mul_of_nonneg_left (hlinebound u hu) hb
          linarith)
        (fun u _ y => by
          have hbu := (guerraUD_measurable_and_bound n s β (U + u • V) V h ht j).2 y
          simpa using hbu)

/-- For a fixed disorder direction `V`, the base directional derivative is jointly
measurable in the current disorder and the cascade field. -/
theorem measurable_guerraBaseUDeriv_joint {n : ℕ} (V : EnergySpace n) (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraBaseUDeriv n p.1 V h t p.2) := by
  unfold guerraBaseUDeriv gibbsAvg
  refine measurable_const.mul (Measurable.div ?_ ?_)
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH_joint h t σ)).mul measurable_const
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH_joint h t σ)

/-- For fixed direction `V`, every propagated disorder derivative is jointly measurable
in the current disorder `U` and the cascade field `x`. -/
theorem measurable_guerraUD_joint {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (V : EnergySpace n) (h t : ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraUD n s β p.1 V h t j p.2) := by
  induction j with
  | zero => exact measurable_guerraBaseUDeriv_joint V h t
  | succ j ih =>
      have hF := (measurable_cascade_joint (n := n) s β h t j).1
      have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          guerraUD n s β p.1 V h t (j + 1) p.2) =
          fun p => ∫ z,
            guerraUD n s β p.1 V h t j
                (fun i => p.2 i + Real.sqrt
                  (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
              * tiltWeightPi n (s.m (k + 1 - j))
                  (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                  (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 z ∂(piGauss n) := by
        funext p
        rfl
      rw [hfun]
      exact measurable_tiltAvg_joint
        (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
        (G := fun U => guerraUD n s β U V h t j) hF ih _ _

/-- The top-level disorder-direction derivative is measurable as a function of the current
disorder. -/
theorem measurable_guerraUD_top_U {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (V : EnergySpace n) (h t : ℝ) :
    Measurable (fun U : EnergySpace n => guerraUD n s β U V h t (k + 2) 0) := by
  exact (measurable_guerraUD_joint s β V h t (k + 2)).comp
    (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))

/-- Gaussian integration by parts for the top cascade in a fixed disorder direction. -/
theorem guerra_cascade_stein {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (a : EnergySpace N) :
    (∫ ω, inner ℝ (sk.U ω) a
        * cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ) =
      ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * inner ℝ a (sk.hU.w i)
        * ∫ ω, guerraUD N s β (sk.U ω) (sk.hU.w i) h t (k + 2) 0 ∂ℙ := by
  classical
  let Φ : EnergySpace N → ℝ := fun U =>
    cascadeT N s β 1 (guerraBase N U h t) (k + 2) 0
  let D : sk.hU.ι → EnergySpace N → ℝ := fun i U =>
    guerraUD N s β U (sk.hU.w i) h t (k + 2) 0
  have hΦm : Measurable Φ := measurable_cascade_top_U s β h t
  have hDm : ∀ i : sk.hU.ι, Measurable (D i) := fun i =>
    measurable_guerraUD_top_U s β (sk.hU.w i) h t
  obtain ⟨A, B, E, L, A', B', E', hB, hE, hL, hB', hE', hprops⟩ :=
    guerra_cascade_hasDerivAt N s β h ht (k + 2)
  have hΦbound : ∀ U : EnergySpace N,
      |Φ U| ≤ A + (B * Fintype.card (Config N)) * ‖U‖ := by
    intro U
    have hbase := (hprops U).2.2.1 t (self_mem_talNbhd ht) 0
    have hu := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N U) hB
    simp [l1] at hbase
    dsimp only [Φ]
    calc
      |cascadeT N s β 1 (guerraBase N U h t) (k + 2) 0|
          ≤ A + B * uAbs N U := hbase
      _ ≤ A + B * (Fintype.card (Config N) * ‖U‖) := by linarith
      _ = A + (B * Fintype.card (Config N)) * ‖U‖ := by ring
  have hA : 0 ≤ A := by
    have hz := hΦbound (0 : EnergySpace N)
    exact le_trans (abs_nonneg (Φ 0)) (by simpa using hz)
  have hnormSlope : 0 ≤ B * Fintype.card (Config N) := by positivity
  have hintCoord : ∀ i : sk.hU.ι,
      Integrable (fun ω => sk.hU.c i ω * Φ (sk.U ω)) (ℙ : Measure Ω) := fun i =>
    integrable_coord_mul_comp_of_affine_norm_bound sk.hU i hΦm hA hnormSlope hΦbound
  have hintΦ : Integrable (fun ω => Φ (sk.U ω)) (ℙ : Measure Ω) :=
    integrable_comp_of_affine_norm_bound sk.hU hΦm hA hnormSlope hΦbound
  have hintD : ∀ i : sk.hU.ι,
      Integrable (fun ω => D i (sk.U ω)) (ℙ : Measure Ω) := by
    intro i
    have hC : 0 ≤ Real.sqrt t * uAbs N (sk.hU.w i) :=
      mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg N _)
    refine integrable_comp_of_affine_norm_bound sk.hU (hDm i)
      (C := Real.sqrt t * uAbs N (sk.hU.w i)) (D := 0) hC le_rfl ?_
    intro U
    have hb := (guerraUD_measurable_and_bound N s β U (sk.hU.w i) h ht (k + 2)).2 0
    simpa only [D, zero_mul, add_zero] using hb
  have hline : ∀ i : sk.hU.ι, ∀ z : EnergySpace N, ∀ x : ℝ,
      HasDerivAt (fun r => Φ (z + r • sk.hU.w i))
        (D i (z + x • sk.hU.w i)) x := by
    intro i z x
    exact hasDerivAt_cascade_Uline N s β z (sk.hU.w i) h ht (k + 2) 0 x
  simpa only [Φ, D] using
    (stein_inner_of_hasDerivAt (g := sk.U) sk.hU a (Φ := Φ) (D := D)
      hline hΦm hDm hintCoord hintΦ hintD)

/-! ## 3. The two analytic cores of the paper -/

/--
**Theorem 2.1 (Guerra's identity).**  On `(0,1)`,

  `φ'(t) = ψ'(t) - Rem(t)`,   `0 ≤ Rem(t) ≤ β²`,

together with continuity of `φ` on `[0,1]`.  Here `ψ'(t) = -parisiCorrection`, and the
remainder is Talagrand's `(1/2) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ(ξ(R) - Rξ'(q_ℓ) + θ(q_ℓ))`, which for
the SK model is `(β²/4) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ((R_{1,2} - q_ℓ)²)`: non-negative by (2.11),
and at most `β²` since `|R_{1,2} - q_ℓ| ≤ 2` and `∑_ℓ (m_ℓ - m_{ℓ-1}) = 1`.  No `c(N)`
error term: the covariance kernel is exactly `(Nβ²/2) R²`.

The ingredients are built in `Targets/CascadeDeriv.lean` (the tilted chain rule through
each level, and the growth bounds that let it chain); what remains is the Gaussian
integration by parts at the base and the algebra identifying the result with the overlap
form.
-/
theorem guerra_identity {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (guerraPhi N s β h sk.U) (Set.Icc (0 : ℝ) 1) ∧
    ∃ Rem : ℝ → ℝ, (∀ t, 0 ≤ Rem t ∧ Rem t ≤ β ^ 2) ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (guerraPhi N s β h sk.U) (-(parisiCorrection s β) - Rem t) t := by
  sorry

/--
**Theorem 2.2.**  Given `t₀ < 1` there is `ε > 0`, depending only on `t₀`, `β`, `h`, such
that for every scheme satisfying (2.16) `𝒫_k(m,q) ≤ 𝒫 + ε` and (2.17) minimality at its own
level, `φ_N(t) → ψ(t)` as `N → ∞` for every `0 ≤ t ≤ t₀`.

This is the content of the paper's §3–§5, deduced there from Proposition 2.3 (the
coupled-replica overlap concentration `μ_r((R_{1,2} - q_r)² ≥ K(ψ(t) - φ(t)) + ε₁) ≤ ε₁`).
-/
theorem talagrand_theorem_2_2 (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun N => guerraPhi N s β h (sk N).U t) atTop (𝓝 (guerraPsi s β h t)) := by
  sorry

/-! ## 4. Target 3 from Theorem 2.1 -/

/-- **Target 3 (Guerra 2003), (2.12)–(2.15).**  `φ - ψ` is non-increasing because
`Rem ≥ 0`, so `φ(1) ≤ ψ(1)`: the free entropy is at most `𝒫_k(m,q)`, with no `O(1/N)`
error term. -/
theorem guerra_rsb_bound {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U ≤ parisiFunctional s β h := by
  obtain ⟨hcont, Rem, hRem, hderiv⟩ := guerra_identity hN β h sk s
  have hdiff : DifferentiableOn ℝ (guerraPhi N s β h sk.U) (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hle : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (guerraPhi N s β h sk.U) t ≤ -(parisiCorrection s β) := by
    rw [interior_Icc]
    intro t ht
    rw [(hderiv t ht).deriv]
    linarith [(hRem t).1]
  have hmvt := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff hle
    0 (by simp) 1 (by simp) zero_le_one
  rw [guerraPhi_one N hN s β h sk.U, guerraPhi_zero N hN s β h sk.U] at hmvt
  rw [parisiFunctional]
  simp only [parisiCorrection, sub_zero, mul_one] at hmvt
  linarith

/-- **Target 3' (upper bound in the limit).**  Immediate from Target 3: the free entropy is a
lower bound for the whole defining set of `parisiValue`, hence at most its infimum. -/
theorem limsup_free_entropy_le_parisiValue (β h : ℝ)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h + ε := by
  intro ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hle : free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h := by
    refine le_csInf (parisiSet_nonempty β h) ?_
    rintro x ⟨k, s, rfl⟩
    exact guerra_rsb_bound hN β h (sk N) s
  linarith

/-! ## 5. Target 4 from Theorems 2.1 and 2.2 -/

/--
**Target 4 (the Parisi formula), Talagrand's Theorem 1.1**, deduced from Theorems 2.1 and
2.2 exactly as on p. 229–230 of the paper.

Upper half: Target 3'.  Lower half: fix `a < 𝒫` and pick `t₀ < 1` so close to `1` that
`L(1 - t₀)` is small, where `L` bounds `|φ'|` by Theorem 2.1.  Theorem 2.2 supplies `ε`; by
definition of the infimum some scheme is `ε`-optimal, and Target 2b-i replaces it by a
minimiser at the same level, which is still `ε`-optimal.  Then `φ_N(t₀) → ψ(t₀) ≥ 𝒫`, and
`φ_N(1) ≥ φ_N(t₀) - L(1 - t₀)` by the mean value theorem, so eventually `φ_N(1) > a`.
-/
theorem parisi_formula (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 (parisiValue β h)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound
    set η : ℝ := (parisiValue β h - a) / 2 with hη
    have hηpos : 0 < η := by rw [hη]; linarith
    set L : ℝ := β ^ 2 / 4 + β ^ 2 with hL
    have hLpos : 0 < L := by rw [hL]; positivity
    set t₀ : ℝ := max 0 (1 - η / (2 * (L + 1))) with ht₀
    have ht₀0 : 0 ≤ t₀ := le_max_left _ _
    have ht₀1 : t₀ < 1 := by
      rw [ht₀]
      apply max_lt one_pos
      have : 0 < η / (2 * (L + 1)) := by positivity
      linarith
    have hgap : L * (1 - t₀) ≤ η / 2 := by
      have h1 : 1 - η / (2 * (L + 1)) ≤ t₀ := le_max_right _ _
      have h2 : 1 - t₀ ≤ η / (2 * (L + 1)) := by linarith
      have hfrac : L / (L + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      have hrw : L * (η / (2 * (L + 1))) = (η / 2) * (L / (L + 1)) := by
        field_simp
      calc L * (1 - t₀) ≤ L * (η / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h2 hLpos.le
        _ = (η / 2) * (L / (L + 1)) := hrw
        _ ≤ η / 2 := by nlinarith [hηpos.le]
    obtain ⟨ε, hεpos, hthm⟩ := talagrand_theorem_2_2 β h hβ sk ht₀1
    -- an `ε`-optimal scheme, then a minimiser at its level (Target 2b-i)
    obtain ⟨x, ⟨k, s₀, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (parisiSet_nonempty β h)
      (show sInf {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}
          < parisiValue β h + ε from lt_add_of_pos_right _ hεpos)
    obtain ⟨s, hsmin⟩ := exists_minimizer_parisiFunctional k β h
    have hs16 : parisiFunctional s β h ≤ parisiValue β h + ε := le_trans (hsmin s₀) hx.le
    have hconv := hthm s hs16 hsmin t₀ ht₀0 le_rfl
    -- `ψ(t₀) ≥ 𝒫`
    have hψ : parisiValue β h ≤ guerraPsi s β h t₀ := by
      have h1 : parisiValue β h ≤ parisiFunctional s β h := parisiValue_le s β h
      rw [← guerraPsi_one] at h1
      rw [guerraPsi] at h1 ⊢
      have hc := parisiCorrection_nonneg s β
      nlinarith [ht₀1.le]
    have hev1 : ∀ᶠ N in atTop,
        guerraPsi s β h t₀ - η / 2 < guerraPhi N s β h (sk N).U t₀ :=
      (tendsto_order.1 hconv).1 _ (by linarith)
    filter_upwards [hev1, eventually_gt_atTop 0] with N hN1 hNpos
    -- mean value theorem on `[t₀, 1]` with `|φ'| ≤ L`
    obtain ⟨hcont, Rem, hRem, hderiv⟩ := guerra_identity hNpos β h (sk N) s
    have hdiff : DifferentiableOn ℝ (guerraPhi N s β h (sk N).U)
        (interior (Set.Icc (0 : ℝ) 1)) := by
      rw [interior_Icc]
      intro t ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    have hge : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        -L ≤ deriv (guerraPhi N s β h (sk N).U) t := by
      rw [interior_Icc]
      intro t ht
      rw [(hderiv t ht).deriv]
      have := parisiCorrection_le s β
      have := (hRem t).2
      rw [hL]
      linarith
    have hmvt := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont hdiff hge
      t₀ ⟨ht₀0, ht₀1.le⟩ 1 (by simp) ht₀1.le
    rw [guerraPhi_one N hNpos s β h (sk N).U] at hmvt
    show a < free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U
    linarith
  · -- upper bound: Target 3'
    have hε : 0 < (b - parisiValue β h) / 2 := by linarith
    filter_upwards [limsup_free_entropy_le_parisiValue β h sk _ hε] with N hN
    show free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U < b
    linarith

end Targets
end SpinGlass
