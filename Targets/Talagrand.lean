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
`guerraD j`, and `guerraD j` is measurable and of `ℓ¹` growth — all with constants uniform
on the neighbourhood.
-/
theorem guerra_cascade_hasDerivAt {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    (∀ t ∈ talNbhd t₀, Measurable (cascadeT n s β 1 (guerraBase n U h t) j)) ∧
    (∀ t ∈ talNbhd t₀, Measurable (guerraD n s β U h j t)) ∧
    (∃ C D : ℝ, 0 ≤ D ∧ ∀ t ∈ talNbhd t₀, ∀ y,
        |cascadeT n s β 1 (guerraBase n U h t) j y| ≤ C + D * l1 y) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ talNbhd t₀, ∀ y y',
        |cascadeT n s β 1 (guerraBase n U h t) j y - cascadeT n s β 1 (guerraBase n U h t) j y'|
          ≤ L * l1 (y - y')) ∧
    (∃ C' D' : ℝ, 0 ≤ D' ∧ ∀ t ∈ talNbhd t₀, ∀ y, |guerraD n s β U h j t y| ≤ C' + D' * l1 y) ∧
    (∀ t ∈ talNbhd t₀, ∀ x, HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) j x)
        (guerraD n s β U h j t x) t) := by
  classical
  have hsub := talNbhd_subset_Ioo ht₀
  induction j with
  | zero =>
      have ht₀2 : 0 < t₀ / 2 := by linarith [ht₀.1]
      have h1t₀2 : 0 < (1 - t₀) / 2 := by linarith [ht₀.2]
      refine ⟨fun t _ => measurable_guerraBase n U h t, fun t _ => measurable_guerraBaseDeriv n U h t,
        ⟨Real.log (Fintype.card (Config n)) + uAbs n U + Fintype.card (Config n) * (n * |h|),
          Fintype.card (Config n), by positivity, fun t ht y => ?_⟩,
        ⟨1, zero_le_one, fun t ht y y' => ?_⟩,
        ⟨uAbs n U / (2 * Real.sqrt (t₀ / 2)),
          Fintype.card (Config n) / (2 * Real.sqrt ((1 - t₀) / 2)), by positivity,
          fun t ht y => ?_⟩,
        fun t ht x => ?_⟩
      · exact abs_guerraBase_le n U h (hsub ht).1.le (hsub ht).2.le y
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
        show |guerraBaseDeriv n U h t y| ≤ _
        linarith
      · exact hasDerivAt_guerraBase n U h x (hsub ht)
  | succ j ih =>
      obtain ⟨hFm, hDm, ⟨C, D, hD, hF⟩, ⟨L, hL, hLip⟩, ⟨C', D', hD', hD'b⟩, hderiv⟩ := ih
      set m : ℝ := s.m (k + 1 - j) with hm_def
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv_def
      have hm : 0 ≤ m := s.m_nonneg (by omega)
      have hv : 0 ≤ v := levelVar_nonneg s β j
      -- level `j+1` is one `N`-site step applied to level `j`
      have hstep : ∀ t, cascadeT n s β 1 (guerraBase n U h t) (j + 1)
          = fun x => parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x := by
        intro t; rfl
      have hDstep : ∀ t, guerraD n s β U h (j + 1) t
          = fun x => ∫ z, guerraD n s β U h j t (fun i => x i + Real.sqrt v * z i)
              * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n) := by
        intro t; rfl
      refine ⟨fun t ht => ?_, fun t ht => ?_,
        ⟨C + stepK n m v D, D, hD, fun t ht y => ?_⟩,
        ⟨L, hL, fun t ht y y' => ?_⟩,
        ⟨C' + (D' * Real.sqrt v)
            * (Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
                * ∫ z, l1 z * Real.exp ((|m| * L * Real.sqrt v) * l1 z) ∂(piGauss n)),
          D', hD', fun t ht y => ?_⟩,
        fun t ht x => ?_⟩
      · rw [hstep]; exact measurable_parisiStepPi (hFm t ht) m v
      · rw [hDstep]; exact measurable_tiltAvg (hFm t ht) (hDm t ht) m v
      · rw [hstep]
        exact parisiStepPi_abs_le hm hv hD (hF t ht) (hFm t ht) y
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
          (C := C) (D := D) (C' := C') (D' := D') x hN hD hD'
          (fun u hu y => hderiv u hu y) hFm hDm hF hD'b

/-- **(3.2) at the top of the cascade**: `d/dt F_{1,t}(0) = guerraD (k+2) t 0`. -/
theorem hasDerivAt_cascade_top {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) (k + 2) 0)
      (guerraD n s β U h (k + 2) t 0) t :=
  (guerra_cascade_hasDerivAt n s β U h ht (k + 2)).2.2.2.2.2 t (self_mem_talNbhd ht) 0

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
