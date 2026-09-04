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
  the `k+2` levels of `cascadeT` and averaging over the disorder.  The `1-t` is carried by
  the level variances (`Targets/CascadeEndpoint.lean` §7), so both endpoint collapses proved
  there apply verbatim;
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
import Targets.CascadeDeriv

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## 1. Talagrand's (2.1)–(2.4): the interpolation -/

/-- (2.2): the innermost level of the interpolating cascade, `log ∑_σ exp H_t(σ)`, with the
cascade field `y` left free.  Talagrand's `H_t` is `√t H(σ) + ∑_i σ_i (h + √(1-t) ∑_p z_{i,p})`;
here the `√(1-t)` is carried by the level variances of `cascadeT` and the external field `h`
is the evaluation point, so the base sees only `√t H(σ) + ∑_i σ_i y_i`. -/
noncomputable def guerraBase (n : ℕ) (U : EnergySpace n) (t : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, Real.exp (Real.sqrt t * U σ + ∑ i, spin n σ i * y i))

/-- (2.4): `φ(t) = (1/N) 𝔼 F_{1,t}` — the base pushed through the `k+2` cascade levels with
variances scaled by `1 - t`, evaluated at the external field, averaged over the disorder. -/
noncomputable def guerraPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ ω, cascadeT n s β (1 - t) (guerraBase n (U ω) t) (k + 2) (fun _ => h) ∂ℙ

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

/-- At `t = 0` the base has no interaction between sites and is the spin sum of §4 of
`CascadeEndpoint`. -/
theorem guerraBase_zero (n : ℕ) (U : EnergySpace n) :
    guerraBase n U 0 = fun y => ∑ i, Real.log (2 * Real.cosh (y i)) := by
  funext y
  rw [guerraBase]
  simp only [Real.sqrt_zero, zero_mul, zero_add]
  exact log_spinSum_exp y

/-- At `t = 1`, evaluated at the external field, the base is `log Z_N`. -/
theorem guerraBase_one_apply (n : ℕ) (β : ℝ) (U : EnergySpace n) (h : ℝ) :
    guerraBase n U 1 (fun _ => h) = Real.log (skZ (N := n) (β := β) (h := h) U) := by
  have hmag : ∀ σ : Config n, (∑ i, spin n σ i * h) = h * magnetization n σ := by
    intro σ
    rw [magnetization, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  simp only [guerraBase, skZ_eq, Real.sqrt_one, one_mul, hmag]

/-- **(2.14): `φ(0) = log 2 + X_0`.**  The `t = 0` endpoint: no interaction, so the cascade
collapses to `N` copies of the one-dimensional recursion. -/
theorem guerraPhi_zero {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 0 = Real.log 2 + parisiF s β (k + 2) h := by
  have hfun : ∀ ω, cascadeT n s β (1 - 0) (guerraBase n (U ω) 0) (k + 2) (fun _ => h)
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    intro ω
    rw [sub_zero, guerraBase_zero, cascadeT_one_scale]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint : (∫ ω, cascadeT n s β (1 - 0) (guerraBase n (U ω) 0) (k + 2) (fun _ => h) ∂ℙ)
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun), integral_const, probReal_univ,
      one_smul]
  rw [guerraPhi, hint]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

/-- **The `t = 1` endpoint: `φ(1)` is the free entropy.**  The variances vanish, the cascade
is the identity, and the base is `log Z_N`. -/
theorem guerraPhi_one {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 1 = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) U := by
  have hfun : ∀ ω, cascadeT n s β (1 - 1) (guerraBase n (U ω) 1) (k + 2) (fun _ => h)
      = Real.log (skZ (N := n) (β := β) (h := h) (U ω)) := by
    intro ω
    rw [sub_self, cascadeT_zero_scale, guerraBase_one_apply]
  rw [guerraPhi, free_entropy, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  show (1 / (n : ℝ)) * cascadeT n s β (1 - 1) (guerraBase n (U ω) 1) (k + 2) (fun _ => h)
      = free_energy_density (N := n) (skEnergy (N := n) (β := β) (h := h) (U ω))
  rw [hfun ω, free_energy_density]
  rfl

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
