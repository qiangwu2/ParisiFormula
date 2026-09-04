import ParisiFormula.GuerraToninelli
import ParisiFormula.AnnealedBound
import ParisiFormula.GaussianCosh
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Target statements for the ParisiFormula project

This file states, with `sorry`, the theorems the project aims to prove.  It is the
Lean-side counterpart of `blueprint/blueprint.tex`.  Nothing here is proved; the
point is to pin down *exact statements* against the vendored API so that every
milestone has a precise, machine-checkable finish line.

This file is built by `lake build Targets`, never by the default build, because it
contains `sorry` on purpose (and, being written before the project had a working
Lean environment, may need small syntactic repairs).

## Conventions (inherited from the vendored core, `Lemmas/SpinGlass/`)

* A configuration on `N` spins is `Config N := Fin N → Bool`, with `spin N σ i ∈ {±1}`.
* An SK disorder `sk : SKDisorder N β h` is a centred Gaussian random vector
  `sk.U : Ω → EnergySpace N` with covariance `E[U σ · U τ] = (N β²/2) · R(σ,τ)²`,
  where `R` is the overlap.  In the language of mixed p-spin models this is
  `N β² ξ(R)` with `ξ(x) = x²/2`.
* The quenched free entropy is `free_entropy β h sk.U = (1/N) E log ∑_σ exp(U σ + h ∑ᵢ σᵢ)`
  (defined in `ParisiFormula/GuerraToninelli.lean`).

## References

* M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263.
* F. Guerra, *Broken replica symmetry bounds in the mean field spin glass model*,
  Comm. Math. Phys. 233 (2003), 1–12.
* F. Guerra, F. L. Toninelli, *The thermodynamic limit in mean field spin glass models*,
  Comm. Math. Phys. 230 (2002), 71–79.
* M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I (Ch. 1) and Vol. II (Ch. 12–14).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal ProbabilityTheory

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Milestone 1 — existence of the thermodynamic limit (Guerra–Toninelli)

`ParisiFormula/GuerraToninelli.lean` already contains the whole argument *except* two
hypotheses that were left open upstream: an upper bound on the free entropy, and
monotonicity of the interpolation `Φ`.  Targets 1a and 1b discharge them; 1c assembles.
-/

/-- Mutual independence of the three disorders entering the Guerra–Toninelli interpolation
(sizes `N+M`, `N`, `M`).  Expressed as pairwise independence of `skN.U` and `skM.U`, plus
independence of `skL.U` from the pair. -/
structure IndepTriple {N M : ℕ} {β h : ℝ}
    (skL : SKDisorder (Ω := Ω) (N + M) β h)
    (skN : SKDisorder (Ω := Ω) N β h)
    (skM : SKDisorder (Ω := Ω) M β h) : Prop where
  indep_NM : skN.U ⟂ᵢ[(ℙ : Measure Ω)] skM.U
  indep_L_pair : skL.U ⟂ᵢ[(ℙ : Measure Ω)] (fun ω => (skN.U ω, skM.U ω))

/-- **Target 1a (annealed bound).**  Jensen's inequality `E log Z ≤ log E Z` and the Gaussian
moment generating function give `(1/N) E log Z_N ≤ log 2 + β²/4 + |h|`.

Reference: Talagrand Vol. I, (1.24) and the discussion after it. -/
theorem free_entropy_le_annealed {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U
      ≤ Real.log 2 + β ^ 2 / 4 + |h| :=
  _root_.SpinGlass.free_entropy_le_annealed hN β h sk

/-- **Target 1b (Gaussian comparison).**  The Guerra–Toninelli interpolation
`Φ(t) = E log Z_{N+M}(√t · K_{N+M} + √(1-t) · (K_N ⊕ K_M))` is non-decreasing on `[0,1]`.

Proof plan (blueprint, Chapter 1): differentiate under the expectation (dominated
convergence, cf. `SpinGlass.hasDerivAt_nu` in `Lemmas/SpinGlass/Replicas.lean`), rewrite
`Φ'(t)` by Gaussian integration by parts
(`PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov`) as a trace of
the covariance difference `C_L - C_blk` against the Hessian of `log Z`
(`SpinGlass.trace_formula`), then use the two facts already proved in
`ParisiFormula/GuerraToninelli.lean`: the diagonal of `C_L - C_blk` vanishes and its
off-diagonal is `≤ 0` (convexity of `x ↦ x²`), while the off-diagonal Hessian entries of
`log Z` are `≤ 0`.  Hence `Φ' ≥ 0`.

Reference: Guerra–Toninelli (2002); Talagrand Vol. I, Theorem 1.3.7 (in the 2nd edition:
Section 1.3, "the Guerra–Toninelli argument"). -/
theorem Φ_monotoneOn {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (β h : ℝ) (hβ : 0 < β)
    (skL : SKDisorder (Ω := Ω) (N + M) β h)
    (skN : SKDisorder (Ω := Ω) N β h)
    (skM : SKDisorder (Ω := Ω) M β h)
    (hindep : IndepTriple skL skN skM) :
    MonotoneOn
      (Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM))
      (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- **Target 1c (thermodynamic limit).**  Assembles 1a and 1b with the already-formalised
Fekete argument `free_entropy_tendsto_of_bddAbove`. -/
theorem free_entropy_tendsto (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h)
    (hindep : ∀ N M : ℕ, IndepTriple (sk (N + M)) (sk N) (sk M)) :
    ∃ ℓ : ℝ, Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 ℓ) := by
  sorry

/-! ## Milestone 2 — the finite-step Parisi functional (no PDE)

Following Talagrand (Annals 2006, §1), a `k`-step replica-symmetry-breaking scheme is a pair
of non-decreasing sequences

  `0 = m₀ ≤ m₁ ≤ ⋯ ≤ m_k ≤ m_{k+1} = 1`,   `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`.

The functional is defined by a *finite backward recursion* through the Gaussian smoothing
operator `T_{m,v}`, so no Parisi PDE is needed.  (The vendored file `port/ParisiOperator.lean`
contains an upstream formalisation of `T_{m,v}` and its semigroup law, awaiting port.)
-/

/-- A `k`-step RSB scheme.  Sequences are indexed by `ℕ` (values beyond the stated range are
irrelevant) to avoid dependent-index bookkeeping. -/
structure RSBScheme (k : ℕ) where
  /-- `m 0 = 0`, …, `m (k+1) = 1`. -/
  m : ℕ → ℝ
  /-- `q 0 = 0`, …, `q (k+2) = 1`. -/
  q : ℕ → ℝ
  m_zero : m 0 = 0
  m_top : m (k + 1) = 1
  m_mono : ∀ p, p ≤ k → m p ≤ m (p + 1)
  q_zero : q 0 = 0
  q_top : q (k + 2) = 1
  q_mono : ∀ p, p ≤ k + 1 → q p ≤ q (p + 1)

/-- Gaussian smoothing step at "temperature" `m` and variance `v`:

  `T_{m,v} A (x) = (1/m) log ∫ exp(m · A(x + √v · z)) dγ(z)`  for `m ≠ 0`,
  `T_{0,v} A (x) = ∫ A(x + √v · z) dγ(z)`,

with `γ` the standard Gaussian.  The `m = 0` case is the `m → 0` limit of the first. -/
noncomputable def parisiStep (m v : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then
    ∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1)
  else
    (1 / m) * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))

/-- Backward Parisi recursion for the SK model (`ξ(x) = x²/2`, so `ξ'(x) = x`).

`parisiF s β j` is the function `F_{k+2-j}` of Talagrand's recursion:

  `F_{k+2}(x) = log cosh x`,
  `F_p = T_{m_p, β²(q_{p+1} - q_p)} F_{p+1}`   for `p = k+1, k, …, 1`,
  `F_0 = T_{0, β² q₁} F_1 = E F_1(· + β√q₁ z)`.

So `parisiF s β (k+2)` is `F_0` (there are `k+2` smoothing steps: `p = k+1, …, 1`, then `p = 0`). -/
noncomputable def parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun x => Real.log (Real.cosh x)
  | j + 1 =>
      parisiStep (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
        (parisiF s β j)

/-- The `k`-step Parisi functional for the SK model with external field `h`:

  `𝒫_k(m,q) = log 2 + F_0(h) - (β²/4) ∑_{p=1}^{k+1} m_p (q_{p+1}² - q_p²)`.

(The prefactor `β²/4` is `β²/2 · (θ(q_{p+1}) - θ(q_p))` with `θ(q) = q ξ'(q) - ξ(q) = q²/2`.) -/
noncomputable def parisiFunctional {k : ℕ} (s : RSBScheme k) (β h : ℝ) : ℝ :=
  Real.log 2 + parisiF s β (k + 2) h
    - (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)

/-- The replica-symmetric scheme with overlap `q`: `k = 0`, `m = (0, 1)`, `q = (0, q, 1)`. -/
noncomputable def rsScheme (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : RSBScheme 0 where
  m := fun p => if p = 0 then 0 else 1
  q := fun p => if p = 0 then 0 else if p = 1 then q else 1
  m_zero := by simp
  m_top := by simp
  m_mono := by
    intro p hp
    have : p = 0 := Nat.le_zero.mp hp
    subst this
    norm_num
  q_zero := by simp
  q_top := by simp
  q_mono := by
    intro p hp
    have hp' : p ≤ 1 := by simpa using hp
    interval_cases p <;> simp [hq0, hq1]

/-- **Target 2a (sanity check: RS case).**  The `0`-step functional is the classical
replica-symmetric formula `log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`.

This lemma guards against off-by-one or normalisation mistakes in the definitions above:
if it is false, the definitions are wrong, not the theorem.

Hand computation to check against (`k = 0`, `m = (0,1)`, `q = (0,q,1)`):
`F_1 = T_{1, β²(1-q)} (log cosh)`, and `∫ cosh(x + σ z) dγ(z) = cosh x · e^{σ²/2}`, so
`F_1(x) = log cosh x + β²(1-q)/2`; then `F_0(h) = E log cosh(h + β√q z) + β²(1-q)/2` and
`𝒫_0 = log 2 + F_0(h) - (β²/4)(1 - q²) = log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`. -/
theorem parisiFunctional_rsScheme (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    parisiFunctional (rsScheme q hq0 hq1) β h
      = Real.log 2
        + (∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1))
        + (β ^ 2 / 4) * (1 - q) ^ 2 := by
  classical
  set s := rsScheme q hq0 hq1 with hs
  have hm0 : s.m 0 = 0 := by simp [hs, rsScheme]
  have hm1 : s.m 1 = 1 := by simp [hs, rsScheme]
  have hqq0 : s.q 0 = 0 := by simp [hs, rsScheme]
  have hqq1 : s.q 1 = q := by simp [hs, rsScheme]
  have hqq2 : s.q 2 = 1 := by simp [hs, rsScheme]
  have hv1 : (0:ℝ) ≤ β ^ 2 * (1 - q) := mul_nonneg (sq_nonneg β) (by linarith)
  have hlogcosh_cont : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))
  -- `F₁ = T_{1, β²(1-q)} (log cosh) = log cosh + β²(1-q)/2`
  have hF1 : parisiF s β 1
      = fun x => Real.log (Real.cosh x) + β ^ 2 * (1 - q) / 2 := by
    funext x
    show parisiStep (s.m 1) (β ^ 2 * (s.q 2 - s.q 1)) (parisiF s β 0) x = _
    rw [hm1, hqq2, hqq1, parisiStep, if_neg (one_ne_zero)]
    have hpt : ∀ z : ℝ,
        Real.exp (1 * parisiF s β 0 (x + Real.sqrt (β ^ 2 * (1 - q)) * z))
          = Real.cosh (x + Real.sqrt (β ^ 2 * (1 - q)) * z) := by
      intro z
      show Real.exp (1 * Real.log (Real.cosh _)) = _
      rw [one_mul, Real.exp_log (Real.cosh_pos _)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_cosh_add_mul_stdGaussian x (Real.sqrt (β ^ 2 * (1 - q))),
        Real.sq_sqrt hv1,
        Real.log_mul (ne_of_gt (Real.cosh_pos x)) (Real.exp_ne_zero _),
        Real.log_exp]
    ring
  -- `F₀(h) = ∫ log cosh (h + |β|√q z) dγ + β²(1-q)/2`
  have hsq : Real.sqrt (β ^ 2 * q) = |β| * Real.sqrt q := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have hF0 : parisiF s β 2 h
      = (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
          + β ^ 2 * (1 - q) / 2 := by
    show parisiStep (s.m 0) (β ^ 2 * (s.q 1 - s.q 0)) (parisiF s β 1) h = _
    rw [hm0, hqq1, hqq0, sub_zero, parisiStep, if_pos rfl, hF1, hsq]
    rw [integral_add (integrable_log_cosh_stdGaussian (|β| * Real.sqrt q) h)
        (integrable_const _)]
    simp
  -- the correction sum is `1 * (1 - q²)`
  have hsum : (∑ p ∈ Finset.range (0 + 1),
      s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) = 1 * (1 - q ^ 2) := by
    simp [hm1, hqq1, hqq2]
  -- `|β|√q` and `β√q` agree under the symmetric Gaussian
  have hrefl :
      (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
        = ∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
    rcases le_or_lt 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by rw [add_comm]))
    · rw [abs_of_neg hβ]
      have hre := integral_reflect_stdGaussian
        (f := fun y : ℝ => Real.log (Real.cosh y)) hlogcosh_cont (β * Real.sqrt q) h
      rw [show -β * Real.sqrt q = -(β * Real.sqrt q) by ring, ← hre]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by rw [add_comm]))
  rw [parisiFunctional, hF0, hsum, hrefl]
  ring

/-- **Target 2b (Lipschitz continuity in the scheme).**  Guerra's estimate: for two schemes
with the same `k`, `|𝒫_k(m,q) - 𝒫_k(m',q')| ≤ C(β) · ∑_p (|m_p - m'_p| + |q_p - q'_p|)`
(up to the precise form of the right-hand side, to be fixed in the blueprint).  This is what
makes `inf_k inf_{(m,q)} 𝒫_k` well-behaved and lets one pass from discrete to general Parisi
measures.  Stated here only as a placeholder shape. -/
theorem parisiFunctional_lipschitz (β h : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ s s' : RSBScheme k,
      |parisiFunctional s β h - parisiFunctional s' β h|
        ≤ C * ∑ p ∈ Finset.range (k + 3), (|s.m p - s'.m p| + |s.q p - s'.q p|) := by
  sorry

/-! ## Milestone 3 — Guerra's replica-symmetry-breaking bound -/

/-- **Target 3 (Guerra 2003).**  For every `N`, every `(β, h)` and every finite-step scheme,
`(1/N) E log Z_N ≤ 𝒫_k(m,q)`.

Because the vendored covariance kernel is exactly `(Nβ²/2) R²` (no diagonal correction), the
bound holds with no `O(1/N)` error term.

Proof plan (blueprint, Chapter 3): interpolate between the SK Hamiltonian and a hierarchical
Gaussian field `∑ᵢ σᵢ ∑_p z_p^i √(β²(q_{p+1} - q_p))` organised along a `k+2`-level tree;
define `φ(t)` through iterated `(1/m_p) log E_p exp(m_p ·)`; compute `φ'(t)` via Gaussian
IBP; the remainder is a sum of terms `-(β²/4)(m_{p+1} - m_p) E⟨(R - q_p)²⟩ ≤ 0`. -/
theorem guerra_rsb_bound {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U ≤ parisiFunctional s β h := by
  sorry

/-- The Parisi value: infimum of the finite-step functionals over all `k` and all schemes. -/
noncomputable def parisiValue (β h : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}

/-- **Target 3' (upper bound in the limit).**  Immediate from Target 3. -/
theorem limsup_free_entropy_le_parisiValue (β h : ℝ)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h + ε := by
  sorry

/-! ## Milestone 4 — the Parisi formula (Talagrand 2006) -/

/-- **Target 4 (the Parisi formula).**  `lim_N (1/N) E log Z_N = inf_k inf_{(m,q)} 𝒫_k(m,q)`.

The upper bound is Target 3.  The lower bound is Talagrand's coupled-replica argument
(Annals 2006), whose replica-symmetric ancestor is formalised in RSAT as
`SpinGlass.AT.twoReplica_GT_bound`.  This is the long-term goal of the project; the
statement is recorded so the finish line is unambiguous.

Note that no independence assumption across sizes is needed: `free_entropy` depends only on
the law of `sk N`. -/
theorem parisi_formula (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 (parisiValue β h)) := by
  sorry

end Targets
end SpinGlass
