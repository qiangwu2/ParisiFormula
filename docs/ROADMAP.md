# Roadmap

## Critical path to the goal

**Goal: Talagrand's proof of the Parisi formula (Ann. of Math. 163 (2006)) — Target 4.**

Target 4 is `Tendsto (fun N => s_N) atTop (𝓝 (parisiValue β h))`, which follows from

* **limsup ≤** — Target 3' , itself immediate from Target 3 (Guerra's RSB bound) via
  `parisiValue_le`; and
* **liminf ≥** — Talagrand's coupled-replica lower bound (Milestone 4), whose induction on
  the number of RSB levels needs **Target 2b-i** (continuity of `𝒫_k` in the parameters for
  fixed `k`, hence existence of a minimiser — Talagrand's (2.17)).  **2b-i is now proved**,
  so the critical path to Target 4 is reduced to Milestone 3 (`3 → 3'`).

So the critical path is: **3 → 3'** and **2b → 4**, with `parisiValue` well-definedness
(done: `bddBelow_parisiSet`) underneath both.

**Milestone 1 (Targets 1b, 1c) is *not* on this critical path.**  Target 4 is strictly
stronger than 1c — convergence to `parisiValue` subsumes existence of a limit — and deriving
4 from 3' plus the lower bound never invokes 1c.  Milestone 1 is the classical
Guerra–Toninelli (2002) result and a useful warm-up that exercises the same interpolation +
Gaussian-IBP machinery Milestone 3 needs, but work there should not be mistaken for progress
toward Target 4.  (Caveat: Talagrand's own exposition sometimes uses existence of the limit
as a convenience; if the Milestone 4 blueprint turns out to need it, 1c moves onto the path.)

Infrastructure that serves *both* (and so is never wasted): the generalisation of
`isGaussianHilbert_UV` to independent `IsGaussianHilbert` vectors, needed for Gaussian IBP in
Milestone 3 as well as in Target 1b.

Concrete, ordered work items. Each maps to a statement in `Targets/Milestones.lean` and a
numbered result in `blueprint/blueprint.tex`. Items are sized roughly
(S = hours, M = days, L = weeks, XL = months).

## Phase 0 — make the skeleton build  (S–M)  — **done**

- [x] `lake exe cache get && lake build` succeeds (Tier 1). Unchanged code, as expected.
- [x] `lake build ParisiFormula` succeeds (Tier 2). Three repairs were needed after all
      (`Fin.addCases_castAdd_natAdd` is now pointwise; two `simpa`s that no longer close
      their goals). See `docs/PROVENANCE.md`.
- [x] `lake build Targets` elaborates (Tier 3), with only `sorry` warnings.
- [x] CI green on GitHub (`.github/workflows/build.yml`).

Note that Tier 3 elaborating means the *statements* are well-formed, not that they are the
right statements: `parisiFunctional` typechecked both before and after an off-by-one in the
`parisiF` index was corrected. Only Target 2a can catch that class of mistake — do it early.

## Phase 1 — Milestone 1: the thermodynamic limit  (M–L)

- [x] Make `cov_deriv_diag` and `cov_deriv_offdiag_nonpos` in
      `ParisiFormula/GuerraToninelli.lean` non-`private` (they are needed by 1b).
- [x] **1a** `free_entropy_le_annealed`: Jensen + Gaussian mgf. **Done**, in
      `ParisiFormula/AnnealedBound.lean`.  Jensen is proved elementarily from
      `log x ≤ x - 1` (`integral_log_le_log_integral`).  The Gaussian moment came out
      as `mgf_inner_isGaussianHilbert`: the mgf of a coordinate `⟪g ·, v⟫` of an
      `IsGaussianHilbert` vector is `exp (⟪Σ v, v⟫ / 2)`, obtained from the ONB
      representation via `iIndepFun.mgf_sum` and `mgf_gaussianReal`.  Note this
      *sidesteps* the missing "continuous linear images of Hilbert Gaussians are
      Gaussian" lemma, which the vendored core does not provide and which would
      otherwise have been the expensive part.
- [ ] **1b** `Φ_monotoneOn`, in three sub-steps mirroring `port/GuerraPipeline.lean`:
  - [ ] dominated differentiation of `Φ` (adapt `hasDerivAt_guerraPhi` from
        `port/GuerraInterpolation.lean` — port needed, or reuse `hasDerivAt_nu` from
        `Lemmas/SpinGlass/Replicas.lean`); (M)
  - [ ] Gaussian IBP rewrite of `Φ'` (`port/GuerraIBP.lean` is *not* adaptable — fork
        mismatch, see `port/README.md`); (M, but see the blocker below)
  - [ ] **BLOCKER, newly identified:** `IsGaussianHilbert (K_block …)`.  The IBP lemma needs
        `(skL.U, K_block)` packaged as one Gaussian-Hilbert vector (RSAT has `UV` /
        `isGaussianHilbert_UV` for an independent *pair*, which is what `IndepTriple` is for),
        and that first needs `K_block` itself to be `IsGaussianHilbert`.  It is never shown
        Gaussian anywhere in the project, and `IsGaussianHilbert` is a concrete
        ONB-plus-independent-coordinates *structure*, not a property, so it is not closed
        under linear images and no closure lemma exists in `Lemmas/SpinGlass/`.
        Concatenating the transported bases does not work: with `(A u)(γ) = u(α)` and
        `(B v)(γ) = v(σ)` one gets `⟪A u, B v⟫ = (∑_α u α)(∑_σ v σ) ≠ 0`.
        **Resolved — the blocker is avoidable.**  `IsGaussianHilbert (K_block)` is not
        actually needed.  All three of `skL.U`, `skN.U`, `skM.U` are `IsGaussianHilbert` by
        hypothesis, and `K_interpol t` is a *linear image* of that triple
        (`K_interpol t ω = √t · skL.U ω + √(1-t) · (A (skN.U ω) + B (skM.U ω))`), so apply the
        IBP lemma to the **packaged triple** instead of to the pair `(skL.U, K_block)`.
        Nothing needs diagonalising and the spectral theorem is not required.
        What is needed instead: generalise RSAT's `isGaussianHilbert_UV` from its special
        form (`SKDisorder` × `SimpleDisorder`, both at size `N`) to two arbitrary independent
        `IsGaussianHilbert` vectors in possibly different Hilbert spaces, then nest once for
        the triple.  Its proof is already generic in substance (it opens with
        `let hU := sk.hU; let hV := sim.hV` and uses only those plus independence, never
        `cov_eq`), so this is a mechanical generalisation, not new mathematics.  (M, not L.)
  - [ ] trace reduction and sign argument (adapt `port/GuerraTrace.lean` +
        `cov_deriv_*` + `hessian_free_energy_std_basis_offdiag_nonpos`). (M)
- [ ] **1c** `free_entropy_tendsto`: plug 1a, 1b into `free_entropy_tendsto_of_bddAbove`. (S)
- [ ] Remove the `hmono`/`hbdd` hypotheses from the ported file's final theorems.

**Deliverable:** first unconditional theorem of the project; announce on Zulip.

## Phase 2 — Milestone 2: the Parisi functional  (M–L)

- [x] Port `port/ParisiOperator.lean` (operator `T_{m,v}`, semigroup law) to Lean 4.32.
      **Done**, as `ParisiFormula/ParisiOperator.lean`.  The 4.28 → 4.32 gap turned out to
      be *zero renames*: the only change needed was adding
      `import Mathlib.MeasureTheory.Integral.Prod` (`Integral.Bochner.Basic` does not pull
      in `integral_prod`).  `Measure.conv`, the `∗` notation and
      `gaussianReal_conv_gaussianReal` all survive unchanged.
- [x] Reconcile `Targets.parisiStep` with `Parisi.T`.  **Done**, as
      `Targets.parisiStep_eq_T`, via `integral_comp_sqrt_mul_gaussianReal` in
      `ParisiFormula/GaussianCosh.lean`.
      **The parenthetical suggestion here was wrong**: `parisiStep` must *not* be defined via
      `T`.  `Parisi.T` has no `m = 0` branch, so `T 0 v A x = (1/0) * log (…) = 0`, whereas
      `parisiStep 0 v A x = ∫ A (x + √v z) dγ` is the `m → 0` limit.  The `m = 0` branch is
      the outermost step `F₀ = T_{0, β²q₁} F₁` of the recursion, so collapsing it to `0`
      would break `parisiFunctional` and Target 2a.  The two agree exactly when `m ≠ 0`.
- [x] **2a** `parisiFunctional_rsScheme` — sanity check of normalisations. **Done.**
      The definitions are correct as written: the `parisiF` off-by-one fixed in `fa63079`
      is right, and the statement holds for *all* real `β` (no `0 < β` needed), because
      `√(β² q) = |β| √q` agrees with `β √q` under the symmetric Gaussian
      (`integral_reflect_stdGaussian`).  Supporting lemmas are in
      `ParisiFormula/GaussianCosh.lean`.
- [x] Moderate-growth / integrability lemmas for `parisiF` at every level. **Done.**
      `HasLinearGrowth` (`ParisiFormula/GaussianCosh.lean`) is the right invariant:
      `hasLinearGrowth_log_cosh` for the base, `Targets.hasLinearGrowth_parisiStep` for the
      step, and `integrable_of_hasLinearGrowth` / `integrable_exp_mul_of_hasLinearGrowth` for
      the two integrability side conditions.  `Targets.parisiF_props` packages these with
      measurability and 1-Lipschitzness as a simultaneous induction over levels.

- [ ] **BLOCKER for the variance-change assembly: `Parisi.T_add` is unusable as ported.**
      It assumes `HasUniformBound A := ∃ C, ∀ x, |A x| ≤ C`, but the Parisi recursion is
      *not* uniformly bounded — its base `log cosh y` grows like `|y|`, and every level
      inherits linear growth, not boundedness.  So the semigroup law, which is the natural
      route for factoring a change of `q_p` as an extra smoothing step
      (`T_{m,v'} = T_{m,v} ∘ T_{m,v'-v}`), does not apply.
      **Fix:** re-prove `T_add` under `HasLinearGrowth` instead.  The proof structure
      (Gaussian convolution + Fubini) should carry; the two appeals to
      `integrable_exp_mul_of_measurable_of_hasUniformBound` become
      `integrable_exp_mul_of_hasLinearGrowth`, and the Fubini step needs product-measure
      integrability, which follows from `exp (a|p₁ + p₂|) ≤ exp(a|p₁|) exp(a|p₂|)` and
      `integrable_exp_abs_mul_stdGaussian` on each factor.  (M)
- [x] **2b-i** Continuity in `(m,q)` at fixed `k`, compactness, and existence of a
      minimiser — Talagrand's (2.17).  **DONE**, `sorry`-free
      (`Targets.exists_minimizer_parisiFunctional`).  This is the regularity the Annals proof
      actually consumes; see the correction from Talagrand's text below.
- [ ] **2b-ii** The uniform-in-`k` Lipschitz bound (`parisiFunctional_lipschitz`). (L) —
      Guerra's route, needed only to extend `𝒫` to general measures on `[0,1]`, which
      Talagrand explicitly avoids.  **Off the critical path.**  No longer blocked either: the
      note below records a derivative-free argument giving `0 ≤ ψ'(m) ≤ 2v` for all `β`.
      It previously read `∀ k, ∃ C, ∀ s s'`, allowing the constant to depend on `k`, which
      cannot control `parisiValue = inf_k inf_{(m,q)} 𝒫_k`: nothing survives the infimum over
      all `k` unless `C` is uniform in `k`.  `∃ C` is now hoisted outside `∀ k`.  Under the
      Talagrand route this target is **load-bearing** (the induction on RSB levels needs
      regularity of `𝒫_k` in the parameters), not optional.
      The `ℓ¹` form of the right-hand side should still be checked against Talagrand when the
      Milestone 4 blueprint is written; the uniformity in `k` is not negotiable.
      Proof route (partly built): `parisiStep` is non-expansive in the sup-norm of its
      argument (`Targets.parisiStep_dist_le`, uniformly in `m`), which propagates a parameter
      perturbation through the backward recursion level by level; a change of `q_p` is
      factored as an extra smoothing step by the semigroup law
      (`Parisi.T_add_of_hasLinearGrowth`) and bounded by
      `Targets.abs_parisiStep_sub_self_le`.

      **Open question about the statement — the modulus in `q` may be wrong.**
      `abs_parisiStep_sub_self_le` gives
      `|T_{m,w} A - A| ≤ L √w 𝔼|Z| + |m| L² w / 2`, whose leading term is **`√w`**, not `w`.
      Chained over levels that yields a **1/2-Hölder** modulus in `q`, not the Lipschitz
      bound 2b currently asserts.  The `√` is *sharp* for a merely Lipschitz `A`: for
      `A = |·|` at `x = 0`, `∫ |√w z| dγ = √w 𝔼|Z|` exactly.  So this is not an artefact of
      the proof.

      Lipschitz-in-`q` requires the first-order term to vanish and **second-derivative**
      control: `∫ A (x + √w z) dγ - A x = (w/2) A''(x) + O(w²)` for `A ∈ C²` with bounded
      `A''`.  The levels `F_p` *are* smooth (they are Gaussian smoothings), so this is
      available in principle, but it needs a bound on `F_p''` propagated through the
      recursion as an extra invariant alongside
      `Targets.parisiF_props` — which has not been built.

      **Decision taken: (ii), keep Talagrand's Lipschitz form.**  The second-derivative
      invariant is now built and verified — see `ParisiFormula/GaussianCosh.lean` §§9–15:
      `HasParisiC2` (`0 ≤ A'' ≤ 1 - (A')²`), preserved by the smoothing step
      (`Targets.hasParisiC2_parisiStep`), giving `|A''| ≤ 1` uniformly in the level and in
      `k`, and hence the improved estimate
      `abs_integral_shift_sub_le_second : |∫ A (x + √w z) dγ - A x| ≤ w` — order `w`, not
      `√w`.  The **`q`-perturbation half of 2b is therefore unblocked.**

### The `m`-perturbation: boundary case settled (2026-09-04)

Writing `ψ(m) = T_{m,v} A (x) = (1/m) log 𝔼[e^{mY}]` with `Y = A(x + √v Z)`:

  `dψ/dm = (⟨Y⟩_m - ψ(m)) / m`,   hence   `|dψ/dm| ≤ ½ · sup_{u ∈ [0,m]} Var_u(Y)`,

`⟨·⟩_u`, `Var_u` in the tilted measure `∝ e^{uY} dγ`.  The tilted-variance route was tried
and **abandoned**: our invariant gives `A'' ≥ 0`, so the tilted log-density
`u A(x + √v z) - z²/2` is concave only while `uv < 1`; Brascamp–Lieb then gives
`Var_u ≤ v/(1 - uv)`, degenerating as `uv → 1`.  Since `v = β²(q_{p+1} - q_p)` can be as
large as `β²`, that silently imposes `β² < 1` — unacceptable, 2b must hold for all `β`.

**Settled instead by a two-sided sandwich at the `m = 0` boundary**, which is where the
difficulty actually sits (`parisiStep` *branches* at `m = 0`, and Talagrand's (1.6) allows
`m_0 = 0`).  For `A` 1-Lipschitz of linear growth, `0 < m`, `0 ≤ v`:

  `parisiStep 0 v A x ≤ parisiStep m v A x ≤ parisiStep 0 v A x + m·v/2`

— `Targets.parisiStep_zero_sandwich`, from two Tier-2 lemmas in
`ParisiFormula/GaussianConcentration1D.lean`:

```
integral_le_inv_mul_log_integral_exp   𝔼[f] ≤ (1/m) log 𝔼[exp(m f)]          (Jensen)
inv_mul_log_integral_exp_le            (1/m) log 𝔼[exp(m f)] ≤ 𝔼[f] + m L²/2  (Herbst)
```

Both are **uniform in `x`** (the constant is the Lipschitz constant `L = √v`, never
`sup |A|`, which is infinite for `log cosh`) and **linear in `m`**, so they survive
summation over the `k+2` levels with a constant independent of `k`.  This is exactly why the
sub-Gaussian form of Herbst is needed: the naive `𝔼[exp(a|Z|)] ≤ 2 exp(a²/2)` contributes
`(log 2)/m`, which blows up as `m → 0`.

**What remains for a full Lipschitz-in-`m`.**  The sandwich is anchored at `0`, and that is
genuinely all it gives: the same computation for general `0 ≤ m' ≤ m` yields
`0 ≤ ψ(m) - ψ(m') ≤ m·v/2` (via `ψ` nondecreasing), a bound in `m`, *not* in `|m - m'|`.
Chord-slope algebra confirms this is not an artefact — writing `g(m) = log 𝔼[e^{mY}]`,

  `ψ(m) - ψ(m') = ((m - m')/m)·(h - ψ(m'))`,  `h` the chord slope of `g` on `[m', m]`,

and `h - ψ(m')` is *not* bounded uniformly as `m' → m` by the sandwich alone.

A genuine Lipschitz bound therefore needs `ψ'`, but — and this is the useful new
observation — it needs only **convexity of `g` plus the sandwich**, no Brascamp–Lieb and no
constraint on `β`:

* `g` is convex (Hölder) with `g(0) = 0`, so `⟨Y⟩_m = g'(m) ≥ (g(m) - g(0))/m = ψ(m)`;
* `g'(m) ≤ (g(2m) - g(m))/m ≤ (2m·𝔼Y + 2m²σ² - m·𝔼Y)/m = 𝔼Y + 2mσ²`, using
  `g(m) ≥ m𝔼Y` (Jensen) and `g(2m) ≤ 2m𝔼Y + 2m²σ²` (Herbst);
* hence `0 ≤ ⟨Y⟩_m - ψ(m) ≤ 2mσ²`, i.e. **`0 ≤ ψ'(m) ≤ 2σ² = 2v`**, uniformly in `x`.

So `|ψ(m) - ψ(m')| ≤ 2v·|m - m'|`, for all `β`.  The remaining Lean work is to differentiate
`m ↦ (1/m) log ∫ exp(m·A(x + √v z)) dγ` under the integral (the parametric-integral
machinery for the *`x`*-derivative is already built in `GaussianCosh.lean` §§10–13 and
transfers) and assemble the three bullets.  **(M, no longer blocked.)**

### A correction to this target, from Talagrand's text (read 2026-09-04)

The Annals paper was read directly.  Talagrand **does not prove, and does not use, a global
Lipschitz estimate in `(m, q)`.**  Explicitly, after (1.13):

> "Guerra proves that this definition can be extended by a continuity argument to any
> probability measure µ on [0,1] … *We do not adopt this point of view since an essential
> ingredient of our approach is that we need only consider discrete objects rather than
> continuous ones.*"

What his proof actually needs from the parameter dependence is:

1. **(2.17) — existence of a minimiser**, by *compactness*: "The existence of `m` and `q`
   satisfying (2.17) is obvious by a compactness argument. It is to permit this compactness
   argument that equality is allowed in (1.6) and (1.7)."  This needs **continuity of
   `𝒫_k` in `(m,q)` on the compact admissible set for fixed `k`** — not a modulus, and not
   uniformity in `k`.
2. **Partial derivatives at the minimiser** (§5, Lemma 5.8 and Prop. 5.5): the proof of
   Theorem 2.2 extracts information from the vanishing/sign of `∂/∂λ` and `∂/∂m` of the
   right-hand side of (5.20) *at* the minimising `(m, q)`.

Consequently `parisiFunctional_lipschitz` as stated is **Guerra's route, not Talagrand's**,
and the ROADMAP's claim that "2b is load-bearing for the induction on RSB levels" was wrong:
the induction consumes (2.17), i.e. minimiser existence.

**Restatement of Milestone 2b to match the source:**

* **2b-i (what Talagrand needs) — PROVED (2026-09-04).**  For fixed `k`, `(m,q) ↦ 𝒫_k(m,q)`
  is continuous on the compact set of admissible schemes, hence attains its minimum:
  `Targets.exists_minimizer_parisiFunctional`, verified `sorry`-free by `#print axioms`
  (only `propext`, `Classical.choice`, `Quot.sound`).  The chain is

  - `admissible k` — the constraints plus `[0,1]`-valued, a *closed* subset of a product of
    copies of `[0,1]`, hence compact by Tychonoff (`isCompact_admissible`).  Closed exactly
    because (1.6)–(1.7) use `≤`, which is Talagrand's own remark.
  - `continuousWithinAt_parisiFRaw` — every level is continuous in the parameters, by
    induction.  The step evaluates level `j` at the *moving* point `y + √(v p) z`;
    equi-Lipschitzness turns fixed-point continuity into moving-point continuity, and
    dominated convergence along `𝓝[admissible k] p₀` moves the limit through the integral.
  - the `m = 0` branch point is split off: for `m p₀ > 0` both sides take the `else` branch,
    and for `m p₀ = 0` the two branches are compared at the *same* parameter by
    `parisiStep_zero_sandwich`, whose gap `m p · v p / 2` vanishes as `m p → 0`.
  - `IsCompact.exists_isMinOn` finishes.
* **2b-ii (Guerra's extension, optional).**  The uniform-in-`k` Lipschitz bound currently
  stated as `parisiFunctional_lipschitz`.  Needed only to extend `𝒫` from discrete schemes
  to general probability measures `µ` on `[0,1]` — which Talagrand explicitly avoids.  Keep
  it stated, but **off the critical path**.

### RSAT already has the right architecture (found 2026-09-04)

Now that the project depends on RSAT rather than vendoring eight files out of it, the
following is available and fully proved, in
`Lemmas/GuerraTalagrand/Gaussian.lean`:

```
structure GoodFam (F D : P → ℝ → ℝ × ℝ → ℝ) : Prop where
  contF     : Continuous fun w : P × ℝ × (ℝ × ℝ) => F w.1 w.2.1 w.2.2
  contD     : Continuous fun w : P × ℝ × (ℝ × ℝ) => D w.1 w.2.1 w.2.2
  hasDeriv  : ∀ p l x, HasDerivAt (fun l' => F p l' x) (D p l x) l
  lipx      : ∀ p l x y, |F p l x - F p l y| ≤ |x.1 - y.1| + |x.2 - y.2|
  bddD      : ∀ p l x, |D p l x| ≤ 1
```

with `step0 μ α β F p λ x = ∫ z, F p λ (x.1 + α p z, x.2 + β p z) ∂μ` (the `m = 0` branch)
and `stepM μ m α β F p λ x = (1/m) log ∫ exp (m F p λ (…)) ∂μ` (the `m ≠ 0` branch, `0 < m`)
— **exactly the two branches of `Targets.parisiStep`** — and theorems `step0_good`,
`stepM_good` that **both steps preserve goodness**, given a probability measure with all
exponential moments (`GTFrame.ExpMoments`).

**Consequences.**

1. The `m`-perturbation should be attacked as *joint continuity in a parameter space* `P`,
   which `contF`/`contD` carry through the recursion by dominated convergence, **not** by
   differentiating in `m` and bounding a tilted variance.  That is what removes the
   `β² < 1` obstruction above: no tilted-variance bound is needed.
2. Much of `ParisiFormula/GaussianCosh.lean` duplicates RSAT: `ExpMoments` is our
   `integrable_exp_abs_mul_*`; `lipx_step0`/`lipx_stepM` are our `parisiStep_lipschitz`;
   `bddD_*` are our `HasParisiC2.abs_*`; `fLbaseDD lam x = 1 - (fLbaseD lam x)^2` is our
   second-order invariant, in the same form.
3. The remaining gap is that RSAT's framework is built for a *two-replica* spatial variable
   `ℝ × ℝ` with a distinguished λ, while `parisiF` is one-dimensional with parameters
   `(m,q)`.  So this is an **instantiation/adaptation job**, not new mathematics.

**Recommended plan for 2b:** restate it as joint continuity (and then Lipschitz) in the
scheme parameters, and instantiate RSAT's `GoodFam` / `step0_good` / `stepM_good` rather than
carrying our own hand-rolled invariant.  (M, and mostly bookkeeping.)

## Phase 3 — Milestone 3: Guerra's RSB bound  (L–XL)

**Blocker found (CI run 33823189093).**  The four `port/` Guerra files cannot be compiled
against this project: they were cut from **or4nge19/SpinGlass** `d1342fd`, whereas
`Lemmas/SpinGlass/` is vendored from **njimaMath/research_public** (RSAT) `f3b34d2`, a
trimmed fork.  They reference or4nge19 API that RSAT never vendored — the whole
`FiniteGibbs` namespace, `SKDisorder.measU`/`SimpleDisorder.measV`, `disorderPair`,
`abs_free_energy_density_le`, `integrable_norm_of_isGaussian_map`, `norm_dH_t_le_on_ball`.
Vendoring the or4nge19 modules alongside would collide in the shared `SpinGlass` namespace.
So Phase 3's k = 0 case must be **rebuilt on RSAT's API**, not ported.  RSAT already supplies
`H_t`, `hasDerivAt_H_t`, `hasDerivAt_nu`, `trace_formula`, `trace_sk`, `trace_simple` and
`guerra_derivative_bound_algebra`; the missing link is the Gaussian-IBP step from the
derivative of `∫ free_energy_density (H_t ·)` to the trace expression.  See `port/README.md`.


- [ ] Finite Gaussian tree: the field `∑ᵢ σᵢ ∑_p z_p^i √(β²(q_{p+1}-q_p))` as an
      `IsGaussianHilbert` vector in `EnergySpace N`, with its covariance kernel. (L)
- [ ] Hierarchical expectation `Z_p = (E_p Z_{p+1}^{m_p})^{1/m_p}` and endpoint `φ(0)`. (L)
- [ ] Derivative `φ'(t)` via Gaussian IBP and positivity of each term. (XL)
- [ ] **3** `guerra_rsb_bound`; **3'** `limsup_free_entropy_le_parisiValue`.

## Phase 4 — Milestone 4: Talagrand's lower bound  (XL, open-ended)

**Route decision (fixed): Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006).**
Panchenko's route is explicitly **out of scope for now**.  This is a deliberate narrowing,
and it prunes a large branch of prerequisites — we do **not** need any of:

* the Ghirlanda–Guerra identities,
* ultrametricity of the overlap (a major theorem in its own right),
* Ruelle probability cascades / Poisson–Dirichlet,
* the Aizenman–Sims–Starr scheme.

What Talagrand's route *does* require, on top of Milestone 3:

* the overlap-constrained two-replica partition function
  `Z_N(u) = ∑_{R(σ¹,σ²)=u} exp(-H(σ¹)-H(σ²))`;
* the Guerra–Talagrand interpolation for that coupled system, with a Lagrange multiplier
  conjugate to the constraint;
* induction on the number of RSB levels `k`, using **convexity/regularity of the `k`-step
  functional in the coupling parameter**;
* Gaussian concentration of the free energy — **already available**, as
  `gaussian_lipschitz_concentration` in `Lemmas/SpinGlass/gaussian_concentration.lean`.

**Consequence for sequencing:** Target 2b (Lipschitz continuity of `parisiFunctional` in the
scheme) is *load-bearing* for this route, not a nice-to-have, because the induction needs
regularity in the parameters.  Its statement in `Targets/Milestones.lean` is currently
marked provisional and should be pinned down before Phase 4 starts.

Note: the starting point named below is **not in this repository** — `grep` finds no
`SpinGlass.AT.twoReplica_GT_bound`; it exists in RSAT upstream and would have to be vendored
(and reconciled with the fork mismatch described in `port/README.md`).

Blueprint chapter still to be written after Phase 3.  Prior starting point: RSAT's
`SpinGlass.AT.twoReplica_GT_bound` (the RS-level coupled-replica bound).

## Correctness of the goal statement — **fixed**

- [x] `parisiValue` is `sInf` of the set of finite-step functionals.  Mathlib sends `sInf`
      of a set that is not bounded below to the junk value `sInf ∅ = 0`
      (`csInf_of_not_bddBelow`), so **Target 4 was asserting convergence to `0`** unless
      that set is bounded below.  Now proved in `Targets/Milestones.lean`:
      `parisiFunctional_ge : log 2 - β²/4 ≤ 𝒫_k(m,q)` uniformly in `k`, hence
      `bddBelow_parisiSet`, `parisiSet_nonempty`, `parisiValue_le`, `parisiValue_ge`.
      `parisiValue_le` is the form Target 3' consumes.

## Housekeeping (any time)

- [ ] Set up `leanblueprint` so `blueprint/blueprint.tex` renders as a website with the
      dependency graph.
- [ ] Consider upstreaming the Gaussian IBP lemmas to Mathlib (general-purpose).
- [ ] Decide whether to keep the `Lemmas.SpinGlass` module names (zero-diff vendoring)
      or rename to `ParisiFormula.Core.*` (cleaner, but touches every import).
