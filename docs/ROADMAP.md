# Roadmap

## Critical path to the goal

**Goal: Talagrand's proof of the Parisi formula (Ann. of Math. 163 (2006)) — Target 4.**

Target 4 is `Tendsto (fun N => s_N) atTop (𝓝 (parisiValue β h))`, which follows from

* **limsup ≤** — Target 3', proved from Target 3 (Guerra's RSB bound) and the now-complete
  SK-model Theorem 2.1; and
* **liminf ≥** — Talagrand's coupled-replica lower bound (Milestone 4), whose induction on
  the number of RSB levels needs **Target 2b-i** (continuity of `𝒫_k` in the parameters for
  fixed `k`, hence existence of a minimiser — Talagrand's (2.17)). **2b-i is proved**;
  Theorem 2.2, the coupled-replica convergence argument, remains open.

**Current critical path: prove `talagrand_theorem_2_2`.** Theorem 2.1, Targets 3 and 3',
the minimizer, and `parisiValue` well-definedness are proved. `parisi_formula` is already
deduced from these results and Theorem 2.2. The axiom guards in `Targets/GuerraAudit.lean`
verify that Theorem 2.1 and the upper bounds have no placeholder dependencies.

The convergence deduction within Theorem 2.2 is now proved in
`Targets/TalagrandConvergence.lean`, conditional on an explicit mass-weighted
overlap-concentration estimate. The next missing input is that concentration estimate,
not the differential-inequality argument. The unconditional Theorem 2.2 remains open.

The unrestricted coupled cascade and both identities in Lemma 2.7 are now proved in
`Targets/CoupledCascade.lean`. `Targets/ReplicaMeasure.lean` identifies the individual
replica probabilities with the components of the existing remainder. The next work is
the overlap-constrained pressure, Lemma 2.6 / Proposition 2.5, and Theorem 2.4; see Step 14.

**Milestone 1 (Targets 1b, 1c) is *not* on this critical path.**  Target 4 is strictly
stronger than 1c — convergence to `parisiValue` subsumes existence of a limit — and deriving
4 from 3' plus the lower bound never invokes 1c.  Milestone 1 is the classical
Guerra–Toninelli (2002) result and exercises related interpolation and Gaussian-IBP
machinery, but work there should not be mistaken for completing Theorem 2.2. The current
deduction of `parisi_formula` does not use the separate thermodynamic-limit target.

The completed Theorem 2.1 uses the local coordinate Stein lemmas and finite cascade
modules. The older Gaussian-triple packaging plan below belongs to Target 1b, not to the
current lower-bound task.

The phases below retain development history as well as current status. Main statements
live in `Targets/Milestones.lean` and `Targets/Talagrand.lean`; the current file map is in
`README.md`. Historical effort estimates are rough (S = hours, M = days, L = weeks,
XL = months), not promises for the remaining proof.

## Phase 0 — make the skeleton build  (S–M)  — **done**

- [x] `lake build` succeeds for the default local library, `ParisiFormula`, and its
      dependencies. `lake exe cache get` supplies the prebuilt Mathlib cache.
- [x] `lake build ParisiFormula` succeeds. Three repairs were needed after all
      (`Fin.addCases_castAdd_natAdd` is now pointwise; two `simpa`s that no longer close
      their goals). See `docs/PROVENANCE.md`.
- [x] `lake build Targets` succeeds, including `Targets.GuerraAudit`; four explicit
      proof placeholders remain, with warnings rather than build errors.
- [x] CI (`.github/workflows/build.yml`) is configured to require both library builds;
      target/audit failures are no longer tolerated. `bash scripts/check.sh` does the
      same locally and reports remaining proof holes.

Elaboration alone does not validate the intended mathematical statement:
`parisiFunctional` typechecked both before and after an off-by-one in the `parisiF` index
was corrected. The now-proved Target 2a checks the RS normalization; axiom guards check
proof dependencies, not whether a specification matches the paper.

## Phase 1 — Milestone 1: the thermodynamic limit  (M–L)

This is an off-path, unfinished development. Its older implementation plan is retained
for reference; it is not the next step for the Parisi formula.

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
  - [ ] **Historical Gaussian-packaging obstacle; alternative not yet assembled.**
        The original plan requested `IsGaussianHilbert (K_block …)`. The IBP lemma needs
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

**Optional deliverable:** a standalone Guerra–Toninelli proof of limit existence.

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

- [x] **Resolved: extend the bounded-function semigroup law to linear growth.**
      It assumes `HasUniformBound A := ∃ C, ∀ x, |A x| ≤ C`, but the Parisi recursion is
      *not* uniformly bounded — its base `log cosh y` grows like `|y|`, and every level
      inherits linear growth, not boundedness.  So the semigroup law, which is the natural
      route for factoring a change of `q_p` as an extra smoothing step
      (`T_{m,v'} = T_{m,v} ∘ T_{m,v'-v}`), does not apply.
      **Done:** `Parisi.T_add_of_hasLinearGrowth` in
      `ParisiFormula/ParisiOperatorGrowth.lean`, using Gaussian convolution, Fubini,
      and exponential integrability on the product measure.
- [x] **2b-i** Continuity in `(m,q)` at fixed `k`, compactness, and existence of a
      minimiser — Talagrand's (2.17).  **DONE**, `sorry`-free
      (`Targets.exists_minimizer_parisiFunctional`).  This is the regularity the Annals proof
      actually consumes; see the correction from Talagrand's text below.
- [ ] **2b-ii** The uniform-in-`k` Lipschitz bound (`parisiFunctional_lipschitz`). (L) —
      Guerra's route, needed only to extend `𝒫` to general measures on `[0,1]`, which
      Talagrand explicitly avoids.  **Off the critical path.**  No longer blocked either: the
      note below records a proposed convexity-and-concentration argument giving
      `0 ≤ ψ'(m) ≤ 2v` for all `β`.
      It previously read `∀ k, ∃ C, ∀ s s'`, allowing the constant to depend on `k`, which
      cannot control `parisiValue = inf_k inf_{(m,q)} 𝒫_k`: nothing survives the infimum over
      all `k` unless `C` is uniform in `k`. `∃ C` is now hoisted outside `∀ k` in this
      legacy target. It is **not used** by the current Talagrand deduction: fixed-`k`
      continuity and existence of a minimizer (2b-i) supply the required regularity.
      Proof route (partly built): `parisiStep` is non-expansive in the sup-norm of its
      argument (`Targets.parisiStep_dist_le`, uniformly in `m`), which propagates a parameter
      perturbation through the backward recursion level by level; a change of `q_p` is
      factored as an extra smoothing step by the semigroup law
      (`Parisi.T_add_of_hasLinearGrowth`) and bounded by
      `Targets.abs_parisiStep_sub_self_le`.

      **Historical obstacle, resolved by second-derivative control below.**
      `abs_parisiStep_sub_self_le` gives
      `|T_{m,w} A - A| ≤ L √w 𝔼|Z| + |m| L² w / 2`, whose leading term is **`√w`**, not `w`.
      Chained over levels that yields a **1/2-Hölder** modulus in `q`, not the Lipschitz
      bound 2b currently asserts.  The `√` is *sharp* for a merely Lipschitz `A`: for
      `A = |·|` at `x = 0`, `∫ |√w z| dγ = √w 𝔼|Z|` exactly.  So this is not an artefact of
      the proof.

      Lipschitz-in-`q` requires the first-order term to vanish and **second-derivative**
      control: `∫ A (x + √w z) dγ - A x = (w/2) A''(x) + O(w²)` for `A ∈ C²` with bounded
      `A''`.  The levels `F_p` *are* smooth (they are Gaussian smoothings), so this is
      available, but it needs a bound on `F_p''` propagated through the
      recursion as an extra invariant alongside
      `Targets.parisiF_props`.

      **Decision taken: retain the legacy Lipschitz target off-path.** The second-derivative
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

**Outcome for 2b-i:** joint continuity and the fixed-level minimizer are now proved in
`Targets/Milestones.lean`. The preceding framework comparison records the investigation,
not a pending prerequisite. The separate uniform Lipschitz target remains off-path.

### Historical checkpoint before completion of Theorem 2.1 (2026-09-04)

The following engine assessment predates the completed cascade proof below; its
recommended order is superseded by the current critical path at the top of this file.
At that checkpoint, five `sorry`s remained:

| target | statement | on critical path? |
|---|---|---|
| 1b | `Φ_monotoneOn` | no — but see below |
| 1c | `free_entropy_tendsto` | no |
| 2b-ii | `parisiFunctional_lipschitz` | no (Guerra's route) |
| **3** | **`guerra_rsb_bound`** | **yes** |
| 4 | `parisi_formula` | yes |

**The structural point: 1b and 3 share one missing engine.**  Everything around them is
already proved —

* `guerra_toninelli_superadditive` takes monotonicity as a *hypothesis*, so all of
  Milestone 1 downstream of `Φ_monotoneOn` is done;
* the endpoints (`Z_interpol_zero`, `Z_interpol_one`) are done;
* the *sign* of the covariance–Hessian trace is done (`covDiff_diag`, `covDiff_nonpos`,
  `covDiff_hessian_sum_nonneg` in `InterpolationDeriv.lean`);
* for Target 3, RSAT proves the general Guerra derivative identity for an arbitrary `xi`
  (`guerra_derivative_bound_algebra`), together with `trace_formula` and `trace_sk`.

What neither has is the **Gaussian interpolation derivative formula**

  `d/dt 𝔼[log Z(H_t)] = ½ ∑_{σ,τ} (C₁ - C₀)(σ,τ) · 𝔼[Hess log Z(H_t)](e_σ, e_τ)`,

i.e. differentiating under the expectation and identifying the derivative by Gaussian
integration by parts.  Mathlib has no Gaussian comparison theorem (no Slepian, no
Sudakov–Fernique, no interpolation formula), so this cannot be short-circuited.

**Recommended order at that checkpoint (superseded).** Prove the engine in the *simpler* of its two settings first —
Target 1b, where the interpolation is between two fields on the same space and no cascade is
involved — then reuse it for Target 3, where the comparison field is the RSB cascade.  1b
also closes Milestone 1: 1c is explicitly "assembles 1a and 1b with the already-formalised
Fekete argument `free_entropy_tendsto_of_bddAbove`".

**Stage 1 of 1b is now de-risked.**  The blocker recorded in `InterpolationDeriv.lean` was
packaging the disorder triple as one `IsGaussianHilbert` vector.  Two library facts, found
today, make this much shorter than RSAT's hand-rolled ~250 lines:

* `OrthonormalBasis.prod` (`Mathlib/Analysis/InnerProductSpace/ProdL2.lean`) supplies the
  product basis on `WithLp 2 (H₁ × H₂)` indexed by `ι₁ ⊕ ι₂`, with an explicit `prod_apply`;
* `ProbabilityTheory.iIndepFun_uncurry` is the combinator turning "the two families are
  independent of each other" plus "each is internally independent" into independence of the
  combined family — the single lemma RSAT's long setup builds towards.

See the expanded note at the end of `ParisiFormula/InterpolationDeriv.lean` for the target
shape of `isGaussianHilbert_prod`.  The genuinely new work is porting RSAT's derivation that
the two coordinate families are independent of each other (`Replicas.lean` 107–213).

**Remaining stages of 1b after that:** nest the pair to a triple; differentiate `Φ` under the
expectation with a dominating bound; apply the IBP lemma and `trace_formula`; conclude from
`covDiff_hessian_sum_nonneg` plus continuity on `Icc 0 1`.  Estimated 600–800 lines total.

## Phase 3 — Milestone 3: Guerra's RSB bound — done for the SK model

### `k = 0` is DONE (2026-09-04)

`Targets.guerra_rs_bound`, `sorry`-free:

    interpolatedPressure N β h q sk sim 1 ≤ parisiFunctional (rsScheme q) β h

the finite-volume SK pressure is at most the replica-symmetric Parisi functional, for every
`N`, every `(β,h)` and every `q ∈ [0,1]`, with no `O(1/N)` error.

It did **not** need the interpolation engine to be built: RSAT already has it for the
single-Gaussian comparison field — `pressure_derivative` (differentiation of the pressure
along the smart path), `pressure_derivative_ibp_trace` (Gaussian IBP), `endpoint_pressure`,
assembled as `replica_symmetric_sum_rule`.  Combining that with our Target 2a
(`parisiFunctional_rsScheme`) and `overlapVariance_nonneg` gives the bound in a few lines.
The two closed forms match exactly (`rsPressure_eq_parisiFunctional`).

This earlier RS-only checkpoint is now superseded by the full finite cascade proof below.
The separate Guerra–Toninelli path of Target 1b remains outside the active critical path.

### The proof structure is now in Lean (2026-09-04) — `Targets/Talagrand.lean`

A re-evaluation: building the cascade derivative bottom-up, lemma by lemma, without the
proof structure in Lean was the wrong order.  Talagrand's §2 is now formalised top-down, and
**Targets 3 and 4 are derived — machine-checked — from the paper's two analytic cores**:

| item | Lean | status |
|---|---|---|
| (2.1)–(2.4) `φ(t)` | `guerraPhi` (base `guerraBase` pushed through `cascadeT`) | defined |
| (2.18) `ψ(t)` | `guerraPsi`; `ψ(1) = 𝒫_k` on the nose | proved |
| (2.14) `φ(0) = log 2 + X_0` | `guerraPhi_zero` | proved, axiom-clean |
| `φ(1) =` free entropy | `guerraPhi_one` | proved, axiom-clean |
| **Theorem 2.1** Guerra's identity (SK) | `guerra_identity` | **proved, axiom-clean** |
| **Theorem 2.2** | `talagrand_theorem_2_2` | **`sorry`** — core 2 |
| (2.12)–(2.15) Target 3 | `guerra_rsb_bound` | proved, axiom-clean |
| Target 3′ | `limsup_free_entropy_le_parisiValue` | proved, axiom-clean |
| **Theorem 1.1 = Target 4** | `parisi_formula` | **derived from cores 1 + 2 + 2b-i** |

`#print axioms` confirms that Theorem 2.1 and both upper bounds use only `propext`,
`Classical.choice`, and `Quot.sound`. `parisi_formula` still depends on `sorryAx` through
Theorem 2.2. The three legacy placeholders in `Targets/Milestones.lean` are not used by
this deduction.
The deduction of Theorem 1.1 is exactly the paper's (pp. 229–230): `|φ'| ≤ L` from core 1
gives `φ_N(1) ≥ φ_N(t₀) - L(1-t₀)`, core 2 gives `φ_N(t₀) → ψ(t₀) ≥ 𝒫`, and `t₀ < 1` is
arbitrary; the upper half is Target 3′.

**The current SK Parisi formula is now formalised modulo Theorem 2.2 alone.**

#### Core 1 — `guerra_identity` (Theorem 2.1)

`φ'(t) = -parisiCorrection - Rem(t)` on `(0,1)` with `0 ≤ Rem ≤ β²`, plus continuity on
`[0,1]`.  Ingredients already built in `Targets/CascadeDeriv.lean`:

* the tilted (Gibbs) chain rule through one level, `hasDerivAt_parisiStep_param`, with both
  branches of `parisiStep` unified by `tiltWeight`;
* the growth bounds that let it chain — `tiltWeight_le`, `integral_abs_mul_tiltWeight_le`,
  `abs_integral_mul_tiltWeight_le` — which required identifying Lipschitzness as the
  load-bearing hypothesis (without it the tilted moment is not bounded uniformly in `x`).

**Recovery checkpoint (2026-09-04, after Claude step 8).**  The parameter chain is now
implemented through all `k+2` levels, including differentiation under the outer disorder
expectation (`hasDerivAt_guerraPhi`).  The line-derivative form of Gaussian IBP is also wired
to the cascade:

* `stein_coord_of_hasDerivAt` and `stein_inner_of_hasDerivAt` need only one-dimensional line
  derivatives, not a Fréchet-`C¹` cascade functional;
* `guerraBaseUDeriv`, `guerraUD`, and `hasDerivAt_cascade_Uline` propagate a disorder
  direction through every level, with a depth-uniform bound and joint measurability;
* `guerra_cascade_stein` is the first end-to-end covariant Stein identity for the top
  cascade, with all integrability obligations discharged from affine Gaussian growth.

**Step 10 (2026-09-04): disorder IBP for the first derivative.**  The next part of
Talagrand's Theorem 2.1 is implemented without new `sorry`s:

* `Targets/CascadeSecondPi.lean` proves the normalized tilted-average derivative
  `d⟨G⟩ = ⟨G' + m G A'⟩ - m⟨G⟩⟨A'⟩`, including `m = 0`, with the dominated-integral
  argument explicit;
* `guerraBaseUUDeriv` is the terminal Gibbs covariance. `guerraUUD` propagates mixed
  disorder derivatives through all levels. `hasDerivAt_guerraUD_Uline`, joint
  measurability, and the bound `2(j+1)t uAbs(V)uAbs(W)` are proved;
* `guerra_gradient_stein` applies Gaussian IBP to a first disorder derivative;
* linearity in the direction (`guerraUD_sum_smul`) gives `guerra_disorder_stein`:
  `E[guerraUD(U,U)] = ∑ᵢ τᵢ E[guerraUUD(U,wᵢ,wᵢ)]`, at every cascade depth. At depth
  `k+2`, field `0`, multiply by `1/(2Nt)` to obtain the disorder contribution to `φ'`.

**Step 11 (2026-09-04): conditional cascade-field IBP.**

* `ParisiFormula/PiStein.lean` proves the coordinate Stein identity for a finite product
  of standard Gaussians from line derivatives and integrability;
* `Targets/CascadeFieldPi.lean` proves
  `E[zᵢ G(x+√v z) W] = √v E[(∂ᵢG + m G ∂ᵢA)(x+√v z) W]`, including the zero-mass
  and zero-variance cases, and proves the required integrability;
* `guerraFieldDirection` represents a field shift as a disorder shift for `t > 0`.
  `hasDerivAt_guerraCascade_Yline` and `hasDerivAt_guerraYD_Yline` give the first and
  mixed second field derivatives through every cascade level, reusing the checked
  disorder derivatives and their bounds;
* `guerra_field_increment_stein` specializes the field IBP to each site and level;
* `guerra_field_radial_step` sums the site contributions with justified integral
  interchanges. Writing `T_j` for the tilted expectation and
  `r_j(y) = y · ∇F_j(y)`, it proves
  `T_j[r_j](x) = r_{j+1}(x) + v_j T_j[∑ᵢ(∂ᵢᵢF_j + m_j(∂ᵢF_j)²)](x)`.

**Step 12 (2026-09-04): Theorem 2.1 completed for the current SK formulation.**

* `Targets/CascadeContinuityPi.lean` proves parameter continuity under uniform affine
  growth, including zero mass; `continuousOn_guerraPhi` includes both endpoints.
* `guerraProb` gives normalized, nonnegative single-replica probabilities at every
  level. `guerraReplicaAvg` and `guerraReplicaAccum` construct the two-replica averages
  and their mass-weighted accumulation. Their bounds, measurability, and linearity
  justify every finite-sum/integral interchange.
* `guerraUUD_eq_replicas` identifies the mixed Hessian exactly. The covariance and field
  contractions become overlap-square and overlap averages, respectively.
* `guerraFieldTerm_step` telescopes the conditional field corrections;
  `guerraD_eq_radials_overlap` assembles them through all levels, and
  `guerraD_top_expectation` combines them with the disorder IBP.
* `guerraRemainder` is the explicit `(β²/4)` times accumulated squared-overlap average,
  extended by zero outside `(0,1)`. `guerraRemainder_nonneg_le` proves its bounds;
  `guerraRemainder_eq_expansion` and `parisiCorrection_eq_mass_q` finish the identity.
* `guerra_identity` has no `sorry`. `Targets/GuerraAudit.lean`, included in
  `lake build Targets`, guards the exact standard-axiom lists for Theorem 2.1 and both
  upper-bound consequences. `lake build ParisiFormula Targets` succeeds.

Theorem 2.2 is unchanged and remains open. The formulation uses the exact SK covariance
`(Nβ²/2)R²`, not a general mixed-p-spin covariance or a finite-size covariance error.
The proof route remains Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263.

#### Core 2 — `talagrand_theorem_2_2` (Theorem 2.2)

**Step 13 (2026-09-04): the concentration-to-convergence deduction.**

`Targets/TalagrandConvergence.lean` formalises the argument on p. 230, (2.20)–(2.22),
for the actual SK cascade:

* `guerraGap = guerraPsi - guerraPhi` is continuous on `[0,1]`, starts at zero,
  is nonnegative, and has derivative exactly `guerraRemainder` on `(0,1)`.
* `guerraReplicaExpectation` averages a level-dependent observable using the existing
  mass-weighted `guerraReplicaAccum`. Positivity, total mass one, bounded-observable
  monotonicity, and the required linearity/integrability are proved.
* `guerraOverlapTail` is the mass-weighted probability of
  `(R - q_level)² ≥ a`. The bound `0 ≤ (R - q_level)² ≤ 4` gives
  `Rem ≤ (β²/4)(a + 4δ)` whenever this tail probability is at most `δ`.
* With `a = K·gap + η` and tail probability at most `η`, this yields
  `gap' ≤ (β²K/4)·gap + (5β²/4)η`.
* `guerraGap_le_mul_exp` proves the integrating-factor estimate on the closed
  interval using derivatives only in its interior. It does not assume a derivative
  at `t = 0`, where the interpolation contains square roots.
* `guerraPhi_uniform_of_overlap_concentration` proves uniform convergence on
  `[0,t₀]` under the stated tail bound, with `K` fixed before `η` and `N`.
  `talagrand_theorem_2_2_of_overlap_concentration` assembles the exact near-optimality
  and fixed-level-minimality quantifiers of Theorem 2.2.

These are proved **implications with an explicit concentration hypothesis**. Axiom
guards in `Targets/GuerraAudit.lean` certify that their proofs use only the standard
axioms, not the existing Theorem 2.2 placeholder. No new placeholder was introduced;
`talagrand_theorem_2_2` itself remains unchanged.

**Step 14 (2026-09-04): Lemma 2.7 and the individual replica probabilities.**

`Targets/CoupledCascade.lean` implements the **unrestricted** coupled cascade:

* Independent levels integrate against the product of the two Gaussian field measures.
  Shared levels use the same increment and half the single-replica mass.
* The base is the actual two-replica partition sum; its factorisation is proved.
  The two-field factorisation is preserved through the independent levels, and the
  diagonal identity is preserved through the shared levels, including zero masses.
* `coupledPhi_eq_two_guerraPhi` proves (2.38), including `t = 0, 1`.
* The independent tilted density factors as `W¹ W²`; the shared diagonal density
  equals `W`, not `W²`. Finite sums are interchanged with integrals using proved
  integrability, and the independent replica probabilities factor at every depth.
* `coupledObservable_eq_replicaMeasure` proves (2.39) in iterated conditional-expectation
  form for `0 < t < 1`, for every finite observable and admissible split. The recursion
  integrates the normalized densities; it does not postulate a replica measure identity.

`Targets/ReplicaMeasure.lean` supplies the connection to Step 13:

* `guerraReplicaMeasure` is nonnegative on nonnegative observables, has total mass one,
  and preserves bounds. Measurability and integrability in the disorder are checked.
* `guerraReplicaExpectation_eq_sum_measures` expresses the actual mass-weighted
  expectation as the sum of the individual replica expectations with weights
  `guerraMass d - guerraMass (d+1)`. Those weights sum to one.
* `guerraOverlapTail_le_of_replicaMeasure` turns per-level tail bounds into the exact
  mass-weighted concentration input already consumed by Step 13. Depth zero has zero
  weight; no spurious concentration assumption is imposed on that extra index.

These results have no new placeholders or axioms and are covered by `GuerraAudit`.
**They do not prove Proposition 2.3 or remove the Theorem 2.2 placeholder.** In particular,
handling zero masses in Lemma 2.7 does not establish the strict-scheme reduction needed
by the remaining estimates.

**Remaining work, following the Annals argument:**

1. Define the overlap-constrained partition sum and pressure in (2.27)–(2.28).
   Prove the constrained free-energy gap-to-probability estimate (Lemma 2.6 and
   Proposition 2.5), including Gaussian concentration under the cascade weights.
2. Prove the a priori two-replica bound of Theorem 2.4 using §3–§5 and the scheme's
   optimality. The imported RS-level `twoReplica_GT_bound` is not this general result.
3. Combine those bounds to obtain Proposition 2.3; Step 14 now supplies its conversion
   to the mass-weighted form. Handle coincident masses/overlap levels via (2.19), or
   prove the needed bound directly without strictness. This reduction is not yet
   formalised merely because the convergence lemma accepts degenerate schemes.
4. Supply the concentration hypothesis and replace the original Theorem 2.2
   placeholder; then audit `parisi_formula` itself.


## Phase 4 — Milestone 4: Talagrand's lower bound  (XL, open-ended)

**Route decision (fixed): Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006).**
Panchenko's route is explicitly **out of scope for now**.  This is a deliberate narrowing,
and it prunes a large branch of prerequisites — we do **not** need any of:

* the Ghirlanda–Guerra identities,
* ultrametricity of the overlap (a major theorem in its own right),
* Ruelle probability cascades / Poisson–Dirichlet,
* the Aizenman–Sims–Starr scheme.

The next task is the proof of `talagrand_theorem_2_2` in `Targets/Talagrand.lean`,
following Proposition 2.3 and the coupled-replica estimates of §3–§5. The current
statement asks for convergence `φ_N(t) → ψ(t)` on `0 ≤ t ≤ t₀ < 1` for schemes that
are sufficiently close to `parisiValue` and minimize at their own fixed level.
The deduction from this theorem and Theorem 2.1 to `parisi_formula` is already written.
The deduction from a mass-weighted Proposition 2.3 hypothesis to Theorem 2.2 is now
also proved separately, as detailed in Step 13 above. Lemma 2.7 and the individual-to-
mass-weighted replica conversion are proved in Step 14.

Supporting results available through the **active RSAT dependency** include:

* `SpinGlass.AT.twoReplica_GT_bound` in `Lemmas/GuerraTalagrand/Bound.lean`;
* `SYK.gaussian_lipschitz_concentration` in
  `Lemmas/SpinGlass/gaussian_concentration.lean`;
* the parameter-continuity framework under `Lemmas/AT/`.

These are supporting ingredients, not an existing proof of the local Theorem 2.2.
Their physical files are under `.lake/packages/QuantitativeStrictAT/RSAT/`; no new
vendoring or mixing of the two historical forks is needed to import them.

Fixed-`k` continuity and existence of a minimizer (Target 2b-i) are already proved.
The uniform-in-`k` Lipschitz placeholder (2b-ii) is **not** a prerequisite of the
current final deduction. Keep the lower-bound work focused on the Annals argument,
not on this legacy target or the separate Guerra–Toninelli limit proof.

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
- [x] Document the two local libraries and the active RSAT dependency; retain the
      historical `Lemmas/` and `port/` copies without adding duplicate build targets.
- [ ] Keep `README.md`, this roadmap, the blueprint, and dependency provenance aligned
      with future proof milestones and manifest changes.
