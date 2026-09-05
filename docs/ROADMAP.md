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
replica probabilities with the components of the existing remainder. The constrained
cascade and the deterministic part of Lemma 2.6 are now proved as well (Step 15).
Gaussian concentration (Step 16) and its transfer to the abstract disorder (Step 17)
are now proved. Lemma 2.6 holds on `[0,1]`, and Proposition 2.5 holds on `(0,1)` with
an explicit size/time-independent constant. This is the time domain needed by the
existing convergence deduction. The a priori bound of Theorem 2.4 is in progress:
Step 18 supplies the §5 lambda endpoint construction and its comparison for the
existing cascade, but not the second interpolation or the strict improvement.
Step 19 reuses RSAT's general analytic framework to supply finite paired-field
recursions, their site tensorization, and lambda differentiation. Step 20
instantiates the second interpolation and proves both endpoints; Step 21
proves the terminal Hessian and covariance algebra. Step 22 proves full-depth
fixed-variance first disorder derivatives, scalar mass differentiation,
zero-lambda identities (5.18)--(5.19), and the conditional finite-overlap
deduction of Proposition 2.3 and convergence. Step 23 extends the disorder
Hessian to all depths and proves its Gaussian Stein identities, the scalar
heat equation on actual Parisi inputs, Lemma 5.9 with a level-independent
constant, and exact mass compression. Step 24 supplies one-level coupled variance
generators, the analytic scalar mass-zero extension, closed-interval nested
monotonicity, actual inserted-scheme optimality comparisons, and right-interval
endpoints. The full varying-variance interpolation/replica identification, uniform
Section 4--5 optimality estimates, and remaining overlap/sign cases are still missing.
Step 25 propagates individual variance derivatives through the full cascade
and the Gaussian average, proves the averaged disorder Hessian-trace term,
handles identically zero variance coordinates, and supplies the right correction
and scalar antimonotonicity. It also differentiates the actual full Section 4
recursion at every baseline mass, including zero, and identifies the actual
first variation (4.46). Those partial derivatives alone do not establish the
simultaneous derivative or identify its replica weights.
Step 26 supplies compact joint-path and actual second-interpolation endpoint
continuity, the genuine square-root coefficient derivatives, full right scalar
variance differentiation, and closed-interval bounds for the actual `U` and `f`.
It proves genuine joint differentiation along simultaneous disorder/variance
paths and in both fields, then specializes to the physical left/right integrands
at fixed disorder. The explicit replica identity is a separate obligation.
It exposes the normalized squared-slope factor in `∂vT` and its endpoint-safe
integral identity. These do not by themselves prove `U′`, `U″` or the uniform
quadratic estimate.
Step 27 passes the simultaneous derivative through the actual Gaussian average
and proves both physical pressure derivatives.
The finite-dimensional chain rule and termwise Gaussian Stein now identify
those derivatives with their explicit Hessian-trace and level-heat contributions.
Joint mass/variance continuity of the actual normalized factor now gives its baseline integrability and the
identity `U′=Q`, including baseline mass zero when the baseline is below one.
Replica identification, `U″`, uniform optimality estimates and the remaining
overlap regimes still stand between these results and Theorem 2.2.

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

**Step 15 (2026-09-04): constrained cascade and deterministic Lemma 2.6 induction.**

`Targets/CoupledGrowth.lean` handles genuinely interacting two-field functions:

* Joint measurability and affine field growth imply both ordinary and exponential
  Gaussian integrability. Product-measure Fubini proves that the independent joint
  log-Laplace step equals successive single-field steps at the same mass.
* Both the independent and shared steps preserve growth and order, including at
  zero mass. These statements do not assume the constrained function factors.

`Targets/CascadeEventBound.lean` proves the one-step comparison used in (2.37):
if `B ≤ A`, `0 < m ≤ p`, and `0 ≤ F ≤ exp(p(B-A))`, then its normalized tilted
average is at most `exp(m(T_m B - T_m A))`. Domination proves the necessary
integrability. Positive bounded observables also have positive tilted integrals.

`Targets/ConstrainedCascade.lean` instantiates this with the actual overlap event:

* `constrainedZ`, `constrainedBase`, and `constrainedPhi` define (2.26)–(2.28).
  Attainable overlap gives positive partition sums; the Gibbs event is their ratio,
  proving (2.34). Constrained levels have affine growth and lie below unrestricted ones.
* `coupledMass` records the correct half-mass shared levels. Its reversed-depth
  masses decrease and stay positive before the outer zero-mass step when `s.m 1 > 0`.
* `coupledEvent_le_exp_gap` proves the full deterministic induction on the actual
  `coupledObservable`. `coupledEvent_pos` proves positivity, and
  `log_coupledEvent_le_gap` gives the logarithmic comparison preceding concentration
  on p. 233. The proof never treats `Real.log 0` as a logarithm of a probability.
* The comparison stops before the zero-mass outer average, as it must. Positivity
  also holds after that final average.

All new proofs are placeholder-free, with regression guards in `GuerraAudit`.
At this checkpoint Lemma 2.6 was not yet complete: the mean-pressure-gap assumption
had not been converted into exponential decay. Step 16 below supplies this estimate
in standard Gaussian coordinates.

**Step 16 (2026-09-04): Gaussian concentration and exponential expectation decay.**

`Targets/CoupledLipschitz.lean` proves sup-norm nonexpansiveness of the interacting
two-field cascade, including zero masses and both independent/shared levels.
The constrained log partition sum is nonexpansive on its nonempty overlap set.
Translation identities propagate Lipschitz control of the individual Hamiltonians
to the actual constrained and unrestricted cascades, without a factor from the
number of configurations.

`Targets/CoupledMeasurability.lean` proves joint measurability of the partition sums,
cascade levels, and tilted observables in the disorder and both fields.

`Targets/CoupledConcentration.lean` uses the SK spectral coefficients and independent
standard coordinates for the shared outer field of variance `β² q₁`. For `N > 0`:

* The squared norm of the coefficients of each interpolated Hamiltonian is exactly
  `t N β²/2 + (1-t) N β² q₁`, hence its Lipschitz constant is at most
  `(1 + |β|) √N`. This includes `β = 0` and both interpolation endpoints.
* The constrained/unrestricted pressure gap `D` is `4(1 + |β|) √N`-Lipschitz.
  The proved Gaussian MGF theorem gives
  `P(D - E D ≥ a) ≤ exp(-a² / (32 (1 + |β|)² N))`.
* `gaussianCoupledEvent_small` combines this with the deterministic Lemma 2.6
  comparison. If `E D ≤ -ε N`, attainable overlap and `s.m 1 > 0` give
  `E Q₁ ≤ exp(-(s.m 1 * ε / 4) N) + exp(-(ε² / (128 (1 + |β|)²)) N)`.
  Both rates are positive and independent of `N`, `t`, the overlap, and the split.
  The gap and event are proved integrable; measurability is not an extra hypothesis.
* This uses concentration of `D` directly, followed by `Q₁ ≤ exp(n₁ D)` and `Q₁ ≤ 1`.
  It does not assume concentration of the logarithm of the tilted event.

The new tail, integrability, and expectation results have standard-axiom-only guards.
At this checkpoint the remaining Lemma 2.6 gap was change of law. Step 17 below
identifies these means with the abstract disorder and outer average, then applies
Lemma 2.7. The original Theorem 2.2 remains open.

**Step 17 (2026-09-04): complete Lemma 2.6 and the needed Proposition 2.5.**

`Targets/CoupledGaussianLaw.lean` proves equality of the joint laws of the spectral
SK realisation and the abstract disorder, each accompanied by an independent standard
outer field. It uses the recorded independence and Gaussian laws of `sk.hU.c` and
the spectral representation, including zero spectral variances. Both integrals and
integrability transfer along this equality of laws.

`Targets/CoupledOuterExpectation.lean` proves:

* For `d ≤ k+1`, the last cascade step is exactly the shared field average with
  variance `β² q₁` and mass zero. The pressure and observable identities hold on
  the actual recursively defined objects, not on substitute definitions.
* `gaussianCoupledGap_mean_eq` identifies the Gaussian mean with
  `N * (constrainedPhi - 2*guerraPhi)`. Fubini and subtraction of expectations are
  justified by proved integrability, including that of the constrained pressure.
* `integral_gaussianCoupledEvent_eq` transfers the event mean to the abstract outer
  average on `[0,1]`. `gaussianCoupledEvent_mean_eq` then uses Lemma 2.7 to identify
  this average with the individual replica probability on `(0,1)`.

`Targets/TalagrandProposition25.lean` completes the estimates:

* `talagrand_lemma_2_6`: an expected unnormalised pressure deficit of `ε N` implies
  exponential decay of the actual iterated tilted event expectation, for `N > 0`,
  attainable overlap, `m₁ > 0`, `d ≤ k+1`, and `0 ≤ t ≤ 1`.
* `talagrand_proposition_2_5_explicit` and `talagrand_proposition_2_5`: on `0<t<1`,
  `Ψ(t,u) ≤ 2φ(t) - ε` implies `μ_r(R=u) ≤ K exp(-N/K)`. Here
  `K = 2 + 1/r`, with `r = min(m₁ ε/4, ε²/(128(1+|β|)²)) > 0`.
  The definition of `K` depends only on the scheme, `β`, and `ε`, not on `N`, `t`,
  the overlap, the split, or the particular disorder realisation.
* No optimality or a priori constrained-pressure bound is assumed beyond the
  explicit pressure deficit. Obtaining that deficit is the separate Theorem 2.4 task.

Standard-axiom-only regression guards cover the law and mean identities, Lemma 2.6,
and Proposition 2.5. The restriction to interior time in Proposition 2.5 matches the
existing `guerraPhi_uniform_of_overlap_concentration` hypothesis, which only asks for
concentration on `(0,t₀)` and already concludes convergence on `[0,t₀]`.
No additional endpoint concentration result is needed for that deduction.

**Step 18 (2026-09-04): the Section 5 lambda endpoint construction.**

`Targets/CoupledLambda.lean` proves:

* The genuine four-term, two-spin partition identity (5.14), positivity of its logarithm
  argument, and the terminal derivative at zero coupling, `tanh(x) * tanh(y)`.
* Factorization of the interacting `N`-site partition sum into those one-site
  factors, with the exact `2 N log 2` normalization at zero interpolation time.
* For every real `λ`, the actual constrained base is bounded by the interacting
  unrestricted base minus `λ N u`. Attainable overlap and `N > 0` are explicit.
* Additive-constant equivariance through independent and shared cascade steps,
  including zero mass, and hence the same penalty comparison at every depth.
* A uniform `N |λ-μ|` bound through the cascade, without assuming replica
  factorization when `λ ≠ 0`.

`Targets/CoupledLambdaPressure.lean` proves joint measurability and integrability
in the abstract SK disorder, then obtains `Ψ(t,u) ≤ Pλ(t) - λu`, `P₀(t) = 2φ(t)`,
and `|Pλ(t)-Pμ(t)| ≤ |λ-μ|`, for the existing cascade on `[0,1]` (with positive
size and an admissible split where required). Axiom guards cover the endpoint
identities and the averaged results.

This is a supporting construction for (5.17), **not** a proof of (5.17) for
Talagrand's new interpolating scheme. In particular, the existing `t = 0`
factorization is not an identification of his second interpolation's `v = 0`
endpoint. Still needed are the inserted level and modified Gaussian variances
of (5.5)–(5.13), their one-site cascade factorization, Theorem 3.1's derivative
bound, and the optimality/variation estimates in §4–§5. The terminal derivative
proved here is not the full derivative-through-cascade identity of Lemma 5.8.

**Step 19 (2026-09-04): reuse existing results for the finite paired recursion.**

The reuse audit found that, although the final RSAT two-replica theorem is
RS-specific, its underlying Gaussian calculus and site-tensorization modules
are generic. `docs/PROVENANCE.md` records exact matches and limitations, and
`AGENTS.md` records the user's standing goal and reuse-first development policy.

* `coupledSite_eq_gtTerminal` proves the exact normalization bridge to RSAT.
  The local zero-coupling, terminal derivative, and spin-sum results now reuse
  the corresponding existing results instead of duplicating their proofs.
* `Targets/CoupledFiniteStep.lean` defines the finite one-site and N-site
  recursions directly using `GTFrame.finiteStep`, `finiteStepD`, and
  `AT.gtVectorStep`. Coefficients may be arbitrary signed continuous functions
  of a parameter; masses are any fixed nonnegative sequence, including zero.
* `pairedScalarCascade_good` propagates the upstream `GoodFam` property:
  joint continuity, the actual lambda derivative and its unit bound, and
  unit spatial Lipschitz bounds. `hasDerivAt_pairedScalarCascade` exposes the
  derivative, without assuming differentiability of any new integral.
* `pairedVectorCascade_eq_sum` proves site tensorization at every finite depth
  by applying `AT.gtVectorStep_sum` and discharging its integrability/positivity
  hypotheses using `GoodFam`. Equal fields give `N` times the scalar result.
* `sharedStepPi_eq_gtVectorStep` identifies the existing shared step with the
  general step at mass `m/2`; `independentStepPi_eq_gtVectorSteps` identifies
  the independent step with two general steps at mass `m`. These bridges
  include zero mass and retain the existing physical Gaussian conventions.

This supplies the general recursion and tensorization infrastructure mentioned
in Step 18, not yet the particular coefficients/endpoints of (5.5)–(5.13) or
Theorem 3.1. The generic lambda derivative is not Lemma 5.8's identification
with `U′`, and its masses are fixed, not differentiated. Next reuse candidates
are RSAT's generic finite-state calculus and ordinary-pressure covariance
comparison; extend only what the nested positive-mass cascade actually needs.

**Step 20 (2026-09-04): actual second-interpolation endpoints for the left interval.**

The next concrete step from Step 19 is now complete for the positive-overlap
left-interval construction `q(r−1) ≤ u ≤ q(r)` (paper indices).

* `Targets/TalagrandSection5.lean` defines the inserted overlap and mass
  sequences (5.5), (5.6), frozen variances (5.7), scalar variances (5.10)–(5.13),
  and the actual scalar `V` in (5.15). Ordering, endpoint values, the admissible
  split variance (5.16), and nonnegativity throughout the second interpolation
  are proved. `V` uses the existing RSAT transforms, including zero mass.
* `Targets/CoupledEndpoint.lean` exposes level data in the interacting cascade
  while reusing the existing independent/shared steps, growth, monotonicity,
  Fubini, and constant rules. Site tensorization is proved using RSAT's
  `gtVectorStep_sum`; integrability and positivity are discharged, not assumed.
* `Targets/CoupledReindex.lean` proves deletion of an inserted zero-variance
  level at any mass, and exact affine changes of the physical fields through
  the nested integrals. These connect the new scheme to the old cascade.
* `Targets/TalagrandSecondInterpolation.lean` defines `section5Interpolation`
  directly using canonical Gaussian coordinates with the combined variances
  of `Z + √(1−w)y`. It proves **(5.8)**: `η(1) = Ψ(t,u)` for the existing
  `constrainedPhi`, not a newly assumed endpoint. The inserted level disappears
  and the field scaling is exactly that of the original Guerra Hamiltonian.
* It also proves **(5.17)**: `η(0) ≤ 2 log 2 + V(λ,m,v(u)) − λu`, including
  the normalization by `N`, the outer zero-mass average, arbitrary real λ,
  and explicit attainable-overlap/positive-size hypotheses.
* `hasDerivAt_section5V` gives the actual recursively tilted λ-derivative.
  This is not yet Lemma 5.8's identification with `U′`. Axiom guards cover the
  completed endpoints, tensorization, derivative, and coordinate changes.

These are proved endpoint results, **not Theorem 3.1 or Theorem 2.4**. No
covariance inequality or interior-time differentiability of the new pressure
has been assumed. The canonical-coordinate path can be differentiated directly;
there is no need to first construct redundant abstract `Z,y` random variables.
The right-interval dual construction, negative-overlap branch, and the additional
interleaved scheme of Proposition 5.7 are not yet formalized. The four original
placeholders are unchanged, including the original Theorem 2.2 declaration.

Validation: `bash scripts/check.sh` passes (3,804 build jobs), including twelve
new standard-axiom regression guards. The blueprint compiles without warnings.
No new placeholders or axioms were added, and no dependencies were changed.

**Step 21 (2026-09-04): terminal Hessian and the Theorem 3.1 covariance algebra.**

The analytic base case and the final sign/telescoping calculation are now
proved separately. The intervening nested differentiation/IBP is still open.

* `Targets/ConstrainedFiniteState.lean` proves an exact bridge from
  `constrainedPairFieldBase` to RSAT's `gtStateLogPartition` on the constrained
  pair subtype. `pairDisorderCLM` reuses `gtCoefficientCLM`. The actual first
  disorder derivative, derivative of each Gibbs weight, and mixed second
  derivative follow from RSAT's existing finite-state calculus. Nonemptiness
  of the constrained state space is explicit where needed.
* `Targets/CoupledCovariance.lean` contracts that actual terminal Hessian with
  the abstract SK spectral covariance. The resulting kernel is
  `β²/2 * Σ_ab R_ab²`; its diagonal is `β²(1+u²)`. The independent and signed
  shared field contractions are checked, as is the nonnegative four-square
  defect. The scalar completion reuses RSAT's `gtCovariance_remainder`.
* `Targets/SecondInterpolationAlgebra.lean` defines the explicit finite
  covariance expression and proves it equals `-t * correction - remainder`.
  The remainder is nonnegative for nondecreasing masses and nonnegative
  normalized replica weights. Mathlib's summation-by-parts theorem supplies
  the telescope. The `min(l,τ)` cross path doubles exactly the shared-level
  correction, also for sign `η` with `η²=1`.
* `section5Correction_eq` identifies the correction of the actual inserted
  sequences with `2 * parisiCorrection + (m-m_(r−1)) (θ(q_r)-θ(u))`, as in
  (5.9). This is a proved finite-sum identity, not the pressure inequality
  in (5.9). No mass differentiation or optimality hypothesis is assumed.

**Important boundary:** `pairCovarianceExpression_le` is not a theorem about
`deriv section5Interpolation`. Its replica weights are explicit finite inputs;
the actual nested measures and the derivative/IBP identification must still be
constructed and proved. No equality with `η′`, or its desired bound, was added
as an assumption. The original Theorem 2.2 placeholder is unchanged.

The next analytic reuse candidates are the local fixed-variance
`hasDerivAt_parisiStepPi_param` and `hasDerivAt_tiltAvg_param_pi`, combined with
the independent-step Fubini and shared-step adapters. Propagate the terminal
derivatives, including the mass covariance term, through the actual nested
integrals. The already proved covariance and correction algebra need not be redone.

Validation: `bash scripts/check.sh` passes (3,809 build jobs), including fifteen
new standard-axiom guards. No new placeholders or axioms were added. README,
provenance, and blueprint are synchronized with the precise proved statements.

**Step 22 (2026-09-04): parallel analytic and concentration assembly.**

Independent agents developed fixed-variance nested derivatives, scalar mass
variation, and the finite-overlap deduction while the main agent assembled the
Section 5 zero-lambda identities. File ownership was separated; the zero-lambda
indexing and mass normalization received an independent read-only review.

* `Targets/CoupledCascadeDeriv.lean` proves the actual first disorder derivative
  through every level of `coupledFieldCascade`, with bound `2 * uAbs V`
  independent of cascade depth. Joint measurability, growth, and normalized-tilt
  bounds are discharged for the actual constrained terminal. The existing
  one-field chain rules and independent-step Fubini are reused. The second-field
  and shared tilted-observable derivatives retain the mass covariance term;
  an actual one-shared-level mixed Hessian is also proved, including mass zero.
* `Targets/ParisiMassDerivative.lean` reuses Mathlib's analytic moment-generating
  function theorem to differentiate the actual scalar step in any nonzero mass.
  The derivative equals normalized tilt entropy divided by `m²`; entropy
  integrability, normalization, nonnegativity and positive-mass monotonicity
  are checked. Every actual `parisiF` input is covered. This holds with the
  input fixed, not yet for all nested Section 4 variations.
* `Targets/ParisiStepSemigroup.lean` supplies the scalar semigroup including
  zero masses and zero variances. The nonzero branch adapts the already proved
  linear-growth semigroup; the expectation branch uses Mathlib convolution.
* `Targets/TalagrandSection5Zero.lean` defines the actual scalar `T(v,m)` of
  (4.35) and proves **(5.18)** `V(0,m,v)=2T(v,m)`. At the original mass the
  two split increments merge by the semigroup, proving **(4.36)** and **(5.19)**.
  The outer zero-mass level and both split-variance endpoints are included.
  The local function takes mass before variance, unlike the paper's notation.
* `Targets/TalagrandOverlapTail.lean` proves the conditional deduction of
  **Proposition 2.3 from a uniform Theorem 2.4 bound** and then uniform convergence
  on `[0,t₀]` for a fixed scheme with `s.m 1 > 0`. There are at most `N+1`
  attainable Ising overlaps. The threshold `2K(ψ−φ)+η` yields the `η/K`
  deficit required by Proposition 2.5, and the finite-overlap union is bounded
  by `(N+1) C exp(-N/C)`, uniformly in time and replica level. The mass-weighted
  conversion introduces no additional factor in the number of RSB levels.

**At the Step 22 checkpoint, still not proved:** the full-depth mixed Hessian, varying-variance derivative,
Gaussian Stein/averaging and actual replica identification needed for Theorem 3.1;
the Section 4 nested variations and optimality estimates; Lemmas 5.8--5.9 and
the remaining interval/sign constructions; the coincident-level reduction.
The conditional Proposition 2.3 theorem assumes the uniform quadratic bound,
not its conclusion, and does not claim Theorem 2.4. The original Theorem 2.2
placeholder remains exactly where it was; none was moved into a helper.

Validation: `bash scripts/check.sh` passes (3,815 build jobs), with twenty-three
new standard-axiom regression guards. All five new modules compile without
warnings. The blueprint compiles without warnings; README layout/status,
roadmap and provenance are synchronized. No placeholders or axioms were added,
and no dependency pins or upstream sources were changed.

**Step 23 (2026-09-04): full-depth Hessian, scalar curvature and exact reduction.**

The main agent and all three available agents worked on independent critical-path
files, reusing the locked Mathlib/RSAT results rather than changing proof routes.

* `Targets/CoupledCascadeSecond.lean` proves the actual mixed disorder Hessian at
  every independent/shared depth, with bound
  `(8 + 16 * Σ_{l<j} |m_l|) * uAbs V * uAbs W`. The same induction propagates
  all tilted covariances and measurability. Continuity of first directions follows
  from the bound via Mathlib's mean value theorem; measurable line derivatives
  supply Hessian measurability in disorder. Existing Gaussian-coordinate Stein
  then gives the coordinate and summed Hessian-trace identities, with every
  integrability obligation discharged. Variances are held fixed here.
* `Targets/CoupledCascadeField.lean` instantiates the full-depth calculus with
  arbitrary separate directions `(A,B)` in the two replica fields. RSAT's
  finite-state derivatives give the terminal spin means and covariances; exact
  translation commutation lifts these to the actual spatial derivatives of the
  cascade. The first derivative is bounded by `l1 A + l1 B`; the mixed Hessian by
  `(2 + 4 * Σ_{l<j}|m_l|)(l1 A+l1 B)(l1 C+l1 D)`. Both are measurable and
  field-uniform. Individual and signed-shared coordinate directions are identified
  with the precise spins used in the existing covariance contractions.
* `Targets/ParisiVarianceDerivative.lean` proves the actual scalar heat equation
  `∂v B = (Bxx + m Bx²)/2`, for positive variance and all masses including zero.
  `Targets/Section4Variance.lean` propagates actual spatial C2 regularity through
  every Parisi input, giving **(4.4)** without additional analytic assumptions.
  RSAT's `GoodTriple` gives joint continuity of `B`, `Bx`, `Bxx`; Mathlib's
  continuous-partials theorem supplies the joint Fréchet derivative and the
  chain rule at the moving outer field. For `m ∈ [0,1]`, the bound `0 ≤ ∂v B ≤ 1/2` is
  independent of depth. Nested Section 4 stationarity is not asserted.
* `Targets/Section4SplitDerivative.lean` closes the actual two-step identity
  **(4.11)** on `0 < v < a`:
  `∂v Step(m',a-v,Step(m,v,A)) = (m-m')/2 * E_W[(Bx)²]`.
  It adapts the existing N-site local-neighborhood chain rule to one coordinate,
  combines it with the proved joint derivative, and uses normalized scalar Stein
  to cancel the second-derivative terms. Inner `m ∈ [0,1]`, arbitrary outer `m'`,
  and both zero-mass branches are included. All structural analytic hypotheses
  are discharged for every actual `parisiF` input. The immediate nonnegative
  derivative for `m' ≤ m` is proved. This is not yet the higher mixed identities
  of (4.16), the remaining outer recursion to `section4T`, or scheme stationarity.
* `Targets/CoupledLambdaCurvature.lean` proves the invariant
  `0 ≤ E ≤ 1-D²` through every normalized Gaussian transform of mass in `[0,1]`.
  This sharpens RSAT's generic depth-dependent bound without redoing its analytic
  differentiation. It proves **Lemma 5.9** for the actual Section 5 scalar `V`,
  with constant **1**, uniform in the level count and parameters. Mathlib convexity
  yields `V(λ) ≤ V(0) + V′(0)λ + λ²/2`; the explicit choice `λ=u-V′(0)` gives
  the quadratic gain of **(5.33)** with denominator **2**.
* `Targets/TalagrandLambdaGain.lean` combines that gain with the actual endpoint
  and zero-lambda baseline. At the original mass,
  `η(0) ≤ 2(log 2 + A₀(h)) - (V′(0)-u)²/2`. This is unconditional on the
  stated attainable left interval, but is not yet a time-one pressure bound.
  Lemma 5.8's identification of `V′(0)` with `U′` is not assumed.
* `Targets/RSBZeroMassPiSemigroup.lean` proves the N-site zero-mass semigroup
  using Mathlib's product reindexing and Gaussian convolution.
  `Targets/RSBSchemeReduction.lean` exactly removes a leading zero mass,
  preserving the functional, `ψ`, and actual `φ_N(t)`. Zero-variance padding
  transfers fixed-level minimality. Induction gives a positive-first-mass scheme
  at a lower or equal level. Consequently **all original Theorem 2.2 quantifiers**
  follow conditionally from a uniform quadratic bound for positive-first-mass
  schemes; no strict-overlap condition is inserted into that hypothesis.
* `Targets/RSBMassPiSemigroup.lean` extends the N-site semigroup to arbitrary
  masses. `Targets/RSBSchemeMassReduction.lean` uses it to remove any equal
  adjacent masses, including the first and last pair. Scalar preservation reuses
  the existing one-site tensorization; correction terms telescope exactly.
  `exists_strict_mass_reduction` gives an equivalent scheme with every adjacent
  mass strictly increasing, preserving actual pressure and fixed-level minimality.
  This is the full **mass-strictness part of (2.19)**, not overlap strictness.
  The final conditional theorem now needs the uniform quadratic bound only for
  strictly increasing mass sequences, while retaining all original convergence
  quantifiers and no extra hypothesis on overlap strictness.

Independent read-only review confirmed the curvature invariant, actual paired
mass normalization, and the precise scope of the optimized time-zero endpoint.
The scalar heat/C2/joint-derivative modules also received independent read-only
review and fresh Lean checks. The original target and strict-mass bridge received
a separate quantifier/indexing review.

**At the Step 23 checkpoint:** Theorem 2.2 remains open in its original declaration. The full
varying-variance derivative of `section5Interpolation`, actual replica-weight
identification, and endpoint-safe integration are not yet supplied by the
fixed-variance Hessian/Stein results. Section 4 optimality and Lemma 5.8 still
have to convert the scalar endpoint gain into a bound in `(u-q_r)²`, uniformly
in the level count. The other Section 5 interval/sign cases remain to be done.

**Endpoint cautions at Step 23 (partially resolved in Step 24):** strict masses still leave
`m_(r-1)=m_0=0` at `r=1`. The existing nonzero-mass derivative therefore does
not yet define the needed mass variation there; extend it to zero or supply the
separate first-interval argument. Likewise the positive-variance heat/split
derivatives alone do not supply variance-endpoint derivatives for stationarity.
The spectral Stein left side is still an explicit finite sum; its identification
with the radial direction `D_Z F(Z)` requires linearity of propagated directions.

**Scalar follow-up proposed at Step 23 (completed in Step 24):** closed-interval split-variance monotonicity needs
continuity on `[0,a]` plus the existing interior derivative sign, not endpoint
derivatives. Reuse `GTFrame.goodTriple_finiteStep` on the inner family
`F(p,λ,y)=parisiStep m p A(λ+y.1)`, using the proved joint continuity and C2
invariant, with outer coefficients `sqrt(a-p),0`. Then apply Mathlib's
`monotoneOn_of_deriv_nonneg` on `Icc`. Do not redo dominated integration.

Validation: `bash scripts/check.sh` passes (3,829 build jobs), including
**53 new standard-axiom regression guards** (143 total). All eleven new modules
compile without new warnings. The four original placeholders are unchanged,
including `Targets/Talagrand.lean:3274`; no axioms or proof holes were added.
The blueprint compiles without warnings after layout checking. README module
layout, status, roadmap, and provenance are synchronized. Dependency pins and
upstream sources are unchanged.

**Step 24 (2026-09-04): mass-zero calculus, actual scalar variations, and right endpoints.**

The main agent and all three available agents again worked in parallel on
disjoint proof modules. The original Theorem 2.2 statement remains unchanged.

* `Targets/CoupledCascadeVariance.lean` proves the N-dimensional heat generator
  for an added Gaussian transform, then discharges its spatial regularity,
  growth and integrability assumptions for the actual fixed inner constrained
  cascade. Both the existing independent and shared level definitions are
  covered at positive variance and every real added mass, including zero.
  The derivative is the tilted mean of the diagonal spatial Hessian plus
  mass times squared spatial first derivatives, divided by two. The shared
  legacy parameter is correctly `2 * mass`; independent fields use `2N`
  separate Gaussian coordinates. Actual spatial-direction linearity is proved.
  This does not yet differentiate all levels and disorder simultaneously.
* `Targets/ParisiMassZero.lean` expresses the actual scalar step as the divided
  difference of the cumulant-generating function at zero. Mathlib analyticity
  and the second CGF derivative give the mass-zero derivative as half the
  centered second moment, without a singular-limit assumption. The actual step
  is analytic and monotone in mass on all of `ℝ`, including variance zero.
  Every `parisiF` input satisfies the hypotheses. This resolves the single-step
  zero-mass caution in Step 23, not the entire nested mass-variation argument.
* `Targets/Section4SplitMonotone.lean` uses RSAT joint continuity and the
  interior derivative sign from (4.11) to prove monotonicity on closed `[0,a]`.
  `Targets/Section4NestedMonotone.lean` propagates this through every unchanged
  outer level of the actual `section4T`. It also proves continuity there,
  `T(m,0)=A₀(h)` for arbitrary mass, and `A₀(h)≤T(m,v)` for increased
  admissible mass. No endpoint derivative, strict variance or positive mass
  is silently assumed.
  `Targets/Section4NestedDerivative.lean` also reuses the existing one-field
  parameter derivative theorem at one Gaussian coordinate to propagate the
  actual (4.11) derivative through every outer scalar level. Its normalized
  mean formula and bound `|∂v T|≤(m-m_(r−1))/2` are checked on the interior
  interval with a constant independent of depth, including baseline mass zero.
  Combining this with closed-interval continuity gives the endpoint-safe bound
  `|T(m,v)-T(m,w)|≤(m-m_(r−1))/2 * |v-w|` on the whole split interval.
  This is a variance derivative, not the missing mixed mass/variance identities.
* `Targets/Section4InsertedScheme.lean` constructs the actual admissible
  `RSBScheme.insertLevel`, identifies all scalar prefixes and the deterministic
  correction, and proves that its Parisi functional is exactly **(4.37)**.
  The actual `section4Phi` satisfies **(4.30)** by near-global minimality and
  **(4.31)** by merging equal masses at the upper inserted mass and applying
  the original fixed-level minimality. It equals the original functional at
  the baseline mass and at the original upper overlap. All interval endpoints,
  coincident overlaps and zero masses are included. Uniform first/second
  mass-variation estimates and the `U′`, `U″` identities are not assumed.
* `Targets/CoupledSharedInsertion.lean` proves exact deletion/insertion of a
  shared zero-variance level and moving the sharing cutoff across that level.
  `Targets/TalagrandRightInterpolation.lean` uses this to supply the dual
  construction for `q_r≤u≤q_(r+1)`, including the last interval. Its inserted
  paired mass is `m/2`, its level is shared, and its split variance is
  `t β²(u-q_r)`. The masses/overlaps are monotone on the stated admissible
  ranges, variances nonnegative, the time-zero scalar comparison holds, and
  time one equals the original constrained pressure with the original cutoff.
  These endpoints do not assert Propositions 5.2/5.6 or the full pressure bound.
  `Targets/TalagrandRightZero.lean` defines the actual dual scalar `T_right`,
  proves `V_right(0,m,v)=2T_right(m,v)` and the baseline at **`m_r`**, and
  reuses the existing sharp lambda curvature to optimize the actual right
  time-zero endpoint. Both variance endpoints and the last interval are covered.
  The dual `U′` identification and transport to time one remain open.

Independent read-only reviews checked the actual inserted functional and its
correction, mass-zero analyticity, scalar monotonicity and full variance derivative,
and the dual right cutoff/mass conventions. Right time-one recovery requires
`1≤r`; the broader scalar/time-zero statements at `r=0` do not remove that
condition. The paired right mass range is not claimed to be the scalar scheme's
admissibility range. No endpoint derivative or higher mixed identity is inferred.

Validation: `bash scripts/check.sh` passes (3,838 build jobs), including
**57 new standard-axiom regression guards** (200 total). All nine new proof
modules compile without new warnings. The four original placeholders remain
unchanged, including Theorem 2.2 at `Targets/Talagrand.lean:3274`; no new
placeholder or axiom was introduced. The updated blueprint compiles with no
LaTeX warnings, and README status/layout, roadmap and provenance are synchronized.
Dependency pins and upstream sources are unchanged.

**Step 25 (2026-09-05): averaged partial derivatives, actual first variation, and dual comparisons.**

The main agent and three agents again worked on separate critical-path modules,
with read-only cross-review. This checkpoint distinguishes checked component
derivatives from the still-unproved simultaneous second-interpolation derivative.

* `Targets/CoupledNestedVariance.lean` differentiates one original level variance
  of the actual cascade, expressed by `Function.update v ℓ w`. The checked heat
  seed is propagated through every unchanged outer level by the existing
  normalized parameter rule. For positive varying variance the bound is
  `N K` at an independent level and `2N K` at a shared one, with
  `K=2+4Σ_{i<ℓ}|m_i|+|m_ℓ|`. There is no additional outer-depth loss, but
  this auxiliary analytic bound is not claimed uniform in the inner depth.
  Unvisited levels have derivative zero. Zero masses and zero fixed variances
  are included; no zero-variance derivative is postulated.
* `Targets/CoupledDisorderInterpolation.lean` proves the actual radial disorder
  direction equals its finite spectral sum, then applies scaled coordinate
  Stein. The amplitude derivative of the Gaussian-averaged cascade is the
  expected radial direction and hence the amplitude times the nested Hessian
  trace. The square-root chain rule gives the genuine fixed-field pressure
  derivative with normalization `1/(2N)`. Its domination and measurability are
  proved, not assumed. The pressure is continuous at zero disorder variance.
  All field variances are held fixed in this contribution.
* `Targets/CoupledVariancePressure.lean` proves disorder measurability of the
  actual individual variance derivative by measurable forward difference
  quotients and the checked disorder continuity. The uniform derivative bound
  then justifies differentiation under the Gaussian disorder average, including
  the site-normalized pressure. Thus both kinds of averaged partial derivative
  are now available; their simultaneous chain rule remains an obligation.
* `Targets/Section5VarianceFaces.lean` checks the boundary alternative for the
  actual left and right variances: before interpolation time one, each is
  positive or identically zero. A vanishing coordinate has zero speed and can
  be omitted from the eventual chain rule. Coincident overlaps are retained.
* `Targets/RightInterpolationAlgebra.lean` proves the exact dual correction
  `2*parisiCorrection + (m-m_r)*(β²/2)*(u²-q_r²)`, with shared cutoff `r+1`.
  At baseline `m_r` it is twice the original correction. The algebra includes
  the last interval and makes no pressure-derivative claim.
  `Targets/Section4RightVariation.lean` reflects the checked two-step (4.11),
  giving coefficient `(m-m_r)/2` for the actual right split. For `0≤m≤m_r`,
  closed-interval antimonotonicity propagates through the full actual dual `T`;
  continuity and `T_right(0)=A₀(h)` give `T_right(v)≤A₀(h)`. The derivative
  through all right outer levels and dual stationarity remain open.
* `Targets/ParisiMassLocal.lean` proves a field-uniform derivative bound on
  positive compact mass intervals and the two-sided zero-mass bound
  `|Step(m,v,A)-Step(0,v,A)|≤|m|v/2`. The latter reuses Herbst and reflection,
  then Mathlib's anchored dominated-differentiation theorem. Positive local
  bounds are not claimed uniform as their lower mass endpoint tends to zero.
* `Targets/Section4MassDerivative.lean` differentiates the actual full `T`
  in its inserted mass. At a positive baseline, an explicit nested normalized
  derivative propagates through every outer level. At zero baseline, all
  unchanged outer masses vanish, and the semigroup reduces them to a single
  Gaussian expectation with variance `β²q_r-v`. The baseline theorem covers
  the entire closed variance interval, including coincident overlaps.
  It justifies the actual `U=2∂mT` of (4.42), its zero-baseline centered-second-
  moment formula, and `U(0)=0`.
  `Targets/Section4FirstVariation.lean` identifies (4.46) with the actual
  baseline mass derivative of `section4Phi` and proves `f(q_r)=0`.
  Mixed mass/variance derivatives, uniform higher-mass estimates and the
  quantitative stationarity argument are not inferred from these results.

Independent read-only cross-reviews checked the radial Stein factor and site
normalization, original variance-level indexing and heat factor, measurable
outer averaging, and the actual mass-zero semigroup/differentiation argument.
No correctness issues were found. The original target remains unchanged.

**Checkpoint checklist:**

* [x] Individual variance derivative through all outer levels and disorder averaging.
* [x] Actual averaged disorder derivative, radial Stein, and zero-disorder continuity.
* [x] Zero variance coordinates in both neighbor intervals are constant.
* [x] Actual nested baseline mass derivative, `U`, and first variation (4.46).
* [x] Right correction and closed-interval scalar comparison.
* [ ] Simultaneous interpolation derivative, replica identification, and transport.
* [ ] `U′`, `U″`, uniform optimality estimates, and Lemma 5.8.
* [ ] Remaining overlap regimes and the uniform Theorem 2.4 bound.
* [ ] Unconditional Theorem 2.2 and the final Parisi-formula dependency audit.

**Step 25 validation:** `bash scripts/check.sh` passes (3847 target-build jobs),
including **57 new standard-axiom guards** (257 total). All nine new proof
modules compile without new warnings. The four original placeholders are
unchanged; no new placeholder, project axiom, dependency update or upstream
source edit was introduced. The updated blueprint compiles to 21 pages with
no LaTeX warnings. README status/layout, provenance and this checked/open
checklist are synchronized with the actual proof boundary.

**Step 26 (2026-09-05): joint path differentiation and normalized Section 4 bounds.**

The main agent and three agents continued separate critical-path tasks and
cross-reviewed the actual Gaussian and mass conventions.

* `Targets/Section5InterpolationPath.lean` proves the actual left/right variance
  and square-root amplitude derivatives. A constant zero face has derivative
  zero, justified by Step 25's positive-or-identically-zero alternative.
  The disorder coefficient `sqrt(w*t)` is differentiated for `w>0`, also at
  `t=0` by its constant branch. No singular endpoint derivative is asserted.
* `Targets/CascadeContinuityPi.lean` generalizes only the parameter type of the
  existing continuity theorem, leaving its proof unchanged.
  `Targets/CoupledPathContinuity.lean` reuses it at variance 1, placing the
  moving coefficients in the input and obtaining uniform growth from compact
  images. Existing finite-direction packing handles both independent and
  shared steps. `Targets/ConstrainedPathContinuity.lean` discharges the actual
  constrained terminal's hypotheses via RSAT's finite-state log partition,
  then proves full-cascade continuity along simultaneous disorder, variance
  and field paths. Masses, cutoff and the attainable overlap stay fixed.
* `Targets/Section5InterpolationContinuity.lean` passes this continuity through
  the actual Gaussian disorder average using the existing disorder Lipschitz
  estimate and affine Gaussian-norm domination. Both actual physical
  interpolations are continuous on `[0,1]`, including zero variances, `t=0`
  and `t=1`. This supplies the endpoint-continuity input for future transport,
  not the missing covariance derivative inequality.
* `Targets/ConstrainedJointTerminal.lean` proves full joint smoothness in the
  actual disorder and both fields, reusing the same finite-state log partition.
  Composing a differentiable disorder path gives the joint terminal derivative
  needed by the moving-shift induction; no compactness or Gaussian assumption
  is needed for this terminal theorem.
* `Targets/CoupledJointInterpolation.lean` proves full joint differentiability
  in time and both fields through every actual independent/shared level. A
  telescoped variance comparison, disorder bound, and spatial bound give local
  anchored domination. Differentiating the moving Gaussian shift then gives the
  induction step, including zero mass and locally constant zero variance. This
  is a proved simultaneous derivative, not an assumption about separate partials.
  The successor derivative is explicitly the normalized Gaussian mean of the
  actual inner joint derivative composed with the moving shift, before Stein/IBP.
  `Targets/Section5JointInterpolation.lean` applies it to both actual physical
  integrands at fixed disorder for `0<w<1`, with no strict-overlap assumption.
  The outer Gaussian derivative and its replica covariance identification remain open.
* `Targets/Section4UBounds.lean` takes right mass difference quotients of the
  already checked full `T` comparison. The actual `U` is nondecreasing and
  1-Lipschitz on the closed variance interval, with `0≤U(v)≤v`. The first
  variation `f` is continuous and `β²/2`-Lipschitz in overlap. This requires
  `m_(r−1)<1`, supplied on the critical path by strict-mass reduction; it does
  include zero baseline mass and coincident overlaps. No mixed derivative is used.
* `Targets/Section4VarianceFactor.lean` defines the actual nested normalized
  squared-slope mean `Q` without dividing by the mass gap and proves
  `∂vT=(m−m_(r−1))Q/2` on the interior, with `Q∈[0,1]`. Mathlib's nonnegative-
  derivative integrability and fundamental theorem give, on closed subintervals,
  `T(m,w)−T(m,v)=(m−m_(r−1))/2 * ∫_v^w Q(m,z) dz`. The product is integrable
  even at equal masses. Integrability of `Q` alone is proved for a positive mass
  gap, not silently inferred at baseline. Continuity of `Q` at the baseline and
  passage to the mass limit remain the concrete route toward `U′=Q`.
* `Targets/Section4RightDerivative.lean` propagates the actual reflected split
  derivative through all `r` outer levels. Its signed range is
  `[(m−m_r)/2,0]` for `0≤m≤m_r`, with no depth loss. The same mass-gap constant
  gives a closed-interval Lipschitz estimate, including zero masses, degenerate
  variance intervals, and the last overlap interval. Dual stationarity is still open.

Independent read-only review checked the general continuity adapter, zero-face
derivative branches, shared-mass packing, actual left/right cutoffs, and outer
Gaussian domination. A separate review checked the full joint induction's
anchored domination, derivative measurability, zero faces, and exact scope.
Root also reviewed the scalar quotient and normalized-factor
arguments, including the distinction between product integrability and baseline
integrability of `Q`. No correctness issues were found in those reviewed results.

**Step 26 checked/open checklist:**

* [x] Genuine physical coefficient derivatives, including constant zero coordinates.
* [x] Actual joint path continuity and Gaussian-averaged continuity at both endpoints.
* [x] Actual terminal joint smoothness and path/field differentiation.
* [x] Full actual cascade joint differentiation and physical pointwise left/right paths.
* [x] Closed-interval monotonicity of actual `U` and Lipschitz bounds for `U` and `f`.
* [x] Actual normalized factor `Q`, bounds, and endpoint-safe integral identity.
* [x] Full right scalar variance derivative and its closed-interval bound.
* [ ] Full simultaneous pressure derivative, replica identification, and transport bound.
* [ ] Baseline continuity of `Q`, `U′`, `U″`, uniform optimality, and Lemma 5.8.
* [ ] Remaining overlap regimes and the uniform Theorem 2.4 bound.
* [ ] Unconditional Theorem 2.2 and the final Parisi-formula dependency audit.

**Step 26 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3857 target-build jobs), including **54 new standard-axiom guards**
(311 total). All ten new proof modules pass direct or targeted Lean checks
without module warnings; independent reviews checked the actual analytic and
normalization hypotheses. The original four placeholders remain unchanged,
and no dependency pins or upstream sources were changed. The updated blueprint
compiles to 23 pages with no LaTeX warnings. README status/layout, provenance,
blueprint and this checked/open checklist match the verified boundary.

**Step 27 (2026-09-05): averaged path derivatives and the actual identity `U′=Q`.**

The main agent and three agents continued independent critical-path tasks,
then cross-reviewed the new analytic hypotheses and normalizations.

* `Targets/CoupledPathPressure.lean` proves an anchored path bound
  `(A+B*‖U‖)*|z-w|` on one common time neighborhood for every disorder `U`.
  Measurable difference quotients establish measurability of the actual time
  derivative; auxiliary clipping of variances agrees with the original path
  nearby and does not change the interpolation. Gaussian norm integrability
  and Mathlib's anchored differentiation rule then prove both derivative
  integrability and interchange with the actual outer Gaussian expectation.
* `Targets/Section5PressureDerivative.lean` specializes this to both actual
  left/right physical pressures on `0<w<1`. The original cutoffs, reversed
  level order and `1/N` normalization are retained. Zero masses, `t=0`, and
  locally constant zero-variance coordinates are included. This is the genuine
  simultaneous pressure derivative, not a formal sum of separately assumed partials.
* `Targets/CoupledPathDecomposition.lean` proves finite-dimensional joint
  differentiability on the actual active variance face. Basis derivatives are
  identified with the checked disorder and single-level variance derivatives;
  linearity then gives the actual simultaneous sum. Inactive zero coordinates
  stay fixed, so no derivative transverse to a zero-variance face is assumed.
  `Targets/CoupledPathPressureFormula.lean` splits the expectation only after
  proving termwise integrability and applies the existing radial Stein identity.
  Both physical pressure trace-plus-heat formulas are now checked, with disorder
  coefficient `t/(2N)` and the existing heat normalization. This does not yet
  identify the terms with the replica-overlap covariance expression.
* `Targets/ParisiJointMassContinuity.lean` proves true joint mass/variance/field
  continuity of the actual scalar potential and slope. Weighted exponential
  moments have Gaussian domination; the potential's mass-zero branch uses the
  existing two-sided Herbst estimate. No division by the mass is used at zero.
* `Targets/Section4VarianceFactorContinuity.lean` propagates the actual bounded
  squared-slope observable through normalized Gaussian means. It proves joint
  continuity of `Q` on the entire closed admissible mass/variance rectangle,
  including masses zero and one, and baseline integrability without dividing
  by the zero mass gap.
* `Targets/Section4UPrime.lean` passes the right mass limit through the checked
  variance integral identity. The actual baseline mass derivative gives
  `U(w)-U(v)=∫_v^w Q(m_(r−1),z) dz`; hence `U′=Q` and `0≤U′≤1` on the
  interior. The baseline must satisfy `m_(r−1)<1`, supplied by strict-mass
  reduction. Both endpoint values in the integral identity, coincident overlaps,
  and zero baseline mass are retained. The actual overlap first variation has
  derivative `β²(u-Q)/2`; beta zero is constant. No stationarity is inferred.

Independent read-only review checked the common time neighborhood, derivative
measurability, exact pressure normalization and cutoffs, and the mass-limit
factor of two and first-variation sign. Separate reviews checked the full
finite-parameter induction, active-face basis decomposition and termwise
Gaussian trace normalization. No substantive issues were found.

**Step 27 checked/open checklist:**

* [x] Simultaneous derivative through the actual outer Gaussian expectation.
* [x] Actual left/right pressure derivatives throughout the open time interval.
* [x] Explicit disorder/variance decomposition and both averaged physical trace-plus-heat formulas.
* [x] Actual scalar joint mass/variance continuity, including mass zero.
* [x] Joint continuity and baseline integrability of the actual normalized `Q`.
* [x] Actual integral representation of `U`, `U′=Q`, and overlap derivative of `f`.
* [ ] Replica covariance identification and the interpolation inequality/transport.
* [ ] `U″`, uniform higher-mass/optimality estimates, and the remaining Lemma 5.8 identities.
* [ ] Remaining overlap regimes and the uniform Theorem 2.4 bound.
* [ ] Unconditional Theorem 2.2 and the final Parisi-formula dependency audit.

**Step 27 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3864 target-build jobs), including **37 new standard-axiom guards**
(348 total). All seven new proof modules pass direct and targeted Lean checks
without module warnings. The original four placeholders, target statements,
dependency pins and upstream sources remain unchanged. The updated blueprint
compiles to 25 pages without LaTeX warnings. README status/layout, provenance
and the checked/open checklist are synchronized with the actual proof boundary.

**Remaining work, following the Annals argument:**

1. Prove the a priori two-replica bound of Theorem 2.4 using §3–§5 and the scheme's
   optimality. The imported RS-level `twoReplica_GT_bound` is not this general result.
   Next concrete step: construct normalized replica weights for the now-checked
   trace/heat contributions of the simultaneous pressure derivative, and
   prove the derivative equals the covariance expression from Step 21.
   Then prove the endpoint-safe integration of that derivative. The square
   completion, mass telescoping, and inserted correction of (5.9) are now
   available, as are the actual nested baseline mass derivative, first variation,
   and baseline identities
   (4.36), (5.18), (5.19), scalar heat equation, Lemma 5.9 and optimized time-zero
   endpoint. The actual scalar insertion and optimality input inequalities are
   now available, as is the actual first identity `U′=Q`; prove the higher
   nested mass/variance identities and uniform estimates
   of Section 4, then Lemma 5.8 and the remaining overlap/sign cases. Both neighbor
   interval endpoint constructions and both correction adapters are checked.
   Do not replace `2ψ(t)`
   with `2φ(t)`.
2. Apply the completed conditional Proposition 2.3/convergence deduction and
   Step 23's exact equal-mass compression/strict-mass bridge once the uniform
   Theorem 2.4 bound is proved. Handle coincident overlap levels needed by the
   scalar stationarity argument via (2.19), or prove the bound without overlap strictness.
3. Supply the concentration hypothesis and replace the original Theorem 2.2
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
