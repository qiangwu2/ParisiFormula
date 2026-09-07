# Roadmap

## Critical path to the goal

**Goal: Talagrand's proof of the Parisi formula (Ann. of Math. 163 (2006)) — Target 4.**

Target 4 states that the free energy `F_N = (1/N) E log Z_N` converges to
the value given by the Parisi formula (`parisi_formula` in Lean). It follows from

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
At the end of Step 27, replica identification, `U″`, uniform optimality estimates
and the remaining overlap regimes were still missing. Steps 29--30 close the
derivative and interpolation gaps described in the current frontier below.

**Current checked frontier (Step 45):** Proposition 4.6, closed-interval
concavity, both transported lambda gains and the positive-baseline far-left
strict bound are checked. Stationarity now includes the final compulsory-mass
level. Exact mass/interior-overlap reduction supplies its inward directions
without restricting the original Theorem 2.2 schemes. The actual Hessian-square
factor `R` is continuous up to the variance endpoints, with inward `Q′=-R`.
The actual scalar third/fourth derivatives now have depth-uniform bounds,
and Gaussian Stein gives the actual `R` a universal Lipschitz constant 535.
Lemma 4.9's genuine interior third-derivative bound and the closed-interval
cubic Taylor estimate are checked. Proposition 4.10's sixth-root curvature
bound no longer assumes regularity. Propositions 5.1 and 5.3 now give the
local-left and entire initial-interval quadratic deficits for the actual
constrained free energy relative to `2ψ`, with explicit beta-only constants.
The right baseline is now identified exactly with the reflected next left
interval, and neighboring endpoint factors agree. This proves the local-right
quadratic estimate for `1 ≤ r ≤ k+1` in every reduced scheme, using the same
beta-only constant as Proposition 5.1. Exact redundant terminal padding includes
the possibly nontrivial interval `[q_(k+1),1]` without assuming minimality of the
padded scheme. One-sided optimality now supplies curvature at zero first overlap,
closing the other boundary case. Proposition 5.2 is checked in the project's
exact-covariance SK setting for the reduced schemes used by the convergence
deduction. The actual right insertion now supplies the genuine mass derivative,
the same depth-uniform second-mass/Taylor bound, and the dual first-variation
upper bound from original fixed-level and near-global minimality. A negative
corrected right mass derivative gives a scalar deficit chosen before system
size and disorder, including baseline mass one. The actual normalized right
factor is now identified and mass-continuous; a mass limit proves `U_+'=Q_+`
up to inward endpoints. Its convex supporting line closes Proposition 5.6
at every physical level. Proposition 5.4 is now checked for reduced schemes:
exact SK spin reflection and conditioning on the frozen positive shared field
reuse the actual covariance inequality with arbitrary external fields. This
transports the retained-field zero-time gain to the original constrained free
energy, using the original minimality and near-minimality assumptions.
For Proposition 5.7, strict scalar interchange (including lower mass zero),
strict finite sorting, and identification of the sorted recursion with the
original Parisi recursion are checked. The actual mixed paired recursion
satisfies the comparison and equality-order condition (5.44). The cumulative
tagged overlaps have the required correction, and the full interleaved
interpolation's endpoint at its second time one is exactly the original
constrained free energy, for either overlap sign. Step 42 supplies actual mixed
first/second derivatives, normalized Gibbs and split laws, their Hessian and
transported heat identities, Gaussian disorder differentiation, and the actual
interpolation's closed-interval continuity. Signed trial-matrix increments now
match the true tagged modes, including frozen physical tags. The negative
field endpoint is strict at every physical level `r ≥ 2` in the current trial
index range, including zero first overlap and overlap breakpoints.
Step 43 identifies the simultaneous derivative with its actual disorder and
level-heat terms, passes it through the Gaussian expectation, and matches the
signed covariance expression under the genuine split law. The full mixed
derivative inequality and closed-interval endpoint transport are now checked
for `1 ≤ j ≤ k+1`. The original constrained free energy inherits the actual
scalar deficit, chosen before system size and disorder. The explicit
outside-index and negative-overlap strict endpoints now give genuine
free-energy bounds, not just bounds at the auxiliary zero-time endpoint.
First-crossing interval selection includes positive breakpoint overlaps:
the left bound covers `0 ≤ u < q_(r-1)`, and the right bound covers
`q_(r+1) < u ≤ q_(k+1)`, with strict masses and the relevant physical gap.
Step 44 completes the outside-neighbor bound of Proposition 5.7 for the
reduced near-minimizing schemes used by the main argument. Exact terminal
padding covers the full trial range without assuming strictness or minimality
of the padded scheme. At zero first overlap, original minimality forces zero
field, and exact free-energy reflection reuses the positive local/far-right
bounds. One positive accuracy is chosen before every scheme; the positive
pointwise deficit precedes all system sizes and disorders. Both signs, every
breakpoint, first-level degeneracies and physical time zero are included.
Step 45 proves actual scalar continuity in time and overlap on each admissible
trial strip, including the sign boundary, and identifies the full-lambda
time-zero family. Finite compact covers now yield uniform gaps on specified
left/right neighboring regions and compact left outside-trial regions.
Adjacent-trial boundary compatibility and the complete uniform Theorem 2.4
assembly, Theorem 2.2 and the final formula remain open.

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
| `φ(1) =` free energy | `guerraPhi_one` | proved, axiom-clean |
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

**Step 28 (2026-09-05): Lemma 5.8, actual replica weights, and endpoint/derivative inputs.**

Three parallel agents continued the replica, scalar-bridge and higher-derivative
branches while the main agent proved endpoint results and integrated the checks.

* `Targets/Section5LambdaUPrime.lean` proves the actual Lemma 5.8 identity.
  Independent levels propagate a product of scalar slopes at zero lambda;
  the shared diagonal steps have potential `2B` and mass `m_old/2`, giving
  exactly the actual normalized `Q` recursion. Thus `∂λV(0,m,v)=Q(m,v)`
  for all `m≥0` and the full closed variance interval. At baseline below one,
  this is `U′` on the interior and the inward derivative at the endpoints.
  The optimized scalar and actual time-zero gains now contain `(Q−u)²/2`.
  The `Q` identity/gain includes baseline one without invoking `U′` there.
* `Targets/CoupledReplicaWeights.lean` constructs actual normalized constrained
  Gibbs probabilities at every depth and identifies genuine disorder/spatial
  first derivatives with their moments. SK and independent/shared contractions
  have the exact `N` factor and signed cross terms. Split-level replica weights
  multiply two inner probabilities **before** the remaining outer tilted means;
  their positivity, normalization and product-moment identities are checked.
  Shifted profiles and cutoff are proved to be the original cascade restarted
  at that level. These are fixed-disorder identities, not yet the full
  Hessian/heat expansion or its Gaussian-averaged covariance formula.
* `Targets/ParisiSlopeVariance.lean` proves the actual positive-variance
  derivative of the scalar slope, the joint variance/field chain rule and the
  moving squared-slope derivative required for `Q′`. Existing C2 regularity,
  actual Hessian continuity and Gaussian-amplitude differentiation suffice;
  no third derivative is assumed. Tilted Gaussian moment estimates give
  integrability and a common bound on `0<lo≤v≤hi`, uniform in field, mass in
  `[0,1]` and actual input recursion depth. This bound is not uniform at `lo=0`.
* `Targets/Section4UEndpoints.lean` proves the actual inward derivatives of `U`
  and `f` throughout their closed physical intervals. Continuous extension of
  `Q` is used only for the FTC and transferred back by equality on the original
  interval. A numerical `derivWithin` equality requires a positive variance gap;
  the derivative predicate alone also covers singleton intervals.
* `Targets/Section4EndpointOptimality.lean` proves the noninitial-interval
  lower-endpoint conclusion `f(q_(r−1))≥0` for `r≥2` and `m_(r−1)<m_r`.
  The lower-overlap insertion has a zero-variance interval; changing its
  irrelevant mass and merging equal masses gives an actual fixed-level
  competitor. Fixed-level minimality bounds the true right mass quotient.
  The initial interval is not included: its compulsory `m₀=0` cannot be raised
  in this argument. No finite-error condition is upgraded to exact minimality.

Independent read-only reviews checked both root endpoint modules, the entire
replica module and the final Lemma 5.8 bridge. They found no substantive issues,
including at zero mass, zero variance, the shared/independent boundary, and
the inward-versus-two-sided endpoint derivative distinction.

**Step 28 checked/open checklist:**

* [x] Actual normalized Gibbs and split-level replica weights, moments and contractions.
* [x] Actual Lemma 5.8 (`∂λV=Q=U′`) with precise interior/endpoint hypotheses.
* [x] Identified `Q` in the optimized scalar and actual time-zero gain.
* [x] Inward endpoint derivatives for the actual `U` and first variation.
* [x] Lower-endpoint `f≥0` for noninitial intervals and strict adjacent mass gap.
* [x] Actual moving slope/squared-slope derivatives and uniform interior domination.
* [ ] Full Hessian/heat telescope, averaged replica-covariance identity and interpolation inequality/transport.
* [ ] Actual `Q′`/`U″` negative-square identity, uniform higher-mass estimates and remaining stationarity.
* [ ] Initial/dual scalar cases, remaining overlap regimes and the uniform Theorem 2.4 bound.
* [ ] Original unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 28 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3869 target-build jobs), including **45 new standard-axiom guards**
(393 total). All five new proof modules pass direct and targeted Lean checks
without module warnings. Independent reviews found no substantive issues.
The original four placeholders, target statements, dependency pins and upstream
sources are unchanged. The updated blueprint compiles to 27 pages without
LaTeX warnings; README status/layout, provenance and this checklist reflect
the same checked/open boundary.

**Step 29 (2026-09-05): actual U″, nested replica Hessian/heat identities, and uniform mass bounds.**

Three parallel agents worked on replica covariance, scalar variance and mass
estimates while the main agent proved disorder averaging and the actual SK
trace, integrated the branches and updated the project map.

* `Targets/ParisiThirdSpatial.lean` derives the actual third spatial derivative
  after positive Gaussian smoothing from the existing C2 invariant. The spatial
  FTC is differentiated in variance using the checked common interior bound;
  the heat equation identifies the third derivative. No input third derivative
  or unproved interchange of mixed partial derivatives is assumed.
* `Targets/Section4SquaredSlopeDerivative.lean` proves the genuine normalized
  two-step negative-square identity (4.16), including mass zero. The equal-mass
  semigroup fixes the outer normalization, and dominated differentiation plus
  Gaussian Stein gives exactly the negative tilted square of the spatial Hessian.
* `Targets/Section4USecond.lean` propagates (4.16) through every actual remaining
  outer level, whose potential velocity is zero at baseline by (4.11). Thus
  `Q′=−R` with `R∈[0,1]`, and (4.45) gives actual `U″∈[−1,0]`. `Q′` includes
  baseline masses zero and one; `U″` retains baseline below one from `U′=Q`.
  Both derivative identities require interior physical variance. Endpoint
  second derivatives, degenerate-interval derivatives and a strictly negative
  bound are not asserted.
* `Targets/ParisiMassUniform.lean` uses Mathlib CGF/MGF derivatives and the actual
  analytic zero-mass extension to bound both scalar mass derivatives uniformly
  in the field and input depth. Centered tilted Gaussian moments bound the
  second/third cumulants; weighted derivative identities remove inverse-mass
  singularities. This is the actual Gaussian-input analogue of Lemma 4.4,
  including masses in `[0,1]` and variances in `[0,V]`.
* `Targets/Section4MassUniform.lean` propagates the first bound through the actual
  full `T` and inserted `Φ`, with constants depending only on `β`, not `k`, the
  field or the adjacent mass gap. The derivative predicates and bounds include
  zero mass and both physical variance/overlap endpoints. This completes the
  first-derivative part of Lemma 4.5, **not its full nested second bound**.
* `Targets/CoupledReplicaHessian.lean` proves the full genuine disorder/spatial
  Hessian covariance telescope under the actual split law. The two independent
  equal-mass tilts have cancelling intermediate covariance products. Terminal
  covariance supplies the diagonal minus split-zero moment; adjacent-mass
  telescoping retains both endpoint coefficients. All nonnegative fixed
  masses and variances, including zeros, are supported.
* `Targets/CoupledReplicaAverage.lean` proves joint disorder/field measurability,
  weight integrability for any measurable random disorder on a probability
  space, normalized averaged weights and finite-moment interchange. The actual
  averaged covariance square completion and nonnegative remainder are checked.
* `Targets/CoupledReplicaTrace.lean` contracts the genuine full nested Hessian
  with the SK spectral covariance, then takes its actual outer expectation.
  The exact factor `N`, constant constrained diagonal and all split indices
  remain explicit. This identifies the disorder contribution, not yet the
  complete interpolation derivative.
* `Targets/CoupledReplicaHeat.lean` transports actual inner covariance products
  through the unchanged outer levels, then identifies each existing original-level
  heat generator with its replica coordinate-sum expression divided by two.
  Packed independent and nested normalized means agree by uniqueness of genuine
  bounded-perturbation derivatives. Zero-variance algebra is included without
  asserting a derivative at zero variance.

**Step 29 checked/open checklist:**

* [x] Actual (4.16), full baseline `Q′`, and (4.45): `U″∈[−1,0]` at interior variance.
* [x] Zero-inclusive uniform first/second scalar mass bounds.
* [x] Uniform first mass bound for the actual full `T` and inserted `Φ`.
* [x] Full genuine disorder/spatial Hessian telescope under actual split weights.
* [x] Joint disorder measurability, normalized outer-averaged split law and actual SK trace.
* [x] Actual original-level heat generators under the same split law through all outer levels.
* [ ] Field contractions/averaging, combined physical covariance sum, interpolation inequality and endpoint transport.
* [ ] Full nested second mass bound, quantitative optimality and remaining stationarity identities.
* [ ] Initial/dual scalar cases, remaining overlap/sign regimes and uniform Theorem 2.4 relative to `2ψ`.
* [ ] Original unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 29 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3878 target-build jobs), including **63 new standard-axiom guards**
(456 total). All nine new modules pass direct and targeted Lean checks without
module warnings. Independent read-only reviews checked the actual derivative
identifications, zero-mass branches, split indices, shared normalization,
heat factor and disorder averaging; no substantive issues were found.
The original four placeholders, target statements, dependency pins and upstream
sources remain unchanged. The updated blueprint compiles to 30 pages without
LaTeX warnings. README status/layout, provenance and the checklist are synchronized.

**Step 30 (2026-09-06): covariance interpolation bound and full nested mass estimates.**

* `CoupledReplicaField.lean` contracts the genuine original-level heat terms
  into two independent or four shared cross-overlaps, with exact factor `N/2`.
  The same actual split weights justify all outer expectations.
* `Section5ReplicaDerivative.lean` identifies both physical pressure derivatives
  under those weights. Vanishing variances contribute zero because their actual
  velocities vanish, not because a variance derivative at zero is assumed.
* `CoupledCovarianceTelescope.lean` reuses Mathlib finite interval summation,
  summation by parts and reflection. It retains both endpoint mass coefficients,
  contracts the physical field increments and reverses the split indices.
* `Section5CovarianceIdentity.lean` identifies the full actual averaged
  derivative with the covariance expression and applies the checked square
  completion. `Section5InterpolationBound.lean` specializes to the allowed
  left/right mass intervals and transports the derivative bound to the endpoints
  by the mean-value theorem and checked closed-interval continuity. Thus (5.9)
  and its dual hold for the actual SK constructions, including repeated levels.
  The general signed-field version of Theorem 3.1 is not claimed.
* `Section4MassSecondInvariant.lean`, `Section4MassSecondLocal.lean` and
  `Section4MassSecond.lean` prove the previously proposed invariant
  `|E| + D² ≤ K₂ + K₁²` and genuine nested second-mass differentiation.
  The bound depends only on `β`, not depth, field or adjacent mass gaps.
  An open mass neighborhood includes both zero and one; the whole physical
  variance interval is covered. Together with Step 29 this completes the
  first/second mass estimates of Lemma 4.5 for the actual inserted functional.
* `Section4MassTaylor.lean` gives uniform Lipschitz first derivatives and
  quadratic Taylor errors for the actual `T` and inserted `Φ`, including the
  baseline expansion in the checked first variation. The error constant is
  `C(β)`, without optimizing it to `C(β)/2`; no optimality conclusion is assumed.

**Step 30 checked/open checklist:**

* [x] Actual field contractions, outer averaging and full covariance identity.
* [x] Covariance derivative inequality and endpoint transport for both positive-overlap Section 5 constructions.
* [x] Full nested second mass bound and endpoint-inclusive Lemma 4.5 estimates.
* [x] Uniform quadratic Taylor estimate at the actual baseline mass.
* [ ] Quantitative optimality estimates and remaining stationarity conditions.
* [ ] Initial/remaining overlap and signed-field cases; uniform Theorem 2.4 bound relative to `2ψ`.
* [ ] Unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 30 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3887 target-build jobs). All nine new modules check without module
warnings. The 55 new standard-axiom dependency guards pass, for 511 guarded
results in total. Independent read-only reviews checked the covariance and
endpoint arguments, genuine mass derivatives, zero cases and Taylor estimates.
The original four placeholders and target statements are unchanged. The updated
blueprint compiles to 31 pages without LaTeX warnings; README, blueprint,
provenance and this checklist use the same checked/open boundary.

**Step 31 (2026-09-06): quantitative optimality, partial stationarity and actual pressure gains.**

* `Section4QuantitativeOptimality.lean` proves Proposition 4.6 for the actual
  first variation: `f(u) ≥ -L(β)√ε`. The positive constant is chosen before the
  depth, field, mass gap and overlap. Fixed-level minimality and near-global
  minimality are genuine hypotheses about the original functional; no desired
  derivative sign is assumed. Zero baseline mass and overlap endpoints are included.
* `Section4Stationarity.lean` proves endpoint-safe overlap derivatives and
  `q_r ≤ Q(0)` from an actual left competitor. `Section4StationarityInterior.lean`
  constructs the opposite competitor by lowering a nonterminal mass and reusing
  the existing insertion. This proves `Q(0)=q_r`, inward `U′(0)=q_r` and
  `f′(q_r)=0` for `1 ≤ r ≤ local k`, `β ≠ 0`, strict adjacent masses, and
  `(q_(r-1)<q_r or q_r=0)`, `(q_r<q_(r+1) or q_r=1)`.
  Numerical inward derivatives additionally require positive interval length.
  The final compulsory-mass level `r=local k+1` and coincident interior
  overlap levels are not silently covered. The target already assumes `β>0`.
* `Section4Concavity.lean` reuses Mathlib's derivative criterion and supporting
  lines to prove closed-interval concavity and (5.34) with the actual `Q`.
  Its SK form retains the error `Q(tv)-u`; no stationarity is presumed.
* `Section5PressureGain.lean` and `Section5RightPressureGain.lean` combine the
  checked interpolation endpoints and lambda optimization into bounds for the
  actual constrained free energy relative to `2ψ(t)`. On the left the deficit
  is `(Q(tv)-u)²/2`; on the right it uses the actual right lambda derivative.
  The two-sided mass Taylor estimate also allows decreasing a positive baseline.
* For `0<m_(r-1)<m_r`, the same file proves the far-left strict improvement
  whenever `2L(β)√ε < (1-t)β²(q_r-u)²/2`. If the lambda error vanishes,
  concavity and Proposition 4.6 force a positive mass slope. An explicit admissible
  mass decrease supplies a positive deficit independent of system size and disorder.
  This is the positive-baseline argument of Proposition 5.5, not the initial
  mass-zero case or the uniform local quadratic estimate.
  `Section5FarLeft.lean` puts it in the paper's uniform-smallness form: choose
  `L₃(β)=4L(β)`, assume `L₁(q_r-u)≥1-t₀` and
  `L₃(β)√ε≤(1-t₀)β²((1-t₀)/L₁)²/2`, with `β≠0`, `L₁>0`, `0≤t≤t₀<1`.
  The same hypotheses give a positive deficit chosen before system size;
  compactness in time and overlap remains unproved.

**Step 31 checked/open checklist:**

* [x] Proposition 4.6, with a depth- and gap-independent constant.
* [x] Proposition 4.7 and `f′(q_r)=0` for nonterminal levels with the stated endpoint directions.
* [x] Actual closed-interval concavity and supporting-line estimate (5.34).
* [x] Actual left/right lambda gains relative to `2ψ(t)`.
* [x] Positive-baseline far-left strict improvement, with a system-size-independent deficit.
* [ ] Remaining stationarity cases and coincident-overlap reduction.
* [ ] Lemma 4.9, Proposition 4.10 and the local quadratic estimates of Propositions 5.1--5.2.
* [ ] Initial/dual/far-overlap and signed-field cases; uniform Theorem 2.4.
* [ ] Unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 31 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3894 target-build jobs). All seven new modules check without module
warnings. The 45 new standard-axiom guards pass, for 556 guarded results in total.
Independent reviews checked the genuine optimality competitors, stationarity
directions, endpoint derivatives, mass admissibility, normalization and the
system-size quantifier order. The original four placeholders, target statements
and dependency pins are unchanged. The blueprint compiles to 33 pages without
LaTeX warnings; README, roadmap and provenance share the same checked/open boundary.

**Step 32 (2026-09-06): complete stationarity reduction and isolate the remaining curvature regularity.**

* `Section4StationarityTerminal.lean` keeps the compulsory mass equal to one,
  replaces the last overlap by one, inserts at a variable overlap and merges
  equal masses. The endpoint observable is the actual original `Q(0)`.
  This closes the final-level competitor, including the replica-symmetric
  case, and combines with Step 31 to prove `Q(0)=q_r`, inward `U′(0)=q_r`
  and `f′(q_r)=0` at every level with the stated inward directions.
* `RSBSchemeOverlapReduction.lean` removes repeated interior overlaps by
  raising an irrelevant zero-variance mass and reusing equal-mass compression.
  It preserves the actual functional, `ψ`, every N-site interpolation `φ_N`
  on `[0,1]`, and fixed-level minimality, while retaining strict masses.
  Combined mass/overlap reduction therefore transfers a uniform quadratic
  estimate for reduced schemes to the original Theorem 2.2 quantifiers.
  It does not prove that quadratic estimate.
  `Section4StationarityReduction.lean` supplies both inward directions and
  stationarity at every level of the reduced minimizer. Boundary overlaps
  zero and one remain allowed; no extra strictness is imposed on the target.
* `Section4HessianRegularity.lean` reuses joint second-observable continuity
  and the existing interior identity to prove closed-interval continuity of
  the actual `R`, `Q(v)-Q(w)=-∫_w^v R`, and inward `Q′=-R`, including
  baseline mass zero. Numerical derivative uniqueness requires positive
  interval length. No higher-regularity bound follows merely from continuity.
* `Section4Curvature.lean` identifies genuine inward first/second derivatives
  of `f` and proves the deterministic short/long-gap sixth-root argument.
  `Section4CubicTaylor.lean` derives the actual cubic remainder from an
  explicit pairwise `L`-Lipschitz bound for `R` on its full physical interval,
  using Mathlib's mean-value theorem twice. The remainder constant is `β⁶L/2`.
* `Section4InitialCurvature.lean` handles the short initial interval using
  stationarity, nonnegativity of `Q` and FTC: `∫_0^(β²q₁) R ≤ q₁`.
  The same explicit Lipschitz input gives `-f″(q₁) ≤ Lβ⁶q₁/4`.
  This does not vary the compulsory initial mass `m₀=0` or assume `f(0)≥0`.
  `Section4CurvatureRegularity.lean` combines short and long initial intervals
  with the noninitial argument. For every positive overlap gap it proves
  `-f″(q_r) ≤ 2(β⁶L/2 + L_opt(β)) ε^(1/6)`, including `ε=0`,
  **conditional on the actual `R` Lipschitz bound**. The constant is uniform
  in depth only if the supplied `L` is. No such uniform `L` is constructed yet.

**Step 32 checked/open checklist:**

* [x] Final-level stationarity and exact coincident-interior-overlap reduction.
* [x] Stationary reduced minimizer preserving the original functional and interpolation.
* [x] Actual `R` continuity and endpoint-safe first/second variation identities.
* [x] Cubic Taylor and all-positive-gap curvature estimates from explicit actual-`R` regularity.
* [ ] Depth-uniform regularity of `R`: Lemma 4.9 and unconditional Proposition 4.10.
* [ ] Local quadratic estimates of Propositions 5.1--5.2.
* [ ] Initial/dual/far-overlap and signed-field cases; uniform Theorem 2.4.
* [ ] Unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 32 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3902 target-build jobs). All eight new modules check without module
warnings. The 49 new standard-axiom guards pass, for 605 guarded results in
total. Independent reviews checked the exact reduction and stationarity
competitors, endpoint and singleton cases, beta scaling, initial zero-mass
admissibility, the zero-tolerance argument and the explicit regularity premise.
The original four placeholders, target statements and dependency pins are
unchanged. The updated blueprint compiles to 35 pages without LaTeX warnings;
README, roadmap, blueprint and provenance distinguish conditional curvature
from the still-unproved uniform regularity input.

**Step 33 (2026-09-06): uniform regularity and the left-overlap estimates.**

* `ParisiThirdUniform.lean` and `ParisiFourthUniform.lean` construct genuine
  third and fourth spatial derivatives of every actual scalar Parisi input,
  bounded by 6 and 43 independently of depth. The normalized exponential
  derivative polynomials contract at fixed mass; changing mass costs at most
  `5 Δm` and `42 Δm`, which telescope. Zero masses and variances are included.
  An additional physical smoothing has derivative bounds 14 and 143.
* `ParisiHessianVariance.lean` differentiates the actual smoothed Hessian
  jointly in variance and field. `ParisiHessianVarianceBound.lean` reuses the
  Gaussian heat generator to remove inverse-variance losses: with input
  C3/C4 bounds `K3,K4`, the Hessian variance derivative is bounded by
  `K4+4K3+16`, hence 83 on actual inputs.
* `ParisiHessianSquareFlow.lean` differentiates the actual equal-mass scalar
  Hessian-square integral with local Gaussian domination. Gaussian Stein
  gives `|R_initial′| ≤ 2 K2 + K3² + K4 + 2 K3 + 2`, hence 535.
  `Section4HessianDerivative.lean` and `Section4HessianLipschitz.lean` transport
  the derivative and bound through fixed normalized outer means without loss.
  `Section4HessianUniform.lean` supplies every input from the actual recursion:
  no C4, derivative, or Lipschitz hypothesis remains in its final results.
  Endpoint continuity gives the closed-interval bound, including singleton
  intervals. `Section4ThirdVariation.lean` identifies the genuine interior
  derivative `f''' = β⁶ R′/2`, handling β=0 separately. Ordinary derivatives
  outside the clamped endpoints are not asserted.
* `Section4CurvatureUniform.lean` discharges Step 32's analytic premise.
  Cubic Taylor has constant `535 β⁶/2`; Proposition 4.10 gives
  `-f″(q_r) ≤ 2(535 β⁶/2 + L_opt(β)) ε^(1/6)` at every physical positive-gap
  level with the genuine inward stationarity directions. Initial/final levels
  and ε=0 are included. The original target statements are unchanged.
* `Section5LocalLeft.lean` proves the actual local lambda-slope estimate and
  quadratic pressure deficit. `Section4InitialHessian.lean` reuses the existing
  weighted Cauchy--Schwarz inequality and zero-mass Gaussian semigroup to prove
  `R(v) ≤ R(0)` on the entire initial interval. `Section5InitialLeft.lean` uses
  this Jensen comparison without a local-overlap smallness assumption.
  `Section5LeftUniform.lean` supplies the proved constant 535, completing the
  SK forms of Propositions 5.1 and 5.3 with the explicit beta-only constant
  `section5LocalLeftConstant β 535`. These estimates retain minimality,
  near-optimality, time and admissibility hypotheses; they do not assert
  Theorem 2.4 for the other overlap cases.

**Step 33 checked/open checklist:**

* [x] Uniform actual scalar C3/C4 bounds, including zero mass and variance.
* [x] Actual interior `R′` and closed-interval `R` Lipschitz bound, independent of depth.
* [x] Lemma 4.9's interior third derivative and endpoint-safe cubic Taylor control.
* [x] Proposition 4.10 without an unproved regularity premise.
* [x] Local-left Proposition 5.1 and full initial-interval Proposition 5.3.
* [ ] Dual local/terminal estimates and remaining far-overlap/sign cases.
* [ ] Uniform Theorem 2.4 assembly and transfer to the original schemes.
* [ ] Unconditional Theorem 2.2 and final Parisi-formula dependency audit.

**Step 33 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3916 target-build jobs). All 85 public results from the 14 new modules
have standard-axiom guards, bringing the guarded total to 690. The new modules
compile without their own warnings. Independent reviews checked the telescoping
C3/C4 invariants, actual initial Jensen identity, Gaussian normalization and
Stein calculation, no-loss transport, beta-zero case and endpoint conventions.
The original four placeholders, target statements and dependency pins remain
unchanged. The updated blueprint compiles to 37 pages without LaTeX warnings;
README, roadmap, blueprint and provenance record the new checked/open boundary.

**Step 34 (2026-09-06): the dual local estimate by exact reflection.**

* `Section5RightLambdaFactor.lean` proves equality of the actual baseline
  lambda families, not just their zero-coupling values. The right paired
  masses equal the next left masses, the sharing cutoffs agree, and the
  variance arrays match under `v ↦ a-v`, where `a=β²(q_(r+1)-q_r)`.
  The existing zero-lambda derivative theorem therefore identifies the
  right derivative with the reflected actual normalized squared-slope factor.
  No new dual Gaussian differentiation is needed for these levels.
* `Section4RightFactor.lean` defines the reflected `Q` and `R` and reuses
  the checked closed-interval calculus to give `Q_right′=R_right` and the
  same Lipschitz constant 535, including zero masses and variance endpoints.
  `Section4NeighborFactors.lean` proves that the next level's full-variance
  `Q` and `R` equal the original level's zero-variance factors. These are
  exact identities, without stationarity or optimality assumptions.
* `Section5LocalRight.lean` proves that the actual right lambda slope
  `Q_right(tβ²(u-q_r))-u` is at most `-(1-t₀)(u-q_r)/2` locally, given
  endpoint stationarity and curvature. The existing right pressure gain
  then gives the quadratic deficit relative to the actual `2ψ`.
  `Section5RightUniform.lean` supplies both endpoint inputs from the original
  minimizer and the checked curvature theorem, with the same constant
  `section5LocalLeftConstant β 535`. No regularity, derivative identification
  or desired free-energy bound is assumed.

**Step 34 checked/open checklist:**

* [x] Exact reflection of the right baseline lambda family and its derivative.
* [x] Neighboring endpoint `Q`/`R` identities and reflected endpoint-safe calculus.
* [x] Actual local-right quadratic estimate for `1 ≤ r ≤ k`, positive left gap.
* [ ] Terminal right interval `r=k+1`: `q_(k+2)=1`, so this interval need not collapse.
* [ ] First-overlap-zero curvature: the positive-left-gap theorem cannot supply it.
* [ ] Remaining far-overlap/sign cases, uniform Theorem 2.4 and unconditional Theorem 2.2.

**Step 34 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3921 target-build jobs). All 20 public results in the five new modules
are guarded, for 710 guarded results overall. No new module warnings or proof
placeholders were introduced; the original four placeholders and dependency
pins are unchanged. The original theorem statements were not weakened.
The updated blueprint compiles to 38 pages without LaTeX warnings.

**Step 35 (2026-09-06): terminal local-right extension by redundant padding.**

`RSBSchemeTerminalPadding.lean` adds a terminal mass-one, zero-variance step
and proves exact shifts of the scalar recursion and its genuine first two
derivatives. `Section4TerminalFactors.lean` transports the full split recursion
and actual `Q/R` factors, including the auxiliary left index `k+2`. The original
terminal right factors therefore inherit the endpoint-safe derivative and
universal 535 Lipschitz bound from the checked nonterminal theory.

`Section5TerminalLambda.lean` proves deletion of a zero-variance independent
step, including zero masses, and equality of the entire original/padded right
lambda family. The existing local-right slope and actual pressure proofs now
apply at every physical level `1 ≤ r ≤ k+1`. The uniform theorem still uses
the original scheme's minimality and near-optimality, with its positive left
gap; no padded-scheme minimality or pressure identity is assumed.

`Section4ZeroOverlap.lean` supplies a separate boundary reduction: at `q_1=0`,
the actual initial `Q/R` factors are squares of the genuine scalar first/second
derivatives, and fixed-level stationarity forces the scalar first derivative
to vanish. These identities include `k=0` but do not prove the remaining
one-sided curvature inequality.

**Step 35 checked/open checklist:**

* [x] Exact scalar, paired lambda and whole-factor terminal padding identities.
* [x] Right factor calculus, neighboring endpoints and actual lambda identification
  at the terminal interval, including its endpoints and degenerate intervals.
* [x] Local-right quadratic deficit at all physical levels with a positive left gap.
* [x] Scalar-square endpoint identities and vanishing scalar slope at zero first overlap.
* [ ] Curvature when the first overlap is zero; stationarity alone is not enough.
* [ ] Remaining far-overlap/sign cases and uniform assembly into Theorem 2.4.
* [ ] Theorem 2.2 and the unconditional final Parisi formula.

**Step 35 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3925 target-build jobs). All 30 public results in the four new modules
are guarded, for 740 guarded results overall, including the strengthened
local-right statements. No new warnings in the changed proof modules, proof
placeholders, project axioms or dependency changes were introduced. The same
four original placeholders remain. The updated blueprint compiles to 38 pages
without LaTeX warnings.

**Step 36 (2026-09-06): zero-first-overlap curvature and Proposition 5.2.**

`ParisiZeroOverlapDerivative.lean` proves the actual endpoint derivative of
the unweighted squared-slope Gaussian mean. At a vanishing scalar slope, the
rescaling `θ = √u` reduces the pointwise limit to existing positive-variance
calculus; Gaussian dominated convergence gives the squared scalar Hessian.
The total variance is explicitly positive, so this is not a derivative
inferred from a singleton interval.

`Section4ZeroOverlapVariation.lean` constructs an actual same-level minimizing
right comparator from the existing auxiliary bases, including `k=0`, and
identifies its derivative on the entire closed interval. Its inner mass is
`m_1` and its outer mass is zero; no equal-mass derivative theorem is substituted.
`OneSidedCurvature.lean` proves the second-order necessary condition at a
stationary one-sided minimum using Mathlib's slope limit and mean-value theorem.

`Section4ZeroOverlapCurvature.lean` combines these results with the original
scheme's stationarity to prove `β² R_1(0) ≤ 1` when `q_1=0`, `q_2>0`, `β≠0`
and the first mass gap is positive. This bound needs no near-optimality error.
`Section5RightBoundary.lean` then proves the local-right deficit at zero first
overlap and combines it with the positive-left-gap theorem. Its final theorem
`constrainedPhi_local_right_of_reduced_min` covers every physical level of a
reduced scheme with the same beta-only constant. A collapsed first right
interval is handled directly by the existing non-strict pressure bound.

**Step 36 checked/open checklist:**

* [x] Actual squared-slope Gaussian endpoint derivative with domination.
* [x] Actual same-level right comparator and one-sided second-order minimality.
* [x] Zero-first-overlap curvature, including the replica-symmetric case.
* [x] Proposition 5.2 for reduced schemes in the exact-covariance SK setting,
  with zero first overlap, terminal levels, closed overlap intervals and
  `0 ≤ t ≤ t₀ < 1` (not `t=1`).
* [ ] Far-right strict improvement, negative initial and outside-neighbor cases.
* [ ] Compactness/uniform Theorem 2.4 assembly, Theorem 2.2 and the final formula.

**Step 36 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3930 target-build jobs). Fourteen newly guarded public results bring
the total to 754. The five new proof modules and changed modules build without
new warnings. No placeholders, project axioms, dependency changes or weakened
target statements were introduced; the same four original placeholders remain.
The updated blueprint compiles to 39 pages without LaTeX warnings.

**Step 37 (2026-09-06): actual right mass calculus and Proposition 5.6.**

The genuine scalar right insertion is now connected to the original scheme's
functional. The inserted mass ranges from `m_(r-1)` to `m_r`, with overlap
in `[q_r,q_(r+1)]`. Equal-mass compression of its lower-mass endpoint produces
a same-level competitor. This proves both needed optimality comparisons from
the original assumptions, not from minimality of an auxiliary padded scheme.

The new `Section4RightMassDerivative` and `Section4RightMassSecond` modules
reuse the checked scalar calculus and normalized covariance invariant on the
actual inner transform. They prove two-sided mass differentiation, including
zero and one, and a depth-uniform quadratic Taylor bound with the same
beta-only constant as on the left. `Section4RightOptimality` then proves the
dual first-variation **upper** bound `f_+(u) ≤ O_β sqrt ε`.

`Section5RightMassGain` transports an actual scalar mass variation to the
original constrained free energy. The paired construction permits scalar
mass up to `2*m_r`; a negative corrected derivative gives a strict improvement
by increasing the mass, even at terminal mass one. The deficit is selected
before system size and disorder. `Section5RightScalarGain` combines this with
the existing right lambda square gain, leaving only the mass derivative sign
to prove in the zero-lambda-slope case. Scalar optimality decreases mass;
paired-pressure improvement increases it. No variable-mass reflection is used.

The normalized factor is now defined without division by the mass gap and
identified with the original reflected factor at baseline. Its fixed-variance
mass continuity allows dominated convergence in the variance integral. The
mass difference quotient is taken from below, so positive baseline mass
suffices, including mass one. This proves the actual `U_+'=Q_+`, including
inward derivatives at both variance endpoints. The checked `Q_+'=R_+≥0`
then gives convexity and the dual supporting line. Actual dual optimality
makes the corrected mass slope negative when the lambda slope is zero and
the overlap is far enough from `q_r`.

`Section5FarRight` assembles Proposition 5.6 with the same beta-only constant
and smallness arithmetic as the far-left case. It covers `1≤r≤k+1`, including
zero first overlap and terminal mass one, with only the original strict mass
gap and minimizing-scheme assumptions. Its positive deficit is chosen before
system size/disorder; compact-uniformity over time and overlap is not claimed.

**Step 37 checked/open checklist:**

- [x] Actual right insertion and both original-scheme optimality comparisons.
- [x] Genuine right mass derivatives and depth-uniform quadratic Taylor bound.
- [x] Dual quantitative first-variation bound from original minimality.
- [x] Normalized right factor, mass continuity, actual `U_+'=Q_+`, and convexity.
- [x] Actual mass-or-lambda gain, including terminal mass one.
- [x] Far-right Proposition 5.6, with a deficit chosen before system size.
- [ ] Signed initial interval, Proposition 5.4.
- [ ] Outside-neighbor construction and strict improvement, Proposition 5.7.
- [ ] Compactness and uniform Theorem 2.4 assembly; then Theorem 2.2 and the formula.

**Step 37 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3941 target jobs). The 62 additional regression guards bring the total
to 816, including the final far-right result and the reused helper lemmas.
All eleven new proof modules compile without warnings. Existing target
statements and dependency pins are unchanged; no new axioms or placeholders
were added, and the same four original placeholders remain. The updated blueprint compiles to 41 pages
without LaTeX warnings.

**Step 38 (2026-09-06): signed initial Gaussian estimates and exact endpoints.**

This records the Step 38 frontier; Step 39 below closes Proposition 5.4's
remaining pressure-transport obligation.

The negative initial interval requires a genuine sign change in the
interpolating field, not a reflection of the external field or a replacement
of the original constrained free energy. `Section4SignedGaussianFactor`
constructs the opposite-field slope product using the actual arbitrary-depth
scalar input. `Section4SignedHessianBound` bounds its Hessian product by the
original unsplit Hessian square, reusing Gaussian reflection and the checked
zero-mass Jensen/semigroup estimate.
`Section4SignedSlopeBound` then gives the endpoint-safe lower bound for the
actual factor, with a generic version valid at any shifted external field.

`Section5SignedInitialLambda` supplies the actual signed scalar lambda family:
its zero-lambda value is twice the original scalar value, its derivative is
the opposite-field product, and its second lambda derivative lies in `[0,1]`.
Thus the existing quadratic optimization gives a scalar square gain. These
are scalar results, not yet a bound on the original constrained free energy.
`Section5RetainedSignedInitialLambda` proves the corresponding baseline,
derivative, and gain with both positive and negative shared fields retained.

`Section5SignedInitialInterpolation` preserves the original frozen positive
shared field and adds a separate mass-zero negative shared field. It proves
the exact physical and zero-time endpoint identities, as well as variance
nonnegativity. With `a=β²q₁`, its zero-time variances are

- independent: `v=tβ²(q₁+u)`;
- frozen positive shared: `b=(1−t)a`;
- negative shared: `c=tβ²(−u)`.

They satisfy `v+b+c=a`; the combined cross-covariance is `b−c`, which may have
either sign. A purely negative shared field does not directly identify this
endpoint. Keep this distinction when connecting the scalar calculation in
Talagrand's proof of Proposition 5.4 to the project's original pressure.
No target statement or external field has been changed.

`Section5RetainedSignedSlope` handles the retained field by conditioning on
its positive shared Gaussian. The generic signed estimate, bounded Fubini,
and the scalar semigroup give the actual derivative bound `V_λ(0)≥−cR₁(0)`.
Under `β²R₁(0)≤1+e` and `0≤e≤(1−t₀)/2`, the actual lambda slope is at least
`(1−t₀)(−u)/2`. `Section5SignedInitialEndpoint` transports the constrained
terminal comparison through the independent prefix and both outer means.
Combining these gives a genuine zero-time endpoint deficit
`(1−t₀)²u²/8`, relative to `2 log 2 + 2A₀(h)`.
This conditions on the actual endpoint curvature data studied previously;
it does not assume the missing signed pressure inequality.

**Step 38 checked/open checklist:**

- [x] Signed Hessian-product Jensen bound, including both variance endpoints.
- [x] Genuine signed Gaussian derivative and closed-interval slope lower bound.
- [x] Genuine signed scalar lambda derivative, baseline, and curvature-one gain.
- [x] Signed/frozen interpolation construction and exact original-pressure endpoint.
- [x] Retained-field slope bound by conditioning, without covariance recombination.
- [x] Quantitative actual zero-time endpoint gain from initial endpoint curvature.
- [ ] Full signed pressure derivative, covariance inequality, and endpoint transport.
- [ ] Complete Proposition 5.4 for the original constrained free energy.
- [ ] Proposition 5.7, uniform Theorem 2.4 assembly, then Theorem 2.2 and the formula.

**Step 38 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3949 target jobs). The 42 additional axiom regression guards bring
the total to 858. All eight new proof modules compile without warnings.
No target statement or dependency pin changed, no axiom or proof placeholder
was added, and the same four original placeholders remain. The updated
blueprint compiles to 42 pages without LaTeX warnings.

### Step 39 — Proposition 5.4: the negative initial interval

The negative initial estimate now holds for the **original constrained free
energy**, not only its zero-time scalar endpoint. In the project's
exact-covariance SK setting, for reduced schemes satisfying the original
fixed-level minimality, near-global minimality and beta-only smallness condition,
`constrainedPhi_initial_signed_uniform` proves

\[
  \Psi(t,u)\le 2\psi(t)-\frac{(1-t_0)^2}{8}u^2,
  \qquad -q_1\le u<0,\quad 0\le t\le t_0<1.
\]

`constrainedPhi_initial_signed_lt` gives Talagrand's strict conclusion.
The explicit hypotheses retain `β ≠ 0`, `m₀ < m₁`, and
`q₁ < q₂` or `q₁ = 1`, as in the initial curvature argument for reduced
schemes. The negative interval is empty when `q₁ = 0`. The deficit is
independent of system size and disorder, but vanishes as `u → 0`; this is
not the full uniform bound of Theorem 2.4.

The proof reuses the positive interpolation calculus rather than constructing
a second signed replica-Hessian framework. `SKSpinFlip` derives
`U(−σ)=U(σ)` almost surely from exact SK covariance, including zero spectral
variances. `Section5SignedCascadeFlip` reflects the second replica and its
independent Gaussian fields. After conditioning on the frozen field, the
external fields are explicitly `x = h + √((1−t)β²q₁) z` and `−x`.
`Section5ConditionedInitialInterpolation` proves the actual derivative bound
and endpoint transport for these arbitrary fields. Genuine joint Gaussian
integrability and Fubini in `Section5SignedInitialConditioning` recover the
original pressure. No external field is silently changed or discarded.
`Section5InitialSigned` combines this transport with Step 38's retained-field
gain. The initial curvature extraction is factored out of the existing
Proposition 5.3 proof without changing that theorem's statement.

**Checked / open checklist:**

- [x] Exact almost-sure SK symmetry and signed-cascade reflection.
- [x] Actual conditioned interpolation derivative and endpoint inequality.
- [x] Integrable frozen-field averaging and original-pressure transport.
- [x] Proposition 5.4, including `u = −q₁`, from the original minimizing assumptions.
- [ ] Proposition 5.7: interleaved mass sequences and outside-neighbor comparison.
- [ ] Compact/uniform assembly into Theorem 2.4.
- [ ] Discharge Theorem 2.2's concentration input and audit the final formula.

**Step 39 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3954 target jobs). All five new proof modules and the refactored
initial-left module compile without warnings. The 32 added standard-axiom
regression guards bring the total to 890. No target statement or dependency
pin changed, no axiom or proof placeholder was added, and the same four
original placeholders remain. The updated blueprint compiles to 43 pages
with no LaTeX warnings or box warnings.

### Step 40 — Proposition 5.7: mass interleaving and scalar operator sorting

This checkpoint develops the new construction on Talagrand's pp. 257--262;
**Proposition 5.7 itself remains open**. It is not a repetition of the completed
neighbor-interval or signed-initial estimates.

`Section5Interleaving` constructs a genuine stable permutation of the physical
and interpolating mass lists using Mathlib's `Tuple.sort`. Every entry retains
its source and original index, including accidental equality between a full
mass and a half mass. The two source lists embed in increasing order. The
sorted masses have endpoints zero and one, and the actual tagged variances
are nonnegative. The correction identity (5.36) and weighted original-level
variance grouping (5.49) are checked, including repeated mass values.
The left/right order obstructions at the end of the paper are also checked
with both witness variances explicitly positive. Ordering is required only
on positive-variance tags. The merged cumulative overlaps and the connection
from actual cascade equality to these order conditions remain to be proved.

`ParisiStepInterchange` proves the actual non-strict Gaussian operator
comparison (5.46) from Mathlib Hölder and Tonelli. It includes equal masses,
zero lower mass, and zero variances. `ParisiCascadeSorting` applies it
repeatedly to the actual finite composition: sorting by increasing mass
raises the scalar recursion. Equal-mass Gaussian steps merge exactly at any
position. This is the sorting mechanism needed for (5.50), not yet the
identification of the sorted interleaved recursion with the original one.

`ParisiStrictConvexity` proves positive Hessians, strictly increasing slopes,
strict convexity and evenness for the actual scalar recursions before or after
sorting. `GaussianCauchySchwarzEquality` proves proportionality of continuous
Gaussian profiles when Cauchy--Schwarz is an equality, by a vanishing square
integral and Gaussian absolute continuity. No equality case is postulated.

`Section5PairScalarComparison` now supplies Lemma 5.10's three non-strict
one-step comparisons and strictness propagation for the actual smooth scalar
inputs. Independent steps preserve the scalar mass; shared/opposite steps
double it. Genuine equality rigidity gives strict shared/opposite comparison
off the appropriate diagonal when mass and variance are positive. Gaussian
non-atomicity spreads strictness off the two diagonals through an independent
step, including mass zero. Explicit growth, differentiability and increasing
slope hypotheses are supplied for actual inputs by the scalar modules, not
assumed as missing comparison conclusions.

The strict version of the scalar interchange must be proved on the actual
strictly convex inputs. Nonconstancy alone is insufficient: affine inputs
also give equality in the operator interchange. The non-strict zero-mass
limit does not prove strictness at zero mass. Neither observation changes
the actual Parisi target or supplies its missing strict comparison.

**Checked / open checklist:**

- [x] Tagged stable interleaving, source embeddings, and mass endpoints.
- [x] Actual tagged variances, correction (5.36), and variance grouping (5.49).
- [x] Non-strict operator interchange (5.46), including degenerate faces.
- [x] Actual finite scalar sorting and exact equal-mass merging.
- [x] Strict convexity/evenness of the scalar inputs and Gaussian equality rigidity.
- [x] Lemma 5.10's one-step comparisons and strictness propagation on actual inputs.
- [x] Outside-neighbor finite-order obstructions with positive witness variances.
- [ ] Strict operator interchange on the actual inputs, including lower mass zero.
- [ ] Full paired recursion comparison and sorted-recursion identification.
- [ ] Interleaved interpolation, original-pressure endpoint transport, and all
      outside-neighbor boundary/sign cases: Proposition 5.7.
- [ ] Uniform Theorem 2.4 assembly, then Theorem 2.2 and the final formula.

**Step 40 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3960 target jobs). All six new modules compile without warnings.
The 68 added standard-axiom regression guards bring the total to 958.
No target statement or dependency pin changed, and no axiom or proof
placeholder was added; the same four original placeholders remain.
The updated blueprint compiles to 46 pages without LaTeX or box warnings.

### Step 41 — Strict scalar comparison and both actual interleaved endpoints

This checkpoint closes the strict scalar-interchange gap, rather than
assuming an equality characterization of Minkowski. **Proposition 5.7 is
still open because its actual mixed-pressure inequality is missing.**

`ParisiStrictVariance` proves strict positivity of the actual tilted variance
of a continuous strictly increasing bounded slope. Gaussian absolute
continuity and the checked Cauchy--Schwarz equality result rule out zero
variance. It also proves that one strict point between continuous ordered
profiles makes a positive-variance Gaussian step strict, even at mass zero.
`ParisiStepStrictInterchange` differentiates the genuine small-variance
commutator at zero; its derivative is minus half the mass difference times
that tilted slope variance. The semigroup and non-strict interchange extend
this small strict swap to every pair of positive variances. The lower mass
may be zero. Actual Parisi recursions and arbitrary admissible scalar
recursions supply every growth, C2 and continuous-positive-Hessian hypothesis.
`ParisiListRegularity` supplies the same properties for actual list suffixes.

`ParisiCascadeStrictSorting` proves that any inversion involving two positive
variances gives a strict increase under sorting. Exact zero-variance deletion
includes the degenerate faces; equality at one field implies ordered scalar
masses on the active tags, as required in (5.51).
`ParisiCascadeIdentification` and `Section5ScalarIdentification` identify the
sorted interleaved composition with the original `parisiF` using the existing
variance grouping and equal-mass semigroup. Thus (5.50) is now an actual
scalar comparison with the original recursion, including all mass ties.
`Section5ScalarEqualityOrder` specializes the equality condition to tagged
data and the outside-neighbor order obstructions.

`Section5MixedCascade` constructs the genuine finite paired recursion with
arbitrary independent, shared and opposite-shared levels. Existing RSAT
finite-step regularity and site tensorization are reused. The scalar
comparison and strictness propagation prove Proposition 5.11's order
condition (5.44) in bottom-up indices. An active shared step followed outward
by an active independent step forces strictness. An active opposite step
followed outward by an ordinary shared step provides the negative-case
mechanism. These statements retain the explicit positive witness variances.

`Section5InterleavedOverlaps` counts interpolation tags before each merged
position and defines the actual cumulative overlap sequence. It proves its
endpoints, monotonicity, value at the distinguished cutoff, unchanged values
across physical tags, and exact increments across interpolation tags.
The actual signed two-replica correction equals twice the original Parisi
correction. `Section5InterleavingFilter` recovers either source list in order,
including numerical mass ties.

`Section5InterleavedEndpoint` defines the full second interpolation with
physical variances frozen and interpolating variances multiplied by `1-w`.
Opposite sharing occurs only at negative-overlap interpolation tags; physical
shared fields remain positive. Exact deletion at `w=1`, source-order recovery,
Gaussian Fubini and physical-field rescaling prove that this endpoint is
exactly the original constrained free energy for either sign of overlap.
`MixedCascadeGrowth` supplies growth, monotonicity and constant transport for
arbitrary mixed steps and lists, including genuinely constrained terminals.
`Section5InterleavedScalarCore` fixes the exact reverse-indexed tagged arrays
shared by both comparisons. `Section5InterleavedZero` proves the other actual
endpoint bound, `eta(0) ≤ 2*log(2) + D_0(lambda;h,h) - lambda*u`, by the
existing constrained-terminal relaxation, mixed Gaussian order and finite-site
tensorization. This holds for either sign, without an interpolation-derivative
hypothesis; the zero-lambda corollary is included.
`Section5InterleavedStrict` then proves the joint strict comparison (5.37)
when the selected absolute-overlap interval is outside the neighboring
indices and the two specified witness variances are positive. Both equality
conditions are derived from the actual recursions, not assumed. The explicit
deficit `2*A_0(h)-D_0(h,h)` is positive and is chosen before system size and
disorder; it gives the corresponding strict bound for the genuine `eta(0)`.
This does not cover the final trial interval above `q_(k+1)`, all choices at
trial-overlap breakpoints, or negative cases whose absolute overlap falls
between the neighboring indices. Those cases still need the existing
padding/reflection machinery or active negative-mode witnesses to be assembled.

`Section5TimeZero` separately proves, for every attainable overlap and every
reduced minimizing level, the actual estimate
`constrainedPhi(0,u) ≤ 2*guerraPsi(0) - (u-q_r)^2/2`.
The explicit-Q version requires no stationarity. This includes signed and
outside-neighbor overlaps; it does not rely on positive interpolation
variances, which vanish when `t=0`.

**Reuse boundary:** `CoupledParamDeriv.linearStep` now packages the existing
arbitrary-matrix Gaussian parameter derivative with unchanged derivative
bound. The existing full spatial/Gibbs/replica/trace and path-decomposition
packages, however, still use one shared/independent cutoff. In Proposition 5.7
the physical and interpolating modes can interleave differently. Neither
RSAT's one-breakpoint GT bound nor its algebraic Guerra bound removes this
mismatch. The actual mixed replica identity and pressure derivative must be
proved before transporting the strict field comparison to the original
free energy. No pressure inequality has been made an assumed input and
called Proposition 5.7.

**Checked / open checklist:**

- [x] Strict scalar interchange, including zero lower mass.
- [x] Strict scalar sorting and its positive-variance equality condition (5.51).
- [x] Sorted scalar endpoint identification and actual inequality (5.50).
- [x] Full mixed paired comparison and equality-order condition (5.44).
- [x] Joint strict scalar and actual second-time-zero endpoint bounds in the
      outside-index regimes with positive witnesses, with a system-size-independent deficit.
- [x] Actual cumulative overlaps and signed correction (5.36).
- [x] Both actual endpoints: the original constrained free energy at second time
      one and the mixed scalar/lambda upper bound at second time zero.
- [x] Uniform-in-system-size time-zero quadratic deficit for all attainable overlaps.
- [ ] Mixed-pressure derivative/covariance inequality and closed-interval transport.
- [ ] All positive-time outside-neighbor boundary/sign cases: Proposition 5.7.
- [ ] Uniform Theorem 2.4 assembly, then Theorem 2.2 and the full formula.

**Step 41 validation:** `bash scripts/check.sh` passes (3229 supporting-library
jobs and 3977 target jobs). All 17 new modules compile without warnings.
The 125 added standard-axiom regression guards bring the total to 1083
(627 allowed-set guards and 456 explicit axiom-print guards).
No original target statement or dependency pin changed; no axiom or proof
placeholder was added, and the same four original placeholders remain.
The updated blueprint compiles to 48 pages without LaTeX or box warnings.

### Step 42 — Actual mixed derivatives, replicas and negative endpoints

This checkpoint removes the one-cutoff restriction from the actual local
derivative and replica machinery required by Proposition 5.7. It does **not**
replace Proposition 5.7 by a theorem assuming the missing pressure inequality.

`MixedCascadeDeriv` and `MixedCascadeSecond` propagate the checked Gaussian
parameter and covariance rules through arbitrary independent, shared and
opposite-shared levels. They prove actual disorder/spatial first and second
derivatives, measurability-enabling bounds, and exact translation identities.
The independent two-step covariance products cancel by the existing proved
identity; opposite sharing is a fixed second-field substitution. All masses
are raw masses and may be zero; unchanged variances may also vanish.
`MixedCascadeVariance` applies the existing arbitrary-direction Gaussian heat
theorem to the actual mixed inner recursion. `MixedNestedVariance` supplies
the full individual-variance parameter package, transports its heat through
all outer modes, and proves the actual partial derivative with a uniform
bound independent of the remaining outer depth.

`MixedReplicaWeights` constructs the actual transported Gibbs law and the
product-before-outer-transport split law. Nonnegativity, normalization,
boundedness, finite linearity and derivative moment formulas are proved.
`MixedReplicaHessian` proves the genuine mixed Hessian's finite covariance
expansion and its mass telescope. `MixedReplicaHeat` transports the actual
spatial Hessian-plus-square expression through every unchanged outer level,
retaining each original split rather than multiplying final averaged means.
`MixedReplicaAverage` proves joint disorder/field measurability, integrability,
normalization and finite moments of the actual disorder-averaged split law;
its signed square completion is included. `MixedReplicaTrace` contracts the
actual Hessian against the original SK spectral covariance and substitutes
that split-moment expression into the genuine amplitude derivative. The
normalized free-energy derivative cancels the factor `N` exactly.

`MixedCascadeContinuity` and `Section5InterleavedContinuity` reuse the existing
arbitrary-direction compact-parameter Gaussian theorem. They prove actual
mixed-potential contraction, disorder continuity/integrability, and
closed-interval continuity of the full tagged free energy, with both signs
and every zero-variance face. `MixedDisorderInterpolation` proves continuity
of the actual first disorder direction, measurability of the actual Hessian,
Gaussian coordinate/radial Stein, and differentiation of the genuine outer
average in its disorder amplitude, with field variances fixed.
`MixedJointInterpolation` proves genuine simultaneous differentiability in
time and both fields, with every visited variance positive or locally fixed
at zero. This reuses the existing joint Gaussian Fréchet theorem; it is not
inferred from separate partial derivatives. The actual time derivative is
the time component of that Fréchet derivative. Finally,
`Section5InterleavedDifferentiability` discharges every such hypothesis for
the actual tagged integrand at `0<w<1`, for both signs and even physical
time `t=0`. The next obligation is its explicit disorder-plus-heat
decomposition and passage through the expectation, not existence of the
pointwise derivative.

`MixedCovarianceTelescope` reuses the existing finite summation-by-parts
identity with arbitrary signed trial-matrix increments. In
`Section5InterleavedCovariance`, the actual cumulative cross path is the unit
trial sign times the stopped absolute-overlap path. Its increment equals the
diagonal increment times the actual tagged mode's correlation. In particular,
physical tags contribute zero covariance velocity even when their positive
sharing differs from the interpolation cutoff. Endpoints and the deterministic
correction are checked; the algebraic bound is `-2*t*parisiCorrection` for any
normalized nonnegative split law. This finite algebra is explicitly separate
from identifying the derivative with that expression.

`Section5MixedReflection` gives an exact scalar second-replica reflection,
interchanging shared/opposite modes while preserving the scalar reference.
This supplies the dual strict comparison without redoing Gaussian strictness.
`Section5InterleavedNegative` proves strictness of the actual field endpoint
for `r ≥ 2`, `1 ≤ j ≤ k+1`, `β ≠ 0`, `0<t<1`, `m_1>0`, `q_1<q_2`, `u<0`,
and `|u|∈[q_(j-1),q_j]`. It allows `q_1=0`, `j=1` and `|u|=q_1`; it does not
require an outside-index condition or strictness of every mass. The positive
deficit is fixed before system size and disorder and bounds the genuine
`eta(0)`. A separate result covers `r=1`, `q_1>0`, `|u|>q_1` in the same trial
index range. The first physical level and final trial interval still require
assembly with the existing initial-interval and padding arguments.

**Checked / open checklist:**

- [x] Actual mixed first/second disorder and spatial derivatives with bounds.
- [x] Actual normalized Gibbs/split laws and Hessian/outer-heat replica identities.
- [x] Actual averaged split laws and the normalized SK spectral contraction.
- [x] Gaussian disorder-amplitude derivative and radial Stein trace.
- [x] Actual individual-variance derivatives and full outer transport.
- [x] Genuine joint differentiability and actual tagged-integrand specialization.
- [x] Actual mixed interpolation continuity at both endpoints, including zero faces.
- [x] Signed cumulative matrix, true mode increments and finite covariance algebra.
- [x] Negative strict field endpoint for all current trial intervals at `r ≥ 2`.
- [ ] Full simultaneous pressure derivative, covariance bound and endpoint transport.
- [ ] Remaining interval/first-level boundary assembly: Proposition 5.7.
- [ ] Uniform Theorem 2.4, Theorem 2.2 and the final Parisi formula.

**Step 42 validation:** `bash scripts/check.sh` passes (3229 supporting jobs
and 3995 target jobs). All 18 new modules compile without warnings. The 172
new allowed-set axiom guards bring the total to 1255 (799 allowed-set guards
and 456 explicit print guards). Independent read-only reviews checked raw
masses, opposite signs, the Gaussian one-half factors, actual split-law
interfaces, zero faces and documentation scope. No axiom or proof placeholder
was added; the same four original placeholders remain. Original target
statements and dependency pins are unchanged. Three existing generic helpers
were made public without changing their proofs. The updated blueprint
compiles to 50 pages without LaTeX or box warnings.

### Step 43 — actual mixed pressure inequality and strict free-energy bounds

The missing simultaneous interpolation connection is now proved. This is a
bound for the actual constrained free energy, not a theorem with a pressure
derivative or replica-law identity assumed as a hypothesis. **Proposition 5.7
still has boundary assembly remaining.**

**Derivative and Gaussian expectation.** `MixedPathDecomposition.lean`
uses the existing finite-dimensional Gaussian parameter theorem to identify
the actual joint time derivative as the disorder direction plus the active
original-level variance derivatives. `MixedPathPressure.lean` supplies one
common anchored neighborhood with a bound affine in the disorder norm,
measurability by difference quotients, and the actual differentiated Gaussian
expectation. `MixedVariancePressure.lean` proves measurability/integrability
of the individual variance derivative and its Gaussian-averaged derivative.
`MixedPathPressureFormula.lean` splits the expectation into its genuine
spectral Hessian trace and finite sum of heat contributions. Locally fixed
zero variances require no derivative at the boundary of the variance domain.

**Actual overlap identity.** `MixedReplicaMoments.lean` supplies the genuine
averaged moments and SK trace. `MixedReplicaField.lean` identifies packed
Gaussian means with the actual mixed normalized means by derivative
uniqueness, transports the heat seed through the unchanged outer levels,
and contracts all three modes to their signed overlap kernels. The factor
is exactly `N/2`; the heat expression at zero variance is algebraic only.
`MixedReplicaPressure.lean` combines the actual SK trace and original-level
heat terms under the same split law using the existing finite covariance
telescope. It does not introduce an arbitrary substitute replica law.

**Actual tagged derivative and endpoints.** `Section5TaggedVelocity.lean`
proves that every nonpositive visited variance has zero actual velocity.
`Section5InterleavedPressure.lean` specializes the complete simultaneous
formula to the true reversed tagged arrays. Its derivative is the signed
covariance expression averaged over the original disorder, and satisfies

`eta'(w) ≤ -2 * t * parisiCorrection s β`.

This holds for both overlap signs, `N>0`, `0≤t≤1`, `0<w<1`,
`1≤j≤k+1` and `|u|∈[q_(j-1),q_j]`, including beta zero, zero masses and
zero unchanged variances. `Section5InterleavedBound.lean` uses the already
proved closed-interval continuity and actual endpoint equality, for physical
`1≤r≤k+1`, to obtain

`constrainedPhi ≤ 2 * guerraPsi - section5InterleavedScalarDeficit`.

The scalar deficit is unchanged and is chosen before system size and disorder.
The strict left/right witness estimates and all negative-overlap estimates
at physical `r≥2` in the current trial range are therefore now actual
free-energy estimates. The latter require `β≠0`, `0<t<1`, `m_1>0`,
`q_1<q_2` and include `q_1=0` and trial breakpoints. The first physical level
is also covered when `q_1>0` and `|u|>q_1`, with trial index at least two.

**Positive breakpoint assembly.** `Section5OutsideIntervals.lean` selects
`[q_(j-1),q_j)` on the left and `(q_(j-1),q_j]` on the right, using Mathlib's
first-crossing `Nat.find` facts. No distinct-breakpoint assumption is needed
for selection. `Section5OutsideBound.lean` discharges the supplied trial index
and witness variances, proving a positive deficit before all `N` and SK
disorders for `0≤u<q_(r-1)` and for `q_(r+1)<u≤q_(k+1)`. These strict
conclusions require `β≠0`, `0<t<1`, strict masses and the relevant positive
physical overlap gap. Exact breakpoint overlaps are included, not excluded
by an extra hypothesis.

**Checked/open after Step 43:**

- [x] Actual simultaneous mixed derivative and its Gaussian average.
- [x] Same-law signed overlap identification, derivative inequality and
      closed-interval original-free-energy transport.
- [x] Positive outside-neighbor strict bounds including breakpoints in the
      stated trial range; no supplied trial-index or heat-velocity hypotheses.
- [x] Negative strict original-free-energy bounds at `r≥2`, and the stated
      nondegenerate first-level case, in the current trial range.
- [ ] Final trial interval `|u|>q_(k+1)` (local index `j=k+2`), including its
      signed boundary cases. Reuse exact terminal padding where possible;
      do not assume strict masses or minimality of a redundantly padded scheme.
- [ ] Remaining first-physical-level sign/degeneracy assembly and integration
      with the already proved initial signed estimate. In particular, the
      first-level negative wrapper does not cover `q_1=0`.
- [ ] A single complete Proposition 5.7, uniform compactness for Theorem 2.4,
      Theorem 2.2 and the final Parisi formula.

**Step 43 validation:** `bash scripts/check.sh` passes (3229 supporting jobs
and 4007 target jobs). All 12 new modules compile without warnings. The 66
new allowed-set guards bring the total to 1321 (865 allowed-set and 456
explicit print guards). Independent read-only reviews checked actual means,
shared/opposite signs and raw masses, the `N/2` factor, reversed split indices,
inactive velocities, endpoint correction and deficit quantifiers. No axiom or
proof placeholder was added; the same four original placeholders remain.
Original target statements and dependency pins are unchanged. The updated
blueprint compiles to 52 pages without LaTeX or box warnings.

### Step 44 — complete the outside-neighbor bound of Proposition 5.7

`Targets/Section5Proposition57.lean` now proves
`talagrand_proposition_5_7` for the exact-covariance SK setting and reduced
schemes used by the main proof. Given `β ≠ 0` and `t₀ < 1`, a positive
accuracy `ε` is chosen before all schemes. For a fixed-level minimizer within
that accuracy of the infimum, with strict mass increments and strict interior
overlap increments, every `1 ≤ r ≤ k+1`, `0 ≤ t ≤ t₀` and `-1 ≤ u ≤ 1`
satisfying `u < q_(r-1)` or `u > q_(r+1)` has

`∃ δ > 0, ∀ N > 0, ∀ SKDisorder, attainable u → Ψ(t,u) ≤ 2ψ(t) - δ`.

The scheme can still have `q₁=0` or `q_(k+1)=1`. The positive deficit may
depend on the scheme, physical level, time and overlap; **it is not yet the
uniform quadratic bound of Theorem 2.4**. Exact reduction already preserves
the objects and quantifiers needed for the original Theorem 2.2.

**Terminal interval, with actual free-energy preservation.**
`Section5TerminalPadding.lean` deletes the extra innermost zero-variance
step and shifts the independent cutoff exactly. Both `constrainedPhi` and
`guerraPsi` remain those of the original scheme. The positive right obstruction
in `Section5InterleavedMassPair.lean` needs only
`m_r < m_(j-1)`, not strictness of every mass. Thus
`Section5PositiveTerminal.lean` applies the proved mixed interpolation to
the padded scheme and covers every `q_(r+1) < u ≤ 1`, including the final
interval. No minimality or strict mass sequence is asserted for the padding.
`Section5NegativeTerminal.lean` similarly covers all negative overlaps at
`r ≥ 2`, including `u=-1`, zero first overlap and all trial breakpoints;
the nondegenerate first level is covered whenever `|u|>q₁`.

**First-level boundaries.** `Section5NegativeInitialAssembly.lean` puts
the existing Proposition 5.4 in the same size-independent gap form, including
`u=-q₁`. If `q₁=0`, `Section5ZeroInitialReflection.lean` first proves that
original minimality forces `h=0`: the actual initial scalar slope vanishes,
is strictly increasing, and is zero at the origin by evenness. Only then is
the second physical replica reflected. The zero shared outer variance is
deleted, and SK disorder evenness gives exact original free-energy symmetry.
`Section5ZeroInitialNegative.lean` reuses the existing local/far-right estimates
to cover `[-q₂,0)`; the full positive outside bound covers the rest after
reflection. This does not assume a symmetry at arbitrary external field.

**Assembly and common accuracy.** `Section5Smallness.lean` uses Mathlib's
continuity of real powers and square root at zero to choose one positive
accuracy satisfying both Section 5 smallness conditions before all schemes.
`Section5Proposition57.lean` combines the signed and positive cases and reuses
the already checked time-zero quadratic bound. No new analytic framework,
dependency revision, axiom or placeholder is introduced.

**Checked/open after Step 44:**

- [x] Final trial interval and exact original-free-energy padding.
- [x] All negative-overlap trials at physical levels at least two.
- [x] Every first-level negative case, including `q₁=0` and `q₁=1`.
- [x] Common positive accuracy before all reduced minimizing schemes.
- [x] Complete Proposition 5.7 outside-neighbor bound in the main proof's SK
      setting, including time zero and every attainable breakpoint.
- [ ] Continuous scalar upper comparisons and compactness giving one uniform
      quadratic bound in time/overlap: Theorem 2.4.
- [ ] Supply the existing concentration/convergence deduction, close the
      original Theorem 2.2 placeholder, and audit the final Parisi formula.

**Step 44 validation:** `bash scripts/check.sh` passes (3229 supporting jobs
and 4016 target jobs). All nine new modules compile without warnings.
Twenty-seven new public results and the one newly exposed unchanged helper
have allowed-set guards, bringing the total to 1349 checks (893 allowed-set
and 456 explicit print guards). Independent read-only reviews checked the
assembled quantifiers, terminal padding, signed reflection, zero-time case
and both positive smallness thresholds. No axiom or proof placeholder was
added; the same four original placeholders remain, including Theorem 2.2.
The updated blueprint compiles to 53 pages without LaTeX or box warnings.
Original targets and dependency pins are unchanged.

### Step 45 — continuous scalar witnesses and compact subregion bounds

Eight new modules connect the actual Section 5 scalar comparisons to finite
compact covers. They do not assume continuity of the finite-size constrained
free energy, nor continuity of a chosen mass or lambda witness.

- [x] `Section5InterleavedScalarContinuity`: actual tagged `(t,u)` continuity
  on each closed admissible trial strip, joining both signs at zero by exact
  zero-variance deletion. This does not yet identify different trial indices
  at their common breakpoint.
- [x] `Section5InterleavedTimeZero`: full-lambda identification at time zero,
  stationary quadratic scalar gain, and a padded final-trial gain using only
  original-scheme minimality. Two existing insertion-array identities are
  exposed unchanged for reuse.
- [x] `Section5InterleavedMajorant`: the actual arbitrary-lambda scalar deficit
  bounds the original constrained free energy, uniformly before system size.
- [x] `Section5ScalarComparisonContinuity` and
  `Section5ScalarComparisonWitness`: continuous fixed-mass left/right scalar
  comparisons and strict witnesses under the proved optimality and smallness
  conditions. The downward left-mass branch requires positive preceding mass.
- [x] `Section5CompactWitness`: a finite-subcover theorem for pointwise strict
  continuous scalar witnesses, including the empty compact set.
- [x] `Section5ScalarComparisonCompact`: one positive gap on each compact
  neighboring region satisfying the stated far-left/right smallness conditions,
  chosen before the point, system size and disorder.
- [x] `Section5InterleavedCompact`: a reusable compact-trial adapter with
  explicit scalar positivity input; also a concrete left outside-trial bound
  on compact subsets of `0 ≤ t ≤ t₀`, `q_(j-1) ≤ u < q_j`, `j < r`, using
  strict masses, the physical overlap gap and actual stationarity. Time zero
  is included. The upper trial endpoint is not included in this concrete result.
- [ ] Join adjacent-trial breakpoints and assemble all remaining signed,
  first-level and padded terminal compact regions with the local quadratic
  bounds to obtain the single Theorem 2.4 bound.
- [ ] Close the original Theorem 2.2 placeholder and audit the final formula.

**Step 45 validation:** `bash scripts/check.sh` passes (3229 supporting jobs,
4024 target jobs). All eight new modules compile without warnings. Thirty-three
new results and two exposed unchanged helpers have allowed-set guards, bringing
the total to 1384 checks (928 allowed-set and 456 explicit print guards).
Independent review checked empty compact sets, gap quantifiers, the genuine
time-zero witness and the half-open trial limitation. The same four original
placeholders remain; no axiom or placeholder was added. The updated blueprint
compiles to 54 pages without LaTeX or box warnings.

**Remaining work, following the Annals argument:**

1. Prove the a priori two-replica bound of Theorem 2.4 using §3–§5 and the scheme's
   optimality. The imported RS-level `twoReplica_GT_bound` is not this general result.
   Next concrete step: join trial boundaries and complete the compact cover
   using the scalar comparisons established in Step 45. Step 44 completes all
   Proposition 5.7 interval/sign/boundary assembly for the reduced schemes.
   Do not assume continuity in `u` of the actual finite-size constrained
   free energy: its attainable constraint set changes with `u`.
   Step 45 reuses `mixedScalarCascade_good` and `splitScalarCascade_good` for
   actual fixed-witness continuity, proves the sign matching and full-lambda
   time-zero identification, and supplies finite compact covers on individual
   domains. Do not rebuild these. Different trial indices still need matching
   at their common breakpoints, followed by all-domain coverage away from
   `q_r` and the already proved local quadratic bounds near `q_r`.
   Step 43 proves the actual simultaneous Gaussian-averaged
   mixed derivative, its signed covariance identity and inequality, and
   closed-interval transport to the original constrained free energy.
   Do not rebuild this pressure chain or assume a replacement derivative.
   Step 41 already supplies strict interchange and sorting, mixed paired
   comparison, sorted scalar identification, cumulative overlaps, exact
   zero-variance deletion and the original free-energy endpoint; do not
   rebuild those. Step 42 also supplies actual mixed derivative/replica
   machinery, endpoint continuity, signed covariance algebra and negative
   strict endpoints at `r ≥ 2`; do not rebuild them. The separate time-zero
   deficit is also checked.
   Step 39 closes Proposition 5.4 through exact
   reflection and frozen-field conditioning; no separate general signed
   pressure derivative is needed for that case. Step 37 closes the far-right strict improvement
   (Proposition 5.6), including its actual mass derivative and optimality input;
   do not repeat that work or identify the full variable-mass families by
   baseline reflection. Steps 35--36 close both local-right boundary cases;
   do not repeat terminal padding or zero-overlap curvature. Uniform regularity,
   Proposition 4.10 and the left/initial estimates are now checked in Step 33;
   do not redo those arguments or the stationarity reduction.
   The actual positive-overlap interpolation estimate (5.9), its dual,
   square completion, mass telescoping and endpoint transport are now
   available, as are the actual nested baseline mass derivative, first variation,
   and baseline identities
   (4.36), (5.18), (5.19), scalar heat equation, Lemma 5.9 and optimized time-zero
   endpoint. The actual scalar insertion and optimality input inequalities are
   now available, as are `U′=Q`, its inward endpoint form and Lemma 5.8. Use
   the checked `Q′`/`U″` negative-square identities, endpoint-safe Hessian
   calculus and new depth-uniform C3/C4 bounds. The old `1/√v` spatial
   estimate is superseded on actual inputs by Step 33's uniform bounds.
   The full nested second mass bound and its depth-uniform invariant are
   checked in Step 30; do not redo the scalar cumulant or nested derivative
   theory or the now completed outside-neighbor cases. Step 31
   transports both lambda gains and proves the positive-baseline far-left
   strict bound; Step 33 adds the local-left quadratic bound, but compactness
   remains open. Both neighbor
   interval endpoint constructions and both correction adapters are checked.
   Do not replace `2ψ(t)`
   with `2φ(t)`.
2. Apply the completed conditional Proposition 2.3/convergence deduction and
   Step 32's exact mass/interior-overlap reduction once the uniform Theorem 2.4
   bound is proved. The reduction already preserves fixed-level minimality
   and the original convergence quantifiers; no further coincident-overlap
   stationarity argument is needed.
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
