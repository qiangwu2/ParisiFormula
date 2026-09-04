# Roadmap

## Critical path to the goal

**Goal: Talagrand's proof of the Parisi formula (Ann. of Math. 163 (2006)) — Target 4.**

Target 4 is `Tendsto (fun N => s_N) atTop (𝓝 (parisiValue β h))`, which follows from

* **limsup ≤** — Target 3' , itself immediate from Target 3 (Guerra's RSB bound) via
  `parisiValue_le`; and
* **liminf ≥** — Talagrand's coupled-replica lower bound (Milestone 4), whose induction on
  the number of RSB levels needs **Target 2b** (regularity of `𝒫_k` in the parameters).

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
- [ ] **2b** Lipschitz continuity in `(m, q)`. (L) — **statement corrected, still unproved.**
      It previously read `∀ k, ∃ C, ∀ s s'`, allowing the constant to depend on `k`, which
      cannot control `parisiValue = inf_k inf_{(m,q)} 𝒫_k`: nothing survives the infimum over
      all `k` unless `C` is uniform in `k`.  `∃ C` is now hoisted outside `∀ k`.  Under the
      Talagrand route this target is **load-bearing** (the induction on RSB levels needs
      regularity of `𝒫_k` in the parameters), not optional.
      The `ℓ¹` form of the right-hand side should still be checked against Talagrand when the
      Milestone 4 blueprint is written; the uniformity in `k` is not negotiable.
      Likely proof route: `parisiStep` is non-expansive in the sup-norm of its argument
      (`|T A - T A'| ≤ ‖A - A'‖`, uniformly in `m`), which propagates a parameter
      perturbation through the backward recursion level by level.

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
