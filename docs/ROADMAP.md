# Roadmap

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
  - [ ] Gaussian IBP rewrite of `Φ'` (adapt `port/GuerraIBP.lean`); (M)
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
- [ ] Reconcile `Targets.parisiStep` with `Parisi.T` (probably: define `parisiStep` via `T`). (S)
- [x] **2a** `parisiFunctional_rsScheme` — sanity check of normalisations. **Done.**
      The definitions are correct as written: the `parisiF` off-by-one fixed in `fa63079`
      is right, and the statement holds for *all* real `β` (no `0 < β` needed), because
      `√(β² q) = |β| √q` agrees with `β √q` under the symmetric Gaussian
      (`integral_reflect_stdGaussian`).  Supporting lemmas are in
      `ParisiFormula/GaussianCosh.lean`.
- [ ] Moderate-growth / integrability lemmas for `parisiF` at every level. (M)
      Partially available for the `log cosh` layer: `integrable_log_cosh_stdGaussian`
      in `ParisiFormula/GaussianCosh.lean`, via `0 ≤ log cosh y ≤ |y|`.
- [ ] **2b** Lipschitz continuity in `(m, q)`. (L)

## Phase 3 — Milestone 3: Guerra's RSB bound  (L–XL)

- [ ] Finite Gaussian tree: the field `∑ᵢ σᵢ ∑_p z_p^i √(β²(q_{p+1}-q_p))` as an
      `IsGaussianHilbert` vector in `EnergySpace N`, with its covariance kernel. (L)
- [ ] Hierarchical expectation `Z_p = (E_p Z_{p+1}^{m_p})^{1/m_p}` and endpoint `φ(0)`. (L)
- [ ] Derivative `φ'(t)` via Gaussian IBP and positivity of each term. (XL)
- [ ] **3** `guerra_rsb_bound`; **3'** `limsup_free_entropy_le_parisiValue`.

## Phase 4 — Milestone 4: Talagrand's lower bound  (XL, open-ended)

Blueprint chapter to be written after Phase 3. Starting point: RSAT's
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
