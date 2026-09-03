# Roadmap

Concrete, ordered work items. Each maps to a statement in `Targets/Milestones.lean` and a
numbered result in `blueprint/blueprint.tex`. Items are sized roughly
(S = hours, M = days, L = weeks, XL = months).

## Phase 0 — make the skeleton build  (S–M)

- [ ] `lake exe cache get && lake build` succeeds (Tier 1). Expected: yes, unchanged code.
- [ ] `lake build ParisiFormula` succeeds (Tier 2). Expected: yes; the ported file was
      verified on Lean 4.32.0, we are on 4.32.1.
- [ ] `lake build Targets` elaborates (Tier 3). Expected: a few repairs needed — these
      statements were written blind. Fix until only `sorry` warnings remain.
- [ ] CI green on GitHub (`.github/workflows/build.yml`).

## Phase 1 — Milestone 1: the thermodynamic limit  (M–L)

- [ ] Make `cov_deriv_diag` and `cov_deriv_offdiag_nonpos` in
      `ParisiFormula/GuerraToninelli.lean` non-`private` (they are needed by 1b).
- [ ] **1a** `free_entropy_le_annealed`: Jensen + Gaussian mgf. (S–M)
      Ingredients exist: `abs_magnetization_le`, `exp_magnetization_le`, and the Gaussian
      moment lemmas in `Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean`.
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

- [ ] Port `port/ParisiOperator.lean` (operator `T_{m,v}`, semigroup law) to Lean 4.32. (S–M)
- [ ] Reconcile `Targets.parisiStep` with `Parisi.T` (probably: define `parisiStep` via `T`). (S)
- [ ] **2a** `parisiFunctional_rsScheme` — sanity check of normalisations. Do this early;
      if it fails, the *definitions* are wrong. (M)
- [ ] Moderate-growth / integrability lemmas for `parisiF` at every level. (M)
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

## Housekeeping (any time)

- [ ] Set up `leanblueprint` so `blueprint/blueprint.tex` renders as a website with the
      dependency graph.
- [ ] Consider upstreaming the Gaussian IBP lemmas to Mathlib (general-purpose).
- [ ] Decide whether to keep the `Lemmas.SpinGlass` module names (zero-diff vendoring)
      or rename to `ParisiFormula.Core.*` (cleaner, but touches every import).
