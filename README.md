# ParisiFormula

A Lean 4 formalisation of Talagrand's proof of the Parisi formula
(*Annals of Mathematics* 163, 2006, 221–263), in the
Sherrington–Kirkpatrick (SK) model with exact covariance.

## Status

- **Proved:** the SK version of Theorem 2.1, Guerra's RSB upper bound,
  Proposition 5.7, Talagrand's uniform quadratic estimate (Theorem 2.4),
  Theorem 2.2, and the Parisi formula.
  The Theorem 2.4 proof covers every overlap sign, breakpoint, physical level,
  terminal case, and the zero-first-overlap boundary. Theorem 2.2 combines this
  estimate with Proposition 2.3 and the convergence argument. The final theorem
  then proves convergence of the free energy `F_N` to the value given by the
  Parisi formula.

**The full critical-path proof is formalised in the project's stated
exact-covariance SK setting.** The numbered theorems and final formula have
build-time axiom checks. Three older placeholders remain in `Targets/Milestones.lean`,
but they are not dependencies of the Parisi-formula theorem.

See the [roadmap](docs/ROADMAP.md) for the completed proof chain and the three
optional declarations outside it. The detailed development checkpoints are
preserved in the [roadmap history](docs/ROADMAP_HISTORY.md). Development follows
Talagrand's 2006 proof and reuses Mathlib and the locked RSAT dependency where possible.

## Build

Install Lean's `elan` version manager if needed (macOS/Linux):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your terminal, then:

```bash
git clone https://github.com/qiangwu2/ParisiFormula.git
cd ParisiFormula
lake exe cache get
bash scripts/check.sh
```

The script builds both local libraries, runs the completed-result axiom guards,
and reports remaining placeholders. Plain `lake build` builds only the default
supporting library, not all proof targets.

[lean-toolchain](lean-toolchain) selects Lean 4.32.1;
[lake-manifest.json](lake-manifest.json) locks dependency revisions.
No dependency update is needed. For interactive proof inspection, open the
project in VS Code with the Lean 4 extension.

## Project guide

- [Targets/](Targets/) — main formalisation and supporting proof modules.
  [TalagrandCore.lean](Targets/TalagrandCore.lean) contains the foundational
  interpolation and upper bound; [TalagrandTheorem24.lean](Targets/TalagrandTheorem24.lean)
  contains Theorem 2.4; and [TalagrandFinal.lean](Targets/TalagrandFinal.lean)
  exports the canonical Theorem 2.2 and Parisi formula through the public
  [Talagrand.lean](Targets/Talagrand.lean) façade.
  [GuerraAudit.lean](Targets/GuerraAudit.lean) checks completed-result dependencies.
- [ParisiFormula/](ParisiFormula/) — supporting library, without proof placeholders.
- [Roadmap](docs/ROADMAP.md) — current proof status, verification and optional follow-up work.
- [Roadmap history](docs/ROADMAP_HISTORY.md) — archived Steps 1–53 and their historical frontiers.
- [Blueprint](blueprint/blueprint.tex) — mathematical outline with formalisation status.
- [Provenance](docs/PROVENANCE.md) — dependency pins, source credits and reusable results.
- [Working rules](AGENTS.md) — proof scope, reuse policy and verification requirements.

Only `ParisiFormula` and `Targets` are local build libraries. `Lemmas.*`
imports come from the RSAT dependency; the root `Lemmas/` and `port/`
directories are historical references, not build targets.

## Credits and licence

Built on [Mathlib](https://github.com/leanprover-community/mathlib4),
[or4nge19/SpinGlass](https://github.com/or4nge19/SpinGlass) and
[njimaMath/research_public](https://github.com/njimaMath/research_public).
Licensed under [Apache 2.0](LICENSE); see [NOTICE](NOTICE) for attribution.

Issues and questions are welcome; external contributions are not yet open.
