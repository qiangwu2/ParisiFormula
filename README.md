# ParisiFormula

A Lean 4 formalisation of Talagrand's proof of the Parisi formula
(*Annals of Mathematics* 163, 2006, 221–263), in the
Sherrington–Kirkpatrick (SK) model with exact covariance.

## Status

- **Proved:** the SK version of Theorem 2.1 and Guerra's RSB upper bound,
  including its thermodynamic upper-bound consequence.
- **In progress:** Theorem 2.2. Quantitative optimality, stationarity at every
  level after exact scheme reduction, uniform curvature, and the local-left
  and initial-interval estimates (Propositions 5.1 and 5.3) are checked.
  The local-right estimate is also checked at every level with a positive
  left overlap gap, including the terminal interval. The zero-first-overlap
  curvature case, the remaining overlap/sign
  cases, and their uniform assembly into Theorem 2.4 are still open.

**The full Parisi formula is not yet formalised.** Completed results have
build-time axiom checks; open proof placeholders remain. A successful build
does not mean the entire proof is complete.

See the [roadmap](docs/ROADMAP.md) for the checked/open checklist, next steps
and detailed progress. Development follows Talagrand's 2006 proof and reuses
Mathlib and the locked RSAT dependency where possible.

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
  Start with [Talagrand.lean](Targets/Talagrand.lean);
  [GuerraAudit.lean](Targets/GuerraAudit.lean) checks completed-result dependencies.
- [ParisiFormula/](ParisiFormula/) — supporting library, without proof placeholders.
- [Roadmap](docs/ROADMAP.md) — proof plan, detailed checkpoints and remaining work.
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
