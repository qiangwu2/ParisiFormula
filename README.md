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
  The local-right estimate (Proposition 5.2) is checked for the reduced schemes
  used in the proof, including zero first overlap and the terminal interval.
  The far-right strict improvement (Proposition 5.6) is also checked,
  including the terminal mass and a deficit independent of system size.
  The negative initial interval (Proposition 5.4) is now checked for reduced
  schemes, preserving the original shared field and free energy.
  Proposition 5.7's outside-neighbor bound is now checked for the reduced
  near-minimizing schemes used in the proof, including both signs, all trial
  intervals, zero first overlap and time zero. Its positive deficit is
  independent of system size. Continuous scalar comparisons now give uniform
  gaps on compact subregions, and the inserted overlap sequences agree at
  adjacent breakpoints, compact right outside-trial bounds, and the scalar
  zero-variance list bridge are checked.
  Adjacent sorted-tag boundary gluing, lambda-deficit transport, finite compact
  cover bookkeeping, terminal padding, and positive-time negative-overlap
  compact bounds are now checked. Initial negative-overlap compact bands and
  same-trial far-left/far-right pressure-gap compact bounds are also checked;
  the level-indexed finite-cover bridge now produces the exact eventual
  quadratic-bound quantifier. The final all-region uniform Theorem 2.4
  instantiation remains; Theorem 2.2 and the final formula are still open.

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
