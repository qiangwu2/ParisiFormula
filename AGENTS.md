# Project objective and working rules

The user's goal is to formalize Talagrand's proof of the Parisi formula in
*Annals of Mathematics* 163 (2006), 221–263. Follow that proof, in the project's
stated SK setting. Read `README.md` and `docs/ROADMAP.md` for the current frontier;
do not substitute a different proof or pursue off-path legacy targets.

## Reuse before new proofs

- Search Mathlib, the locked RSAT dependency, and existing local modules before
  developing a new lemma or analytic framework.
- Prefer imports and small proved bridges between definitions to duplicate
  proofs, copied dependency files, or new infrastructure.
- Check full hypotheses, quantifiers, Gaussian conventions, signs, normalization,
  zero-mass cases, and proof dependencies before reusing a result. A narrower
  final theorem can still contain reusable general-purpose supporting lemmas.
- `Lemmas.*` resolves to `.lake/packages/QuantitativeStrictAT/RSAT/`, not the
  historical root `Lemmas/` or `port/` directories. Keep dependencies pinned unless
  a justified change is requested.
- Record useful matches and genuine mismatches in `docs/PROVENANCE.md` and the
  roadmap so future sessions do not repeat the same search.

## Verification and handoff

- Do not weaken the target, assume the missing conclusion, introduce axioms, or
  move an existing placeholder into a helper and call the theorem complete.
- Add axiom regression guards for completed critical-path results and run
  `bash scripts/check.sh` before committing.
- Keep README status/layout, roadmap, blueprint, and provenance consistent with
  the actual checked statements. Distinguish supporting lemmas from a completed
  numbered theorem in the paper.
- Preserve unrelated user work. The user requests verified updates pushed to
  the existing GitHub development branch; commit and push normally, never force
  push, and confirm synchronization. Report any permission or network blocker.
