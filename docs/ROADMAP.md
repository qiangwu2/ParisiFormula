# Roadmap

## Current status

The main objective is complete: Talagrand's proof of the Parisi formula from
*Annals of Mathematics* 163 (2006), 221--263, is formalized in the project's
exact-covariance Sherrington--Kirkpatrick setting.

For every inverse temperature `β > 0`, external field `h`, and family of SK
disorders with covariance

`E[H_N(σ) H_N(τ)] = (N β² / 2) R(σ,τ)²`,

the public theorem `SpinGlass.Targets.parisi_formula` proves that the free energy
`F_N = (1/N) E log Z_N` converges to the infimum of the finite-step Parisi
functional.

## Completed proof chain

- [x] Define finite replica-symmetry-breaking schemes and the finite backward
      Gaussian recursion, including the zero-mass expectation branch.
- [x] Prove that the set of finite-step Parisi-functional values is nonempty and
      bounded below.
- [x] Prove continuity and existence of a minimizer at each fixed number of levels
      (Talagrand's (2.17)).
- [x] Prove Theorem 2.1, including differentiation through the cascade, Gaussian
      integration by parts, the nonnegative overlap remainder, and both endpoints.
- [x] Deduce Guerra's finite-volume upper bound and the corresponding limsup bound.
- [x] Formalize the coupled and constrained replica constructions, Lemmas 2.6--2.7,
      Proposition 2.3, and the concentration-to-convergence argument.
- [x] Prove the Section 4 optimality estimates and Propositions 5.1--5.7, covering
      both overlap signs, breakpoints, zero first overlap, terminal padding, and all
      physical levels.
- [x] Assemble the uniform quadratic estimate of Theorem 2.4.
- [x] Integrate Theorem 2.4 into the exact conclusion of Theorem 2.2.
- [x] Combine Theorem 2.2 with Guerra's upper bound to prove the Parisi formula.
- [x] Audit the completed theorem chain for proof placeholders and nonstandard axioms.

There are no unchecked mathematical items on the proof path above.

## Public theorem entry points

| Result | Lean declaration | Source |
|---|---|---|
| Theorem 2.1 | `guerra_identity` | [`Targets/TalagrandCore.lean`](../Targets/TalagrandCore.lean) |
| Theorem 2.4 | `talagrand_theorem_2_4` | [`Targets/TalagrandTheorem24.lean`](../Targets/TalagrandTheorem24.lean) |
| Theorem 2.2 | `talagrand_theorem_2_2` | [`Targets/TalagrandFinal.lean`](../Targets/TalagrandFinal.lean) |
| Parisi formula | `parisi_formula` | [`Targets/TalagrandFinal.lean`](../Targets/TalagrandFinal.lean) |

[`Targets/Talagrand.lean`](../Targets/Talagrand.lean) is the stable public façade.
[`Targets/GuerraAudit.lean`](../Targets/GuerraAudit.lean) checks the dependencies of
the completed results. The public Theorems 2.2 and 2.4 and the final formula depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Remaining declarations outside the proof path

Three older declarations in [`Targets/Milestones.lean`](../Targets/Milestones.lean)
still contain explicit placeholders. They are retained as optional, independent
projects and are not imported by the proof of Theorem 2.2 or the Parisi formula.

| Declaration | Status and issue | Why it is not required |
|---|---|---|
| `Φ_monotoneOn` | Optional standalone Guerra--Toninelli interpolation. It still needs dominated differentiation, Gaussian integration by parts for a packaged independent Gaussian triple, and the covariance-trace sign argument. | The completed Parisi formula directly proves convergence of `F_N`; its proof does not use this separate construction. |
| `free_entropy_tendsto` | Optional assembly theorem depending on `Φ_monotoneOn`. | Its conclusion--existence of the thermodynamic limit--is already implied by the stronger final convergence theorem. |
| `parisiFunctional_lipschitz` | Optional Lipschitz estimate uniform in the number of RSB levels. A merely Lipschitz recursion gives only a square-root modulus, so a depth-uniform second-derivative argument is needed. | Talagrand's finite-scheme proof uses fixed-level continuity and a fixed-level minimizer, both of which are proved. It does not require extending the functional to general Parisi measures. |

These three placeholders are reported by `bash scripts/check.sh` so that they cannot
be mistaken for completed results. They do not occur in the transitive dependencies
of `talagrand_theorem_2_2` or `parisi_formula`.

## Verification

Run the complete local check with:

```bash
bash scripts/check.sh
```

The script:

1. builds the supporting `ParisiFormula` library;
2. builds all `Targets`, including the final theorem and dependency audit;
3. verifies that `ParisiFormula/` contains no `sorry`, `admit`, or new `axiom`;
4. reports the three optional placeholders above.

The mathematical blueprint is [`blueprint/blueprint.tex`](../blueprint/blueprint.tex),
and dependency/source details are in [`docs/PROVENANCE.md`](PROVENANCE.md).

## Optional follow-up work

The following would improve presentation or reuse but is not part of completing
Talagrand's SK proof:

- render the LaTeX blueprint as a browsable dependency graph;
- consider contributing the general-purpose Gaussian integration-by-parts lemmas
  upstream to Mathlib;
- formalize one or more of the three independent declarations listed above;
- obtain an external mathematical and Lean code review of the completed theorem chain.

## Development history

The detailed Steps 1--53, including the obstacles and the frontier at each historical
checkpoint, are preserved in [`docs/ROADMAP_HISTORY.md`](ROADMAP_HISTORY.md). Unchecked
boxes in that archive describe what was open *at that checkpoint* and must not be read
as the current project status.
