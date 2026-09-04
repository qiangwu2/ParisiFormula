import Lake
open Lake DSL

/-!
# ParisiFormula — Lake configuration

## Dependency on RSAT instead of vendoring

`Lemmas/SpinGlass/` originally held eight files copied out of
`njimaMath/research_public` (RSAT).  RSAT is on the **same** toolchain and Mathlib pin as
this project (`v4.32.1`), and its library exports exactly the `Lemmas.SpinGlass.*` module
names our files already import, so we now `require` it rather than copying from it.

Two reasons this is better than the vendoring it replaces:

* the eight vendored files were byte-identical to upstream, so nothing local is lost; and
* RSAT has ~150 modules, of which only eight were taken.  Depending on it makes the rest
  available — `Lemmas.AT.PsiContinuity` (continuity of the Guerra–Talagrand functional in
  its parameters), `Lemmas.GuerraTalagrand.Bound.*` (the GT bound, including the coupled
  two-field form), `Lemmas.Cavity.TalagrandCavity`, `Lemmas.Concentration.*` — which is
  where supporting interpolation and concentration results live. These do not replace
  the still-open local Theorem 2.2 in `Targets/Talagrand.lean`.

The narrowness of the original vendoring is also what made `port/` unusable: those files
were cut from a *different* fork (`or4nge19/SpinGlass`) and referenced API that the
eight-file slice did not include.  See `port/README.md`.

`Lemmas/` is retained on disk for reference but is no longer a build target.

## Build targets

* `ParisiFormula` (default): the local supporting library, without source placeholders.
* `Targets`: the finite-step functional and cascade proofs, the completed SK Theorem 2.1,
  and four remaining placeholders (Theorem 2.2 plus three off-path legacy lemmas).
  This target also builds `Targets.GuerraAudit`, which guards the completed results
  against placeholder or additional-axiom dependencies. Both libraries must build.
-/

package ParisiFormula where
  -- Keep options identical to the upstream projects so imported files compile unchanged.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require QuantitativeStrictAT from git
  "https://github.com/njimaMath/research_public.git" @ "main" / "RSAT"

/-- Supporting library: local proofs and adapted upstream results. -/
@[default_target]
lean_lib ParisiFormula where
  globs := #[.submodules `ParisiFormula]

/-- Cascade proofs, remaining targets, and completed-theorem axiom audits. -/
lean_lib Targets where
  globs := #[.submodules `Targets]
