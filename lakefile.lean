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
  where the machinery for Milestones 3 and 4 already lives, fully proved.

The narrowness of the original vendoring is also what made `port/` unusable: those files
were cut from a *different* fork (`or4nge19/SpinGlass`) and referenced API that the
eight-file slice did not include.  See `port/README.md`.

`Lemmas/` is retained on disk for reference but is no longer a build target.

## Build targets

* `ParisiFormula` (default): our own work.
* `Targets`: statements of the theorems we are aiming for; contains `sorry` by design.
-/

package ParisiFormula where
  -- Keep options identical to the upstream projects so imported files compile unchanged.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require QuantitativeStrictAT from git
  "https://github.com/njimaMath/research_public.git" @ "main" / "RSAT"

/-- Tier 2: new work for this project. -/
@[default_target]
lean_lib ParisiFormula where
  globs := #[.submodules `ParisiFormula]

/-- Tier 3: target statements (contain `sorry` on purpose). -/
lean_lib Targets where
  globs := #[.submodules `Targets]
