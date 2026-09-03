import Lake
open Lake DSL

/-!
# ParisiFormula — Lake configuration

The project is split into three build targets, ordered by risk:

* `SpinGlassCore`  (default): the vendored, already machine-verified library
  (`Lemmas/SpinGlass/`), copied verbatim from njimaMath/research_public (RSAT),
  itself derived from or4nge19/SpinGlass.  A plain `lake build` builds only this.
* `ParisiFormula`: our own work (`ParisiFormula/`).  Build with `lake build ParisiFormula`.
* `Targets`: statements of the theorems we are aiming for (`Targets/`).  These contain
  `sorry` by design and may need small repairs.  Build with `lake build Targets`.

Toolchain and Mathlib are pinned to exactly the versions RSAT was verified against
(`lean-toolchain`, `lake-manifest.json`), so the vendored code should compile unchanged.
-/

package ParisiFormula where
  -- Keep options identical to the upstream projects so vendored files compile unchanged.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

/-- Tier 1: vendored core (verified upstream, no `sorry`). -/
@[default_target]
lean_lib SpinGlassCore where
  globs := #[.submodules `Lemmas]

/-- Tier 2: new work for this project. -/
lean_lib ParisiFormula where
  globs := #[.submodules `ParisiFormula]

/-- Tier 3: target statements (contain `sorry` on purpose). -/
lean_lib Targets where
  globs := #[.submodules `Targets]
