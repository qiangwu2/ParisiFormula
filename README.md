# ParisiFormula

A Lean 4 formalisation project for the **Parisi formula** for the Sherrington–Kirkpatrick
spin glass, following Guerra's interpolation bounds and Talagrand's proof
(*Ann. of Math.* 163, 2006).

**Status (September 4, 2026):** the SK-model version of Talagrand's **Theorem 2.1**
(`guerra_identity`) is proved, including endpoint continuity and an explicit nonnegative,
bounded squared-overlap remainder. The Guerra RSB upper bound and its thermodynamic
upper-bound consequence are also proved without `sorry` dependencies. Build-time axiom
checks live in [`Targets/GuerraAudit.lean`](Targets/GuerraAudit.lean).

**The full Parisi formula is not yet complete:** Theorem 2.2 remains the one open theorem
on the current critical path. Three older, off-path placeholders remain in
[`Targets/Milestones.lean`](Targets/Milestones.lean). See [`docs/ROADMAP.md`](docs/ROADMAP.md)
for the current status and [`blueprint/blueprint.tex`](blueprint/blueprint.tex) for the
mathematical outline and its formalisation status.

**Theorem 2.2 progress:** [`Targets/TalagrandConvergence.lean`](Targets/TalagrandConvergence.lean)
proves the deduction from an explicit mass-weighted overlap-concentration bound to
uniform convergence of the actual cascade on `[0,t₀]`. The tail-to-remainder estimate,
endpoint-safe differential inequality, and final quantifier assembly are checked without
placeholders. The concentration hypothesis itself is **not yet proved**; the original
Theorem 2.2 placeholder has not been removed or relocated.

[`Targets/CoupledCascade.lean`](Targets/CoupledCascade.lean) now proves both identities
in **Lemma 2.7** for the unrestricted coupled cascade: its pressure is `2φ(t)` and its
iterated tilted expectations are the individual replica probabilities `μ_r`.
[`Targets/ReplicaMeasure.lean`](Targets/ReplicaMeasure.lean) connects those probabilities
to the existing mass-weighted remainder and proves that per-level tail bounds imply the
concentration input above.

[`Targets/ConstrainedCascade.lean`](Targets/ConstrainedCascade.lean) now defines the
overlap-constrained cascade and proves the **deterministic induction in Lemma 2.6**:
the log tilted event probability is bounded by the mass times the constrained pressure
gap. Attainable overlap, positivity, and the positive-mass restriction are checked.
[`Targets/CoupledConcentration.lean`](Targets/CoupledConcentration.lean) now proves
Gaussian concentration and the exponential expectation estimate in **standard Gaussian
coordinates**, using the SK spectral coefficients and shared outer field. The constants
are explicit and uniform in `N` and `t`. Joint measurability, integrability, and the
required `O(√N)` Lipschitz bound are proved, not assumed.

[`Targets/TalagrandProposition25.lean`](Targets/TalagrandProposition25.lean) now completes
**Lemma 2.6** for `0 ≤ t ≤ 1` and **Proposition 2.5** for `0 < t < 1`, in the abstract
SK-disorder formulation. The change of Gaussian law and the outer-average identities
are proved, giving `Ψ(t,u) ≤ 2φ(t) − ε ⇒ μ_r(R=u) ≤ K exp(-N/K)` with explicit `K`
independent of `N` and `t`. The interior-time proposition is sufficient for the
existing endpoint-safe convergence deduction.
**Theorem 2.4 is now in progress:**
[`Targets/CoupledLambda.lean`](Targets/CoupledLambda.lean) proves the λ-interacting
single-site formula from §5, exact factorization at zero interpolation time, and
the overlap-penalty comparison through the existing coupled cascade.
[`Targets/CoupledLambdaPressure.lean`](Targets/CoupledLambdaPressure.lean) proves
the averaged comparison `Ψ(t,u) ≤ Pλ(t) − λu`, with `P₀(t) = 2φ(t)` and
a size-independent 1-Lipschitz bound in λ. These results do **not** yet give
Theorem 2.4's improvement relative to `2ψ(t)`: the covariance derivative bound
of Theorem 3.1 and the §4–§5 parameter-variation estimates remain open.
The deduction of Proposition 2.3 is checked conditionally on the quadratic bound;
the leading-zero-mass scheme reduction is now exact.
Theorem 2.2 itself remains open.

[`Targets/CoupledFiniteStep.lean`](Targets/CoupledFiniteStep.lean) now reuses RSAT's
general Gaussian transforms to build arbitrary finite paired-field recursions:
site factorization, continuity, and differentiation in λ are proved at every
depth. Shared and independent steps are connected to the existing cascade.
[`Targets/TalagrandSecondInterpolation.lean`](Targets/TalagrandSecondInterpolation.lean)
now defines the second interpolation for `q(r−1) ≤ u ≤ q(r)` with nonnegative
overlap and proves both endpoint results: **(5.8)** `η(1) = Ψ(t,u)` and **(5.17)**
`η(0) ≤ 2 log 2 + V(λ,m,v(u)) − λu`. The inserted masses, overlap sequence,
nonnegative Gaussian variances, N-site tensorization, and λ-differentiation of
the actual scalar `V` are checked. The definitions use canonical Gaussian
coordinates with the combined variances of `Z + √(1−w)y`.
[`Targets/TalagrandRightInterpolation.lean`](Targets/TalagrandRightInterpolation.lean)
now supplies the dual right-interval construction and both endpoints, with the
inserted level shared and its paired mass halved.
[`Targets/TalagrandRightZero.lean`](Targets/TalagrandRightZero.lean) proves its
zero-coupling baseline and reuses Lemma 5.9's curvature bound for the optimized
right-interval time-zero gain.
**Still open:** the derivative inequality between these endpoints, the negative-overlap
and other overlap cases, and the §4–§5 optimality estimates. The endpoint
results alone do not prove Theorem 2.4 or Theorem 2.2.

[`Targets/ConstrainedFiniteState.lean`](Targets/ConstrainedFiniteState.lean) now
connects the actual constrained terminal to RSAT's finite-state log partition,
proving its first and mixed second disorder derivatives.
[`Targets/CoupledCovariance.lean`](Targets/CoupledCovariance.lean) contracts that
Hessian with the SK covariance and proves the four-overlap square completion.
[`Targets/SecondInterpolationAlgebra.lean`](Targets/SecondInterpolationAlgebra.lean)
proves the sign and telescoping calculation on pp. 240–241 and identifies the
inserted correction in (5.9). **The missing analytic step is still to identify
the derivative of the full nested pressure with this covariance expression.**
The algebraic bound is not presented as a proved bound on `η′`.

[`Targets/CoupledCascadeDeriv.lean`](Targets/CoupledCascadeDeriv.lean) now propagates
the actual constrained-terminal first disorder derivative through every paired
level with fixed variances, retaining zero masses and a depth-independent bound.
The tilted-observable rules retain the mass covariance term.
[`Targets/CoupledCascadeSecond.lean`](Targets/CoupledCascadeSecond.lean) extends
this to the actual mixed disorder Hessian at every depth, with a uniform-in-disorder
bound, and proves Gaussian-coordinate and summed-trace integration by parts.
[`Targets/CoupledCascadeField.lean`](Targets/CoupledCascadeField.lean) proves the
separate replica-field first and mixed second derivatives at every depth, including
their spin-observable formulas, field-uniform bounds, and measurability.
[`Targets/CoupledCascadeVariance.lean`](Targets/CoupledCascadeVariance.lean) now
proves the positive-variance heat generator for an additional independent or shared
level of the actual constrained cascade, including zero mass. Spatial-direction
linearity and the independent two-field Gaussian packing are checked. Simultaneous
variation of every level and the disorder, and identification with replica weights,
are still needed for the full interpolation derivative.
[`Targets/ParisiMassDerivative.lean`](Targets/ParisiMassDerivative.lean) reuses
Mathlib's moment-generating-function calculus for the scalar mass derivative,
its entropy identity and nonnegativity.
[`Targets/ParisiMassZero.lean`](Targets/ParisiMassZero.lean) identifies the actual
mass-zero branch with an analytic divided difference: its derivative is half the
variance, and mass monotonicity now holds on all of `ℝ`. Nested Section 4
mass-variation estimates are not yet proved.
[`Targets/TalagrandSection5Zero.lean`](Targets/TalagrandSection5Zero.lean) proves
**(5.18)** `V(0,m,v)=2T(v,m)` and **(5.19)** `V(0,m_(r−1),v)=2A₀(h)`.
The baseline uses the Gaussian semigroup with zero mass and zero variance included.
[`Targets/ParisiVarianceDerivative.lean`](Targets/ParisiVarianceDerivative.lean) and
[`Targets/Section4Variance.lean`](Targets/Section4Variance.lean) prove the scalar heat
equation **(4.4)** on every actual Parisi input, including zero mass, at positive
variance. Spatial second derivatives, joint variance/field differentiation, and
the moving-field chain rule are checked; the nested optimality estimates remain open.
[`Targets/Section4SplitDerivative.lean`](Targets/Section4SplitDerivative.lean) now
proves the genuine two-step split-variance identity **(4.11)** for every actual
Parisi input, including zero masses, on the interior variance interval. Higher
mixed derivatives, variance-endpoint stationarity, and the full Section 4
optimality estimates remain open.
[`Targets/Section4SplitMonotone.lean`](Targets/Section4SplitMonotone.lean) and
[`Targets/Section4NestedMonotone.lean`](Targets/Section4NestedMonotone.lean) extend
the comparison to the closed variance interval and every actual outer level of
`T`, using continuity rather than assuming endpoint derivatives.
[`Targets/Section4NestedDerivative.lean`](Targets/Section4NestedDerivative.lean)
also propagates the actual variance derivative through the full `T`, with
`|∂v T| ≤ (m−m_(r−1))/2` independent of depth on the interior interval.
The corresponding Lipschitz bound holds on the closed variance interval.
[`Targets/Section4InsertedScheme.lean`](Targets/Section4InsertedScheme.lean)
constructs the admissible inserted scalar scheme and identifies its functional
with **(4.37)**. The near-global and fixed-level optimality hypotheses now give
the actual inequalities **(4.30)** and **(4.31)**, including zero masses and
coincident overlaps. These inputs do not yet prove the uniform variation bounds.
[`Targets/CoupledLambdaCurvature.lean`](Targets/CoupledLambdaCurvature.lean) proves
**Lemma 5.9** with the level-independent bound `0 ≤ ∂²λ V ≤ 1`.
[`Targets/TalagrandLambdaGain.lean`](Targets/TalagrandLambdaGain.lean) optimizes λ
to give the actual time-zero endpoint gain. Identifying `∂λ V(0)` with `U′`
(Lemma 5.8) and transporting the gain to time one remain separate obligations.
[`Targets/TalagrandOverlapTail.lean`](Targets/TalagrandOverlapTail.lean) now proves
the finite-overlap deduction from a uniform Theorem 2.4 quadratic bound to
Proposition 2.3 and uniform convergence on `[0,t₀]`, for a fixed scheme with
positive first mass. [`Targets/RSBSchemeReduction.lean`](Targets/RSBSchemeReduction.lean)
removes that mass restriction exactly, preserving the actual pressure, the functional,
and fixed-level minimality. The original Theorem 2.2 quantifiers now follow from a
uniform quadratic bound for positive-first-mass schemes. That bound remains unproved;
no unconditional completion of Theorem 2.2 is claimed.
[`Targets/RSBSchemeMassReduction.lean`](Targets/RSBSchemeMassReduction.lean) further
removes every equal adjacent mass, preserving the same quantities. This completes
the mass-strictness part of **(2.19)**, not strictness of the overlap sequence.
Its final conditional theorem reduces the original Theorem 2.2 to the uniform
quadratic bound for strictly increasing mass sequences alone.

Development follows the reuse-first rules in [`AGENTS.md`](AGENTS.md); the concrete
reuse inventory is recorded in [`docs/PROVENANCE.md`](docs/PROVENANCE.md).

## Project milestones

1. **Existence of the thermodynamic limit** (Guerra–Toninelli superadditivity + Fekete).
2. **The finite-step Parisi functional** (Talagrand's recursion; no PDE) and its continuity.
3. **Guerra's replica-symmetry-breaking upper bound** `F_N ≤ 𝒫_k(m,q)`.
4. **Talagrand's lower bound**, hence the Parisi formula. (Long-term.)

The active proof route is Talagrand (2006); the next critical step is Theorem 2.2, not
the separate Guerra–Toninelli development in milestone 1.

---

## Setting up (no prior Lean experience assumed)

Steps are for macOS/Linux; on Windows use WSL or follow the equivalent installer links.
Allow time and disk space for Lean, the dependencies, and the Mathlib build cache.

### 1. Install `elan` (the Lean version manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your terminal afterwards. `elan` reads the file `lean-toolchain` in this
repository and automatically installs the exact Lean version we use (`v4.32.1`).

### 2. Install VS Code and the Lean 4 extension

Download [VS Code](https://code.visualstudio.com/), open it, go to Extensions
(`Ctrl/Cmd+Shift+X`), search **"lean4"** and install the extension by *leanprover*.

### 3. Get this repository and the prebuilt Mathlib

```bash
git clone --branch worktree-parisi-phase1 https://github.com/qiangwu2/ParisiFormula.git
cd ParisiFormula
lake exe cache get      # fetch the compiled Mathlib cache
```

The current proof development is on `worktree-parisi-phase1`. `lake-manifest.json`
locks the dependency revisions; no dependency update is needed to reproduce this build.

### 4. Build

```bash
lake build                       # default: the ParisiFormula library and its dependencies
lake build ParisiFormula Targets  # both local libraries, including the axiom guards
bash scripts/check.sh            # both builds plus source-placeholder checks/report
```

For the completed Theorem 2.1, upper bounds, Lemma 2.7, and convergence dependency audit:

```bash
lake build Targets.GuerraAudit
```

`Targets` contains proved results alongside four remaining placeholders. Those warnings
do not mean a failed build, but a successful build alone does not certify the full Parisi
formula. `GuerraAudit` checks that Theorem 2.1 and both upper bounds depend only on
`propext`, `Classical.choice`, and `Quot.sound`—not `sorryAx` or extra axioms. It also
checks Lemma 2.7, the replica-measure decomposition, Lemma 2.6 including concentration
and change of law, interior-time Proposition 2.5, the §5 λ endpoint/pressure comparison,
the imported-analytic finite paired recursion and its tensorization,
the full-depth fixed-variance disorder Hessian and Gaussian Stein identities,
scalar mass/variance calculus, Lemma 5.9 and the optimized scalar endpoint,
zero-lambda identities, exact equal-mass compression, and the conditional
finite-overlap/convergence deductions, including the strict-mass bridge.
This does not certify the still-open Theorem 2.4 or Proposition 2.3. CI requires both
local libraries to build; it does not ignore target or audit failures.

Open the folder in VS Code and click into any `.lean` file: the Lean extension shows the
proof state live in the side panel ("Lean Infoview").

### If something fails

Copy the **entire** error message (the terminal output, or the red squiggle text in
VS Code) and paste it to your collaborator/assistant. Most first-run errors are one of:

- forgot `lake exe cache get` (symptom: build runs for hours, or "missing .olean" errors);
- network hiccup during cache download (just rerun `lake exe cache get`);
- Lean elaboration errors: these are not expected and must be fixed. Only the recorded
  placeholder warnings are allowed.

---

## Project layout and build targets

```
ParisiFormula/
├── lakefile.lean                 two local libraries; Mathlib and RSAT dependencies
├── lean-toolchain                Lean v4.32.1
├── AGENTS.md                     Talagrand objective, reuse-first policy, verification rules
├── lake-manifest.json            locked dependency revisions, including RSAT
├── ParisiFormula/                default library; no source placeholders
│   ├── AnnealedBound.lean            Gaussian moments and the annealed upper bound
│   ├── GuerraToninelli.lean          conditional superadditivity and Fekete argument
│   ├── InterpolationDeriv.lean       covariance/Hessian sign calculations
│   ├── ParisiOperator.lean           ported bounded-function smoothing semigroup
│   ├── ParisiOperatorGrowth.lean     semigroup extended to linear growth
│   ├── GaussianCosh.lean             Gaussian integrability and cosh identities
│   ├── GaussianConcentration1D.lean  one-dimensional concentration estimates
│   ├── GaussianExpCompare.lean       comparison of Gaussian log-exp integrals
│   ├── GaussianStein.lean            one-dimensional Stein identity
│   ├── CoordStein.lean               Gaussian-Hilbert coordinate/trace IBP
│   └── PiStein.lean                  product-Gaussian coordinate IBP
├── Targets/                     second library; completed proofs and open targets
│   ├── Milestones.lean               Parisi recursion, continuity, minimizer; 3 open lemmas
│   ├── CascadeEndpoint.lean          N-site cascade and endpoint factorization
│   ├── CascadeDeriv.lean             one-dimensional tilted chain rule
│   ├── CascadeDerivPi.lean           N-site tilted chain rule and growth bounds
│   ├── CascadeSecondPi.lean          second derivatives of tilted averages
│   ├── CascadeFieldPi.lean           conditional field integration by parts
│   ├── CascadeContinuityPi.lean      parameter continuity through smoothing
│   ├── Talagrand.lean                Theorem 2.1 proved; Theorem 2.2 open; final deduction
│   ├── TalagrandConvergence.lean     overlap concentration implies Theorem 2.2 (conditional)
│   ├── CoupledCascade.lean          unrestricted coupled cascade; both Lemma 2.7 identities
│   ├── ReplicaMeasure.lean          individual replica probabilities and remainder decomposition
│   ├── CoupledGrowth.lean           interacting two-field Gaussian integrability and growth
│   ├── CascadeEventBound.lean       one-step tilted-event comparison and positivity
│   ├── ConstrainedCascade.lean      constrained pressure; deterministic Lemma 2.6 induction
│   ├── CoupledLipschitz.lean        nonexpansiveness and Gaussian-input stability of cascades
│   ├── CoupledMeasurability.lean    joint measurability in disorder and replica fields
│   ├── CoupledConcentration.lean    Gaussian tail and event decay in standard coordinates
│   ├── CoupledGaussianLaw.lean      spectral/abstract disorder joint-law identity
│   ├── CoupledOuterExpectation.lean  outer-average, pressure-gap and replica identities
│   ├── TalagrandProposition25.lean   Lemma 2.6 and interior-time Proposition 2.5
│   ├── CoupledLambda.lean           Section 5 spin formula, endpoint and cascade penalty
│   ├── CoupledLambdaPressure.lean   averaged lambda comparison, normalization and stability
│   ├── CoupledFiniteStep.lean       RSAT-backed general finite recursion and site factorization
│   ├── CoupledEndpoint.lean         inserted-level cascade growth, tensorization and constraint bound
│   ├── CoupledReindex.lean          zero-variance insertion/deletion and physical field rescaling
│   ├── TalagrandSection5.lean       explicit inserted masses/variances and scalar V
│   ├── TalagrandSecondInterpolation.lean  second-interpolation endpoints (5.8), (5.17), left interval
│   ├── CoupledSharedInsertion.lean    exact shared zero-variance insertion and cutoff adapter
│   ├── TalagrandRightInterpolation.lean  dual right-interval construction and both endpoints
│   ├── TalagrandRightZero.lean         dual scalar baseline and optimized time-zero lambda gain
│   ├── ConstrainedFiniteState.lean   RSAT-backed first/second derivatives of the constrained terminal
│   ├── CoupledCovariance.lean        four-overlap covariance, square completion and terminal Hessian
│   ├── SecondInterpolationAlgebra.lean  algebraic remainder sign, telescoping and (5.9) correction
│   ├── CoupledCascadeDeriv.lean       fixed-variance nested disorder derivatives and tilted covariance
│   ├── CoupledCascadeSecond.lean      full-depth mixed disorder Hessian and Gaussian Stein identities
│   ├── CoupledCascadeField.lean       separate replica-field first/mixed derivatives and spin directions
│   ├── CoupledCascadeVariance.lean    actual independent/shared one-level heat generators
│   ├── ParisiMassDerivative.lean      scalar mass derivative, entropy and monotonicity via Mathlib
│   ├── ParisiMassZero.lean            analytic mass-zero extension and half-variance derivative
│   ├── ParisiStepSemigroup.lean       scalar semigroup including zero masses and variances
│   ├── ParisiVarianceDerivative.lean  Gaussian heat generator and actual scalar variance derivative
│   ├── Section4Variance.lean          actual Parisi C2, heat equation and joint variance/field calculus
│   ├── Section4SplitDerivative.lean   actual two-step split-variance identity (4.11), including zero masses
│   ├── Section4SplitMonotone.lean     joint continuity and closed-interval split comparison
│   ├── Section4NestedMonotone.lean    closed-interval monotonicity through every outer scalar level
│   ├── Section4NestedDerivative.lean  actual full T variance derivative with depth-independent bound
│   ├── Section4InsertedScheme.lean    actual inserted functional (4.37), optimality inputs (4.30)--(4.31)
│   ├── TalagrandSection5Zero.lean     actual scalar T and zero-lambda identities (5.18), (5.19)
│   ├── CoupledLambdaCurvature.lean    level-independent lambda curvature: Lemma 5.9
│   ├── TalagrandLambdaGain.lean       optimized scalar and actual second-interpolation time-zero gain
│   ├── TalagrandOverlapTail.lean      finite-overlap deduction from a uniform Theorem 2.4 bound
│   ├── RSBZeroMassPiSemigroup.lean    N-site zero-mass Gaussian semigroup
│   ├── RSBMassPiSemigroup.lean        N-site semigroup at arbitrary mass
│   ├── RSBSchemeReduction.lean        exact leading-zero-mass reduction and conditional Theorem 2.2
│   ├── RSBSchemeMassReduction.lean    exact equal-mass compression: mass-strictness part of (2.19)
│   └── GuerraAudit.lean              axiom guards for completed critical-path results
├── .lake/packages/              generated dependency checkout; not tracked
│   ├── mathlib/                      Mathlib v4.32.1
│   └── QuantitativeStrictAT/         active RSAT source for Lemmas.* imports
├── Lemmas/SpinGlass/             historical RSAT copies; NOT a local build target
├── port/                        historical Lean 4.28 sources; NOT built (see port/README.md)
├── blueprint/blueprint.tex       mathematical outline and proof-status annotations
├── docs/ROADMAP.md               current critical path and historical checkpoints
├── docs/PROVENANCE.md            dependency pins and origins of copied/ported sources
├── scripts/check.sh             strict local build/check entry point
└── .github/workflows/build.yml   required builds for both libraries
```

Only `ParisiFormula` and `Targets` are declared as local `lean_lib` targets.
The imported `Lemmas.*` modules come from the `QuantitativeStrictAT` dependency, not
the historical copies under the repository's `Lemmas/` directory. Older notes call these
the upstream tier, Tier 2, and Tier 3; those are not three local build targets.

---

## Credits and licence

This project would not exist without two open-source Lean libraries, both Apache-2.0:

- **[or4nge19/SpinGlass](https://github.com/or4nge19/SpinGlass)** by Matteo Cipollina —
  the finite-volume spin-glass calculus and the Gaussian IBP machinery.
- **[njimaMath/research_public](https://github.com/njimaMath/research_public)** —
  the RSAT and perceptronFixed artifacts (arXiv:2608.23413), which extend the above and
  contain the Guerra–Toninelli blueprint we build on.

All vendored files keep their original copyright headers. See `NOTICE` and
`docs/PROVENANCE.md`. This project is released under the Apache License 2.0 (`LICENSE`).

## Contributing

Not yet open for external contributions; issues and questions are welcome. Development
should follow the current critical path in `docs/ROADMAP.md`, retain the Talagrand (2006)
proof route, and preserve the completed-theorem axiom guards.
