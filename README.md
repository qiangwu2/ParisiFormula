# ParisiFormula

A Lean 4 formalisation project for the **Parisi formula** for the Sherrington–Kirkpatrick
spin glass, following Guerra's interpolation bounds and Talagrand's proof
(*Ann. of Math.* 163, 2006).

**Status (September 5, 2026):** the SK-model version of Talagrand's **Theorem 2.1**
(`guerra_identity`) is proved, including endpoint continuity and an explicit nonnegative,
bounded squared-overlap remainder. The Guerra RSB upper bound and its thermodynamic
upper-bound consequence are also proved without `sorry` dependencies. Build-time axiom
checks live in [`Targets/GuerraAudit.lean`](Targets/GuerraAudit.lean).

**The full Parisi formula is not yet complete:** Theorem 2.2 remains the one open theorem
on the current critical path. Three older, off-path placeholders remain in
[`Targets/Milestones.lean`](Targets/Milestones.lean). See [`docs/ROADMAP.md`](docs/ROADMAP.md)
for the current status and [`blueprint/blueprint.tex`](blueprint/blueprint.tex) for the
mathematical outline and its formalisation status.

**Latest checkpoint:** Lemma 5.8 is checked, together with actual split-replica
weights, inward endpoint derivatives and further Section 4 derivative inputs.
The full build and all 393 axiom guards pass. The interpolation inequality,
`U″`/uniform optimality estimates and remaining overlap cases are still open.

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

[`Targets/CoupledReplicaWeights.lean`](Targets/CoupledReplicaWeights.lean)
constructs the actual normalized constrained Gibbs weights at every depth and
identifies the disorder and spatial first derivatives with their moments.
It also constructs split-level replica weights by forming the inner product
before the outer Gaussian averages, proving normalization and product-moment
identities. SK and independent/shared field contractions are checked. The full
Hessian/heat telescoping and averaged covariance identity remain open.

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
linearity and the independent two-field Gaussian packing are checked. Identification
of the simultaneous derivative with the replica covariance expression is still
needed for the full interpolation inequality.
[`Targets/CoupledNestedVariance.lean`](Targets/CoupledNestedVariance.lean) now
propagates a single original level's variance derivative through every unchanged
outer level of the actual constrained cascade. The varying variance must be
positive; zero fixed variances and masses are included. Its derivative bound
has no additional outer-depth factor.
[`Targets/CoupledDisorderInterpolation.lean`](Targets/CoupledDisorderInterpolation.lean)
proves the other partial contribution: at fixed field variances, the actual
Gaussian-averaged disorder derivative is the nested Hessian trace divided by
`2N`. Radial linearity, outer differentiation, and continuity at zero disorder
variance are checked. These partial identities are not yet the simultaneous
derivative of the full second interpolation.
[`Targets/CoupledVariancePressure.lean`](Targets/CoupledVariancePressure.lean)
also carries the individual variance derivative through the actual Gaussian
disorder average, proving the required measurability and domination.
[`Targets/Section5VarianceFaces.lean`](Targets/Section5VarianceFaces.lean) checks
that any zero variance before time one is an identically zero coordinate in
either neighbor-interval construction. No positive-variance assumption is
therefore imposed on coincident overlap increments.
[`Targets/Section5InterpolationPath.lean`](Targets/Section5InterpolationPath.lean)
proves the actual square-root coefficient derivatives, including constant zero
coordinates and zero disorder amplitude. The compact-parameter continuity rules
in [`Targets/CoupledPathContinuity.lean`](Targets/CoupledPathContinuity.lean) and
[`Targets/ConstrainedPathContinuity.lean`](Targets/ConstrainedPathContinuity.lean)
cover simultaneous disorder, field and variance paths of the actual cascade.
[`Targets/Section5InterpolationContinuity.lean`](Targets/Section5InterpolationContinuity.lean)
passes this through the Gaussian average, proving continuity on `[0,1]` of both
actual second interpolations. No derivative inequality is inferred from continuity.
[`Targets/ConstrainedJointTerminal.lean`](Targets/ConstrainedJointTerminal.lean)
proves joint smoothness of the actual terminal in disorder and both fields.
[`Targets/CoupledJointInterpolation.lean`](Targets/CoupledJointInterpolation.lean)
then proves genuine joint differentiability of the full cascade along a disorder
path and all variance paths, using dominated differentiation of the moving Gaussian
shifts. Positive variances and locally constant zero coordinates are covered.
The successor derivative is its normalized Gaussian expectation of the actual
inner joint derivative composed with the moving shift, before integration by parts.
[`Targets/Section5JointInterpolation.lean`](Targets/Section5JointInterpolation.lean)
specializes this to both actual second-interpolation integrands for `0<w<1`, at
fixed disorder. [`Targets/CoupledPathPressure.lean`](Targets/CoupledPathPressure.lean)
now proves derivative measurability and affine Gaussian-norm domination on one
common time neighborhood, passing the simultaneous derivative through the outer
Gaussian expectation. [`Targets/Section5PressureDerivative.lean`](Targets/Section5PressureDerivative.lean)
gives genuine derivatives of both actual pressures on `0<w<1`. Identification
with the replica covariance expression and its inequality remains open.
[`Targets/CoupledPathDecomposition.lean`](Targets/CoupledPathDecomposition.lean)
proves the needed finite-dimensional joint regularity, fixing zero-variance
coordinates, and identifies the actual time derivative with the disorder
direction plus the sum of original-level variance derivatives.
[`Targets/CoupledPathPressureFormula.lean`](Targets/CoupledPathPressureFormula.lean)
integrates this decomposition and applies the existing radial Gaussian Stein
identity. Both physical pressures now have explicit trace-plus-heat formulas,
with disorder coefficient `t/(2N)`. These analytic terms still need to be
identified with Talagrand's replica-overlap expressions and bounded.
[`Targets/ParisiMassDerivative.lean`](Targets/ParisiMassDerivative.lean) reuses
Mathlib's moment-generating-function calculus for the scalar mass derivative,
its entropy identity and nonnegativity.
[`Targets/ParisiMassZero.lean`](Targets/ParisiMassZero.lean) identifies the actual
mass-zero branch with an analytic divided difference: its derivative is half the
variance, and mass monotonicity now holds on all of `ℝ`.
[`Targets/ParisiMassLocal.lean`](Targets/ParisiMassLocal.lean) adds local domination,
including a two-sided mass-zero bound.
[`Targets/Section4MassDerivative.lean`](Targets/Section4MassDerivative.lean) now
differentiates the actual full `T` at every original baseline mass, including
zero and both variance endpoints. This justifies the actual **(4.42)**
`U = 2∂m T`; higher mixed mass/variance identities and uniform optimality
estimates are still open.
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
[`Targets/Section4FirstVariation.lean`](Targets/Section4FirstVariation.lean)
identifies **(4.46)** with the genuine baseline mass derivative of this `Φ`
and proves that it vanishes at `u=q_r`. This is not yet stationarity in `u`.
[`Targets/Section4UBounds.lean`](Targets/Section4UBounds.lean) proves the actual
`U` is nondecreasing, 1-Lipschitz, and satisfies `0≤U(v)≤v` on the closed
variance interval when `m_(r−1)<1`. The strict-mass reduction supplies this
condition; zero baseline mass and degenerate intervals are included. The actual
first variation is continuous and `β²/2`-Lipschitz in overlap.
[`Targets/Section4VarianceFactor.lean`](Targets/Section4VarianceFactor.lean)
factors `∂vT=(m−m_(r−1))Q/2`, with an actual nested normalized squared-slope
average `Q∈[0,1]` defined without division by the mass gap. The endpoint-safe
integral identity is proved. [`Targets/ParisiJointMassContinuity.lean`](Targets/ParisiJointMassContinuity.lean)
proves true joint mass/variance/field continuity of the scalar step and its slope,
including zero mass. [`Targets/Section4VarianceFactorContinuity.lean`](Targets/Section4VarianceFactorContinuity.lean)
propagates this to the actual `Q` on the full closed mass/variance rectangle and
proves its integrability even at baseline. [`Targets/Section4UPrime.lean`](Targets/Section4UPrime.lean)
takes the right mass limit in the integral identity and proves `U′=Q`, with
`0≤U′≤1` on the interior when `m_(r−1)<1`, including a zero baseline. It also
differentiates the actual overlap first variation.
[`Targets/Section4UEndpoints.lean`](Targets/Section4UEndpoints.lean) extends both
derivative formulas to the closed physical interval as inward derivatives;
the numerical `derivWithin` identity requires a nonzero variance gap.
[`Targets/Section4EndpointOptimality.lean`](Targets/Section4EndpointOptimality.lean)
proves `f(q_(r−1))≥0` for `r≥2` and a strict adjacent mass gap, using an actual
fixed-level competitor and a zero-variance deletion. The initial interval is
not included because `m₀=0` is fixed. `U″`, uniform higher-mass estimates,
and the remaining stationarity identities are still open.
[`Targets/ParisiSlopeVariance.lean`](Targets/ParisiSlopeVariance.lean) now proves
the actual positive-variance derivative of the inner slope, its joint field/variance
chain rule, and the moving squared-slope derivative. A common domination bound
is independent of the field and recursion depth, but requires variance bounded
away from zero. This is a prerequisite for differentiating `Q`, not yet `U″`.
[`Targets/RightInterpolationAlgebra.lean`](Targets/RightInterpolationAlgebra.lean)
supplies the exact dual correction, and
[`Targets/Section4RightVariation.lean`](Targets/Section4RightVariation.lean)
reuses (4.11) by reflection: the actual dual two-step derivative and full
closed-interval antimonotonicity are checked for decreased inserted mass.
[`Targets/Section4RightDerivative.lean`](Targets/Section4RightDerivative.lean)
now propagates the derivative through the full right recursion with
`|∂vT_right|≤(m_r−m)/2`. Its Lipschitz bound holds on the closed interval,
including zero masses and the last interval. Dual stationarity remains open.
[`Targets/CoupledLambdaCurvature.lean`](Targets/CoupledLambdaCurvature.lean) proves
**Lemma 5.9** with the level-independent bound `0 ≤ ∂²λ V ≤ 1`.
[`Targets/TalagrandLambdaGain.lean`](Targets/TalagrandLambdaGain.lean) optimizes λ
to give the actual time-zero endpoint gain.
[`Targets/Section5LambdaUPrime.lean`](Targets/Section5LambdaUPrime.lean) now proves
**Lemma 5.8**: the actual zero-λ derivative is `Q`, hence `U′` at baseline mass
below one. The `Q` identity includes every nonnegative inserted mass and both
variance endpoints; the endpoint `U′` statement uses inward derivatives.
The optimized time-zero gain now contains `(Q−u)²/2`. Transporting that gain
to time one and the uniform optimality estimates remain open.
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
The audit also covers the actual Gaussian-averaged disorder and individual
variance derivatives, degenerate variance coordinates, full baseline mass
differentiation and first variation, and dual correction/comparison.
It now checks the actual simultaneous pointwise cascade derivative and its
normalized recursion, both physical path specializations, Gaussian-averaged
endpoint continuity, the bounds for `U` and `f`, the normalized variance factor,
and the full dual variance derivative. It also checks the averaged trace-plus-heat
formulas, actual normalized split-replica weights and contractions, inward endpoint
derivatives, noninitial endpoint optimality, slope-derivative domination and
Lemma 5.8 with the identified `Q` gain. There are 393 completed-result guards.
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
│   ├── RightInterpolationAlgebra.lean exact dual deterministic correction and its baseline
│   ├── Section4RightVariation.lean    dual split derivative and full closed-interval antimonotonicity
│   ├── Section4RightDerivative.lean   full dual variance derivative and closed mass-gap Lipschitz bound
│   ├── ConstrainedFiniteState.lean   RSAT-backed first/second derivatives of the constrained terminal
│   ├── CoupledCovariance.lean        four-overlap covariance, square completion and terminal Hessian
│   ├── CoupledReplicaWeights.lean    actual Gibbs/split-replica weights, moments and contractions
│   ├── SecondInterpolationAlgebra.lean  algebraic remainder sign, telescoping and (5.9) correction
│   ├── CoupledCascadeDeriv.lean       fixed-variance nested disorder derivatives and tilted covariance
│   ├── CoupledCascadeSecond.lean      full-depth mixed disorder Hessian and Gaussian Stein identities
│   ├── CoupledCascadeField.lean       separate replica-field first/mixed derivatives and spin directions
│   ├── CoupledCascadeVariance.lean    actual independent/shared one-level heat generators
│   ├── CoupledNestedVariance.lean     one original variance derivative through every outer level
│   ├── CoupledDisorderInterpolation.lean  actual Gaussian-averaged disorder derivative and radial Stein
│   ├── CoupledVariancePressure.lean   individual variance derivative through the Gaussian disorder average
│   ├── Section5VarianceFaces.lean     positive-or-identically-zero alternative for actual level variances
│   ├── Section5InterpolationPath.lean actual coefficient derivatives, including constant zero coordinates
│   ├── CoupledPathContinuity.lean     compact-parameter Gaussian continuity through all moving levels
│   ├── ConstrainedPathContinuity.lean actual constrained-terminal/cascade joint path continuity
│   ├── ConstrainedJointTerminal.lean actual terminal joint smoothness in disorder and both fields
│   ├── CoupledJointInterpolation.lean simultaneous cascade/field differentiation by moving Gaussian shifts
│   ├── Section5JointInterpolation.lean actual left/right pointwise interpolation differentiability
│   ├── CoupledPathPressure.lean      actual simultaneous derivative through the Gaussian disorder average
│   ├── CoupledPathDecomposition.lean proved finite-parameter chain rule and disorder-plus-variance sum
│   ├── CoupledPathPressureFormula.lean actual averaged Hessian-trace plus finite heat formula
│   ├── Section5PressureDerivative.lean actual pressure derivatives and both physical trace-plus-heat formulas
│   ├── Section5InterpolationContinuity.lean Gaussian averaging and both actual endpoint-continuity theorems
│   ├── ParisiMassDerivative.lean      scalar mass derivative, entropy and monotonicity via Mathlib
│   ├── ParisiMassZero.lean            analytic mass-zero extension and half-variance derivative
│   ├── ParisiMassLocal.lean           local derivative domination and two-sided mass-zero bound
│   ├── Section4MassDerivative.lean    actual full baseline mass derivative and U, including mass zero
│   ├── Section4FirstVariation.lean    actual Phi first variation (4.46) and its upper-overlap zero
│   ├── Section4UBounds.lean           monotonicity of U and closed-interval Lipschitz bounds for U and f
│   ├── Section4VarianceFactor.lean    normalized squared-slope factor Q and endpoint-safe integral identity
│   ├── ParisiJointMassContinuity.lean joint scalar mass/variance/field continuity, including mass zero
│   ├── Section4VarianceFactorContinuity.lean actual Q continuity and integrability at baseline
│   ├── Section4UPrime.lean            actual U′=Q and overlap derivative of the first variation
│   ├── Section4UEndpoints.lean        inward derivatives of U and f at the physical endpoints
│   ├── Section4EndpointOptimality.lean fixed-level lower-endpoint f≥0 for noninitial intervals
│   ├── ParisiStepSemigroup.lean       scalar semigroup including zero masses and variances
│   ├── ParisiVarianceDerivative.lean  Gaussian heat generator and actual scalar variance derivative
│   ├── Section4Variance.lean          actual Parisi C2, heat equation and joint variance/field calculus
│   ├── ParisiSlopeVariance.lean       actual slope velocity, moving squared slope and uniform local domination
│   ├── Section4SplitDerivative.lean   actual two-step split-variance identity (4.11), including zero masses
│   ├── Section4SplitMonotone.lean     joint continuity and closed-interval split comparison
│   ├── Section4NestedMonotone.lean    closed-interval monotonicity through every outer scalar level
│   ├── Section4NestedDerivative.lean  actual full T variance derivative with depth-independent bound
│   ├── Section4InsertedScheme.lean    actual inserted functional (4.37), optimality inputs (4.30)--(4.31)
│   ├── TalagrandSection5Zero.lean     actual scalar T and zero-lambda identities (5.18), (5.19)
│   ├── CoupledLambdaCurvature.lean    level-independent lambda curvature: Lemma 5.9
│   ├── TalagrandLambdaGain.lean       optimized scalar and actual second-interpolation time-zero gain
│   ├── Section5LambdaUPrime.lean      actual zero-lambda derivative Q=U′ (Lemma 5.8) and identified gain
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
