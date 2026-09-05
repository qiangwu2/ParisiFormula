# Dependencies and source provenance

## Active build dependencies

`lakefile.lean` declares two local libraries, `ParisiFormula` and `Targets`. Their
upstream dependencies are locked in `lake-manifest.json`:

| Dependency | Source | Locked revision |
|---|---|---|
| `mathlib` | `leanprover-community/mathlib4`, tag `v4.32.1` | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `QuantitativeStrictAT` | `njimaMath/research_public`, subdirectory `RSAT` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` |

`Lemmas.*` imports resolve to the RSAT dependency under
`.lake/packages/QuantitativeStrictAT/RSAT/`, not the historical root-level `Lemmas/`
copies. Neither `Lemmas/` nor `port/` is a local build target. The `main` selector in
the RSAT dependency declaration does not replace the pinned revision when reproducing
the checked-in manifest; `lake update` would deliberately refresh dependencies.

## Reuse inventory for the Talagrand lower bound

Search the locked dependency before developing new analytic machinery. The
following matches were checked in the active RSAT source, not the historical
copies. `Targets/GuerraAudit.lean` checks the completed local bridges and their
transitive dependencies for the standard Lean axioms only.

| Existing result | Local use or remaining adaptation |
|---|---|
| `AT.gtTerminal`, `AT.gtTerminal_zero`, `AT.deriv_gtTerminal_zero` | `coupledSite_eq_gtTerminal` bridges the paper's hyperbolic expression to RSAT's exponential expression; local normalization and derivative proofs now reuse RSAT. |
| `AT.sum_bool_pair_exp_eq_four_mul_exp_gtTerminal`, `AT.sum_pair_exp_sum_eq_prod_sum_exp` | Reused by the local one-site and N-site partition identities in `CoupledLambda.lean`. |
| `GTFrame.finiteStep`, `finiteStepD`, `step0_good`, `stepM_good`, `goodFam_fLbase` | `CoupledFiniteStep.lean` and `CoupledEndpoint.lean` iterate the existing transforms and regularity results. `TalagrandSection5.lean` specializes them to the actual inserted-level scalar `V` and its lambda derivative. No new dominated differentiation proof. |
| `AT.gtVectorStep`, `gtScalarStep`, `gtVectorStep_sum` | Directly reused for the N-site recursion and tensorization; integrability and positivity are discharged using `GoodFam`. Proved bridges identify the old shared step and the composition giving its independent step. |
| `AT.gtStateLogPartition`, `contDiff_gtStateLogPartition`, `fderiv_gtStateLogPartition_apply`, `fderiv_gtStateGibbs_apply` (`Bound/FiniteState.lean`) | Used in `ConstrainedFiniteState.lean` on `AT.ConstrainedPair N u`, with an exact positive-Hamiltonian bridge and actual first/mixed second terminal derivatives. `CoupledCascadeSecond.lean` now propagates the disorder Hessian through all fixed-variance levels. |
| `AT.gtCoefficientCLM` (`Bound/Comparison.lean`) | Defines the pair-disorder map `U ↦ (U(σ)+U(τ))` as an existing continuous linear map; no new finite-dimensional map construction needed. |
| `AT.pairOverlapMatrix_self`, `spin_sum_eq_mul_overlap`, `gtCovariance_remainder` (`Bound/Basic.lean`) | Reused in `CoupledCovariance.lean` for the constrained diagonal, independent/signed-shared field contractions, and entrywise square completion. The SK spectral contraction reuses the already proved local `sk_covariance_spectral_sum`. |
| `Finset.sum_range_by_parts`, `sum_range_sub` (Mathlib) | Reused in `SecondInterpolationAlgebra.lean` for the mass-weighted telescoping identity. The inserted correction is proved equal to the existing `2 * parisiCorrection` plus the split-level term in (5.9). |
| `AT.hasDerivAt_gtOrdinaryPressure_ibp`, `gtOrdinaryPressure_one_le_zero_add_shiftedDiagonalGap` (`Bound/Comparison.lean`) | Generic finite-state covariance interpolation, but for the ordinary expected log partition, not an arbitrary nested positive-mass cascade. Reuse where its pressure matches; extend only the missing cascade layer. |
| `hasDerivAt_mgf`, `integrable_pow_mul_exp_of_mem_interior_integrableExpSet` (Mathlib `MGFAnalytic`) | `ParisiMassDerivative.lean` proves the actual scalar mass derivative. Existing Gaussian linear-growth integrability makes the exponential-integrability domain all of `ℝ`; no new dominated-differentiation proof. |
| Mathlib `analyticAt_cgf`, `has_fpower_series_dslope_fslope`, `iteratedDeriv_two_cgf_eq_integral` | `ParisiMassZero.lean` identifies the existing zero-mass expectation with the analytic divided difference and proves its half-variance derivative. It does not redefine the transform or assume a limit. |
| Mathlib `hasFDerivAt_integral_of_dominated_loc_of_lip'`; local Herbst sandwich, scalar mass analyticity, `CoupledParamDeriv.secondStep`, zero-mass semigroup | `ParisiMassLocal.lean` supplies anchored domination at mass zero and local positive-mass bounds. `Section4MassDerivative.lean` differentiates the actual full recursion at every original baseline, including zero and both variance endpoints. |
| `Real.self_sub_one_le_mul_log` (Mathlib) | Nonnegativity of the genuine normalized tilt's entropy, hence scalar mass monotonicity. Integrability and density normalization are checked. |
| Local `Parisi.T_add_of_hasLinearGrowth`, Mathlib `integral_conv`, `gaussianReal_conv_gaussianReal` | `ParisiStepSemigroup.lean` adapts the existing nonzero-mass semigroup and proves the actual expectation branch at mass zero. Both variance endpoints are allowed. |
| Local `independentStepPi_add`, `sharedStepPi_diag`, `parisiStepPi_sum`, `coupledFieldCascade_eq_sum` | `TalagrandSection5Zero.lean` derives the actual zero-lambda factorization (5.18); the semigroup then restores the original recursion for (4.36), (5.19). |
| Local `hasDerivAt_parisiStepPi_param`, `hasDerivAt_tiltAvg_param_pi` | `CoupledCascadeDeriv.lean` adapts the first derivative through independent/shared levels and the tilted covariance rules, retaining the actual mass coefficient. The finite-state terminal supplies concrete derivative inputs. |
| Mathlib mean value theorem and `measurable_lineDeriv`; local `stein_coord_of_hasDerivAt`, Gaussian affine-growth integrability | `CoupledCascadeSecond.lean` derives disorder continuity/measurability from the proved mixed Hessian, then proves actual coordinate and summed-trace Stein identities without extra analytic hypotheses. |
| Local `gaussianReal_stein_of_bound`, scalar spatial derivative formulas, and Gaussian exponential-growth integrability | `ParisiVarianceDerivative.lean` proves the positive-variance heat equation, retaining the actual mass-zero expectation. `Section4Variance.lean` applies it to every genuine Parisi input. |
| RSAT `GTFrame.goodTriple_finiteStep`; Mathlib `hasStrictFDerivAt_uncurry_coprod` | Joint continuity of the scalar step and its spatial derivatives, then joint variance/spatial differentiation in `Section4Variance.lean`; separate partial derivatives are not silently treated as joint differentiability. |
| RSAT `GoodTriple`; Mathlib `monotoneOn_of_deriv_nonneg`; local `parisiStepPi_mono_growth` | The two-step closed-interval comparison and its propagation through the actual `section4T`. Continuity plus interior derivatives suffice; no variance-endpoint derivatives are assumed. |
| Local `continuousOn_parisiStepPi_param`, finite-direction Gaussian packing, `stepK_mono_variance`; Mathlib compact-image bounds and dominated continuity | Generalize only the old parameter type (same proof), then `CoupledPathContinuity.lean` reuses the theorem at fixed variance 1 with moving shifts in the input. Actual terminal specialization and Gaussian averaging prove continuity of both physical interpolations at their endpoints. |
| Local full `T` mass derivative and variance comparison; Mathlib `HasDerivAt.tendsto_slope_zero_right`, `IsClosed.mem_of_tendsto` | `Section4UBounds.lean` derives actual `U` monotonicity and a unit Lipschitz bound by right mass quotients, without a mixed derivative. The baseline must be below 1. |
| Local normalized Gaussian means and spatial C2 bounds; Mathlib `intervalIntegral.integrableOn_deriv_of_nonneg`, `integral_eq_sub_of_hasDerivAt_of_le` | `Section4VarianceFactor.lean` exposes the genuine squared-slope factor, bounds it in `[0,1]`, and proves the full endpoint-safe variance integral identity. No division by a zero mass gap is used. |
| Local `section5InterpolationVariance_zero`, `section5Correction_eq`, `section4T_baseline`, `parisiFunctional_mergeEqualMass` | The actual scalar inserted scheme, formula (4.37), and both optimality comparisons (4.30)--(4.31). Reuses checked variance algebra and mass compression instead of duplicating finite-sum/semigroup proofs. |
| Local `stein_tiltWeightPi`, `hasDerivAt_parisiStepPi_param`; Mathlib measure-preserving finite product reindexing | `CoupledCascadeVariance.lean` proves the heat generator of an added independent/shared level of the actual fixed inner constrained cascade. The full varying-variance nested pressure remains to be assembled. |
| Local `CoupledParamDeriv.independentStep`, `.sharedStep`, and the checked one-level heat generator | `CoupledNestedVariance.lean` differentiates one original level via `Function.update v ℓ w` and propagates its actual heat seed through every unchanged outer level. Explicit growth and measurable normalized means discharge the local analytic hypotheses. |
| Local `pairedIndependentMean_sum`, `pairedSharedMean_sum`, coordinate Stein, and mixed Hessian; Mathlib dominated differentiation | `CoupledDisorderInterpolation.lean` proves radial disorder linearity, scaled Stein and the actual outer-average disorder derivative with normalization `1/(2N)`. Field variances remain fixed. |
| RSAT `GoodTriple`, `stepMD_le`, `stepMVar_nonneg`, and terminal `fLbaseDD = 1-fLbaseD²` | `CoupledLambdaCurvature.lean` supplies only the strengthened invariant `E ≤ 1-D²`. All analytic regularity is inherited. This gives Lemma 5.9 with constant 1, not RSAT's coarse depth-dependent bound. |
| Mathlib `convexOn_univ_of_deriv2_nonneg`, `ConvexOn.isMinOn_of_rightDeriv_eq_zero` | Tangent-quadratic estimate and explicit lambda optimization; `TalagrandLambdaGain.lean` applies this to the actual time-zero second-interpolation endpoint. |
| Local `talagrand_proposition_2_5`, replica-weighted-tail conversion, and endpoint-safe convergence; Mathlib exponential asymptotics | `TalagrandOverlapTail.lean` sums over at most `N+1` attainable Ising overlaps and proves the conditional concentration/convergence deduction. `RSBSchemeReduction.lean` removes its positive-first-mass restriction by exact equivalence; the uniform quadratic bound remains unproved. |
| Mathlib `measurePreserving_arrowProdEquivProdArrow`, `Measure.pi_map_pi`, Gaussian convolution; local scalar semigroup | `RSBZeroMassPiSemigroup.lean` proves the N-site expectation semigroup. Leading zero-mass deletion preserves the actual pressure and Parisi data; exact zero-variance padding transfers fixed-level minimality. |

The final `AT.twoReplica_GT_bound` has RS smart-path hypotheses (one overlap
parameter, positive `β` and `h`, and an interior RS overlap). It cannot replace
the finite-RSB Theorem 2.4 as stated. This mismatch does **not** exclude its
generic supporting modules above. The generic half-step calculus may likewise
help extend the ordinary-pressure comparison, but has not yet been adapted.

No dependency revision was changed and no upstream source was copied or edited.
The general finite recursion supplies λ-differentiation at fixed masses;
it does not itself assert mass-variation estimates. The identification with
Talagrand's `U′` is now proved by the local `Section5LambdaUPrime` adapter below.

### Section 5 endpoint specialization

The coefficients were checked against the [original Annals paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n1-p04.pdf),
pp. 252–253, equations (5.5)–(5.17). The paper's `k` is the local `k+1`.
For the left interval `q(r−1) ≤ u ≤ q(r)`, the inserted level is independent,
has mass `m`, and has frozen variance zero; outer shared masses are `m_p/2`.
The second interpolation is defined directly on standard Gaussian coordinates
using the combined variance of `Z + √(1−w)y`, with shared fields below `r` and
independent fields at/above `r`. Thus it does not require introducing and then
integrating out redundant Gaussian copies. The exact endpoint identities are
proved against the existing `constrainedPhi` and the explicit scalar recursion,
not assumed from a distributional identification.

`CoupledEndpoint.lean` reuses the existing interacting-step growth, order,
Fubini, and additive-constant results, together with RSAT's site tensorization.
`CoupledReindex.lean` supplies only algebraic changes of coordinates and deletion
of a zero-variance step. `TalagrandSecondInterpolation.lean` proves (5.8) and
(5.17) for this canonical construction. All are covered by axiom guards.
Theorem 3.1's nested-cascade derivative estimate is still missing; the ordinary
RSAT covariance comparison cannot be applied to this pressure without that extension.
The right-interval endpoints are now checked in `TalagrandRightInterpolation.lean`.
This dual construction follows the final paragraph of Section 4 (p. 250), used
in Propositions 5.2 and 5.6: insert the overlap after `q_r`, put mass `m/2` at
the new shared level, and split off variance `t β²(u-q_r)`. The frozen variance
there is zero, so the new cutoff adapter reuses the existing time-one identity.
`TalagrandRightZero.lean` reuses the zero-lambda diagonal factorization and
scalar semigroup to identify its actual dual scalar recursion and restore the
baseline at `m_r` (not `m_(r-1)`). The same sharp lambda-curvature invariant
gives the optimized time-zero gain; the dual `U′` is not yet identified.
Negative-overlap and general out-of-neighbor-interval cases remain separate work,
as do the uniform Section 4 optimality estimates.

### Covariance calculation and the remaining analytic gap

The calculation was checked against the same paper, pp. 239–241. The terminal
derivatives in `ConstrainedFiniteState.lean` are derivatives of the actual
`constrainedPairFieldBase`, not a separately postulated Gibbs family.
`constrainedPairSecond_SK_trace` contracts this Hessian with the actual abstract
SK spectral covariance. In contrast, `pairCovarianceExpression_eq` and `_le`
are deliberately statements about explicit normalized finite replica weights:
their expression has not been identified with `η′`. This is the remaining
nested differentiation/IBP obligation, not an assumption or relocated placeholder.

The local `hasDerivAt_parisiStepPi_param` and `hasDerivAt_tiltAvg_param_pi`
are now reused in `CoupledCascadeDeriv.lean`: first disorder derivatives
propagate through the entire actual paired cascade with fixed variances,
and tilted-observable derivatives retain the mass-weighted covariance term.
`CoupledCascadeSecond.lean` extends the mixed Hessian to arbitrary depth and
proves actual Gaussian-coordinate Stein identities, including the summed trace.
The uniform-in-disorder Hessian bound gives continuity of first directions via
Mathlib's mean value theorem; measurable line derivatives avoid duplicating
joint differentiation theory. This is not yet the varying-variance derivative
of the second interpolation or its identification with actual replica weights.
`CoupledCascadeField.lean` reuses the same induction with separate replica-field
directions represented as finite-state spin observables. Translation commutation
identifies the resulting derivatives with actual spatial derivatives, and the
coordinate spin bridges match the existing independent/signed-shared contractions.
The RSAT half-step modules were inspected: they supply a single fixed half-mass
transform, not the arbitrary finite sequence needed here. Their final comparison
does not close the nested-cascade gap. Do not repeat the finite-state or
square-completion proofs already connected by this step.

`CoupledNestedVariance.lean` now differentiates a genuine original variance
coordinate, written `Function.update v ℓ w`, through every unchanged outer
level. Its explicit seed is the checked independent/shared spatial heat
generator. Local variance-monotone growth bounds package the existing
`CoupledParamDeriv` hypotheses; normalized tilted means preserve the derivative
bound without an outer-depth factor. This is a positive-variance partial
derivative, not an assumed joint derivative for all level variances.

`CoupledDisorderInterpolation.lean` handles the other contribution in the
Section 3 Gaussian-IBP calculation: the terminal disorder amplitude. Finite
linearity of the actual propagated disorder direction identifies the radial
direction with its spectral sum. Coordinate Stein on `D_V F(aU)` gives the
factor `a` and the actual mixed Hessian; the existing bound is uniform in
disorder. Mathlib's dominated differentiation moves the amplitude derivative
through the outer Gaussian expectation. The square-root chain rule gives
the correctly normalized `1/(2N)` trace. The amplitude result holds at zero
as well; composition with the continuous square root gives zero-variance
continuity without claiming an endpoint variance derivative. Replica-weight
identification remains a separate obligation.

`CoupledVariancePressure.lean` closes the outer-average issue for an individual
field-variance derivative. It reuses the actual cascade's disorder continuity
and Mathlib's `measurable_of_tendsto_metrizable'` on forward difference quotients.
This provides disorder measurability of the actual derivative without assuming
joint differentiability. The uniform derivative bound then discharges the
dominated-differentiation hypotheses. For simultaneous interpolation, separate
partials do not by themselves justify the chain rule. The pointwise simultaneous
chain rule and outer averaging are now proved separately as described below;
identification with the replica covariance expression remains open.

`Section5VarianceFaces.lean` preserves degeneracies when applying that eventual
chain rule: each physical variance is `A+(1-w)B` with `A,B≥0`. Before `w=1`,
zero variance implies `A=B=0`, so the coordinate is constant. The proof applies
to both actual neighbor-interval sequences; no strict-overlap restriction is added.

`Section5InterpolationPath.lean` turns this alternative into genuine derivatives
of the square-root coefficients. At a zero face both frozen and varying parts
vanish, so the coefficient is constant; the displayed totalized quotient then
equals zero for a proved reason. The disorder path `sqrt(w*t)` is also handled
at `t=0`, not by assuming a square-root derivative at zero.

`CascadeContinuityPi.lean` now allows any first-countable parameter space in
its existing continuity theorem; the proof is unchanged. `CoupledPathContinuity.lean`
uses that theorem at variance 1 after moving the varying Gaussian coefficients
into the input. Compact images supply all uniform growth bounds. The existing
independent/shared finite-direction packing identifies this with the actual
coupled recursion, including its half-mass convention and zero branches.
`ConstrainedPathContinuity.lean` absorbs the two fields into RSAT's finite-state
potential and discharges terminal continuity and compact growth. Finally
`Section5InterpolationContinuity.lean` compares with zero disorder using the
proved uniform disorder Lipschitz bound. The resulting affine Gaussian-norm
domination justifies outer averaging and gives both actual physical pressures'
closed-interval continuity. This does not itself prove the interpolation derivative.

RSAT's `GoodFam` was inspected for reuse: its auxiliary coefficients are continuous,
but its supplied derivatives concern lambda, not this simultaneous moving path.
The direct Fréchet bridge below supplies that genuine mismatch without copying
upstream code or changing the locked dependency.

`ConstrainedJointTerminal.lean` reuses RSAT's smooth finite-state log partition
after absorbing the disorder and both replica fields, with Mathlib's `contDiff_piLp`
handling the energy-space coordinates. `CoupledJointInterpolation.lean` first
telescopes the existing single-coordinate variance Lipschitz estimates and combines
them with disorder and spatial Lipschitz estimates. Differentiable parameter paths
therefore have a local anchored difference bound, uniform in the replica fields.
Mathlib's anchored dominated differentiation of integrals then proves a joint
Fréchet derivative for the actual moving Gaussian shift. Linear/exponential growth
gives Gaussian domination, and measurable Fréchet derivatives give the derivative
integrand's measurability. The mass-zero expectation is handled separately from
the nonzero log-Laplace branch. Induction uses the existing independent/shared
packing, without treating separate partial derivatives as a joint derivative.
Visited variances must be positive at the base point or locally identically zero.
The successor identity retains the normalized Gaussian mean of the actual inner
joint derivative composed with the moving shift derivative. This is a proved
derivative candidate before integration by parts, not a postulated replica formula.
`Section5JointInterpolation.lean` discharges these hypotheses for the actual left
and right paths at `0<w<1`, with fixed disorder and their different cutoffs.
This module proves pointwise integrand differentiability.

`CoupledPathPressure.lean` obtains a single time neighborhood with a bound
`(A+B*‖U‖)*|z-w|` for every disorder `U`. The coefficients are chosen from the
scalar amplitude and finitely many variance paths before choosing `U`; a
disorder-dependent neighborhood would not justify outer dominated differentiation.
Derivative measurability uses measurable difference quotients with variances
clipped to `max(v,0)` only in those auxiliary quotients. Eventual nonnegativity
identifies them with the original path near the differentiation point, preserving
the original derivative. Mathlib's anchored Fréchet integral rule then proves
both derivative integrability and interchange with the Gaussian expectation.
`Section5PressureDerivative.lean` specializes to both actual physical pressures,
with exact `1/N` normalization and their distinct cutoffs. This closes outer
averaging, not the identification with Talagrand's replica covariance sum or its bound.

`CoupledPathDecomposition.lean` reuses the Gaussian log-Laplace derivative for
finite-dimensional parameters and proves the actual full joint induction.
It then varies disorder and finitely many active variance coordinates on a
face that fixes precisely the zero coordinates. Derivative uniqueness on
disorder lines and single-coordinate update lines identifies each basis value;
linearity of the proved Fréchet derivative gives the actual finite sum. The
remaining depth is `j-(l+1)`, with `l+1+(j-(l+1))=j` for every visited level.
`CoupledPathPressureFormula.lean` proves termwise integrability, splits the
expectation and reuses radial Stein: the disorder coefficient is `a′*a`, and
the heat terms retain their existing normalization. The physical specializations
in `Section5PressureDerivative.lean` reduce this to `t/(2N)`, including `t=0`
by its constant branch. Covariance eigenvalues are variances, not standard
deviations. The full replica-covariance identification and desired inequality
remain open.

`CoupledReplicaWeights.lean` reuses normalized paired derivative transport and
its finite-sum rules to transport the actual constrained terminal Gibbs
coordinates. Their nonnegativity, normalization, measurability and unit bound
are proved, as are the actual disorder/spatial first-derivative moments and
their SK and independent/shared field contractions. The SK spectral weights
are variances and contribute exactly `N*pairSKCovariance`; the shared formula
retains both signed off-diagonal overlaps.

For split-level replicas, the product of the two inner Gibbs coordinates is
formed **before** applying the remaining outer tilted means. Taking a product
of two fully averaged probabilities would give the wrong covariance term.
The shifted recursion uses profiles `m(l+i)`, `v(l+i)`, cutoff `d-l`, and the
actual level-l potential; an exact level-addition identity verifies this
restart. Positivity, normalization and both actual disorder/spatial product
moment identities are checked. The full Hessian/heat telescope and the final
Gaussian-averaged covariance identity have not been inferred from these facts.

`CoupledReplicaHessian.lean` supplies the missing actual Hessian expansion.
The two equal-mass independent tilts have cancelling intermediate covariance
products; the resulting rule is the same single covariance increment as for
one shared tilt at its actual mass. Existing bounded-observable transport
linearity expands the genuine full disorder/spatial Hessians under the actual
split weights. Adjacent-mass telescoping retains the initial `m₀−1` and final
`−m_j` coefficients; no endpoint value is silently assumed. All fixed masses
and variances may vanish.

`CoupledReplicaAverage.lean` extends the existing parameter-integral measurability
rules to disorder plus both fields. The proved unit bound makes every actual
split weight integrable for any measurable random disorder on a probability
space. Finite sum/integral interchange gives the averaged moment identities,
normalization and nonnegative completed-square remainder.
`CoupledReplicaTrace.lean` reuses the exact SK spectral covariance contraction
and constrained diagonal to identify the full genuine Hessian trace and its
outer expectation, with the exact factor `N`. This proves the disorder term,
not yet the combined trace-plus-heat interpolation covariance identity.

`CoupledReplicaHeat.lean` reuses the exact level-addition identity and bounded
transport linearity to carry inner Hessian and heat expressions through the
unchanged outer levels. The products remain at their original split level;
only their remaining outer depth increases. Packed independent and nested
equal-mass normalized means agree by uniqueness of genuine derivatives of
bounded perturbations, reusing the checked equality of potentials. Both actual
`constrainedLevelVarianceD` generators are identified with their coordinate
sums of replica expressions divided by two, through all remaining outer levels.
The algebraic identities include zero variances; they do not assert a variance
derivative there. Coordinate contraction into overlaps, outer averaging of
the heat terms and the full physical coefficient sum with the disorder trace
remain to be assembled. The desired interpolation inequality is not inferred
merely from the square completion.

### Scalar variation, baseline, and finite-overlap assembly

`ParisiSlopeVariance.lean` reuses the existing Gaussian-amplitude differentiation
lemma on `exp(mA)` and `A' exp(mA)`, then differentiates their quotient. This
gives the actual positive-variance slope velocity without needing an assumed
third derivative of `A` and without division by the mass, so mass zero is
retained. The joint chain rule uses the checked continuity of the actual
`parisiFSecond` and Mathlib's continuous-partial-derivative criterion.
The moving squared-slope formula includes the outer-field term
`-z B''/(2 sqrt(a-v))` with the negative sign required for (4.16).

Existing tilted Gaussian moment bounds give a field-independent velocity
bound, Gaussian integrability and a common bound on `0<lo≤v≤hi`, uniform in
`m∈[0,1]` and the actual recursion input/depth. The bound has a factor
`1/sqrt(lo)`: it does not assert uniform endpoint differentiability or the
Stein cancellation needed for the negative-square identity for `Q'`/`U''`.

`ParisiThirdSpatial.lean` now justifies that missing derivative without assuming
an input third derivative. Differentiate the finite spatial FTC identity in
variance using the existing common interior bound; spatial FTC identifies the
derivative of the heat velocity. The checked heat equation yields the actual
third spatial derivative of the smoothed transform.
`Section4SquaredSlopeDerivative.lean` differentiates the genuine normalized
two-step squared-slope mean, uses the equal-mass semigroup to fix the outer
normalization, and applies existing Gaussian Stein with proved domination.
The result is exactly (4.16), the negative tilted square of the spatial Hessian.
`Section4USecond.lean` propagates it through the remaining outer means. Their
potential derivatives vanish at equal masses by the existing (4.11), so no
unaccounted covariance terms remain. Thus actual `Q'` is the negative nested
Hessian-square and actual `U''∈[−1,0]`, on the open physical variance interval.
The `Q'` identity includes baseline zero/one; `U''` inherits baseline below one
from the proved `U'=Q` identification. Endpoint second derivatives are not asserted.

`ParisiMassUniform.lean` reuses Mathlib's analytic CGF/MGF derivative rules,
the local analytic zero-mass divided difference, and tilted Gaussian moment
bounds. Centering `A(x+√v z)` at `A(x)` makes the first three moments uniformly
bounded independently of the field and input depth. The weighted identities
`(m² M')'=m K''` and `(m³ M'')'=m² K'''` remove the apparent singularities at
zero mass. This proves the actual Gaussian-input analogue of Lemma 4.4, not a
separate theorem for arbitrary random variables. `Section4MassUniform.lean`
uses normalized outer means and the already proved actual mass differentiation
to give the first half of Lemma 4.5 for full `T` and inserted `Φ`, including zero
mass and closed variance/overlap endpoints, with constants depending only on `β`.
The full nested second mass derivative and Proposition 4.6 remain open.

A concrete reuse candidate for the latter is `CoupledParamDeriv.tiltSecond`:
it already differentiates a normalized mean with its covariance term. After
connecting actual scalar second-mass regularity, the invariant
`|E|+D²≤K₂+K₁²` may preserve a depth-uniform second bound for outer masses in
`[0,1]`. This route is not yet implemented or claimed as a result.

`ParisiMassDerivative.lean` differentiates one mass while its input function
is fixed, including every actual `parisiF` input. It does not assert the nested
Section 4 variation or stationarity identities. The derivative theorem assumes
nonzero mass; entropy integrability includes mass zero, and the separate scalar
semigroup covers zero mass without identifying it with the incorrect totalized
operator `Parisi.T 0`.

The scalar heat generator is checked at **positive variance**; the mass can be
zero. `Section4Variance.lean` proves the spatial second-order invariant on every
actual Parisi input, then bridges a spatial translation into RSAT's general
`GoodTriple` parameter to obtain joint continuity in variance and field. Together
with the heat equation, Mathlib's continuous-partials theorem gives joint
differentiability. This is the justified input to the moving-field chain rule,
not a new assumption of the nested variation being sought.
`Section4SplitDerivative.lean` adapts the existing local-neighborhood N-site
parameter chain rule to one coordinate. Compactness and RSAT joint continuity
give neighborhood growth bounds; the established joint derivative differentiates
the inner step at the moving outer field. Normalized scalar Stein then cancels
the `Bxx` terms and proves **(4.11)** for the actual two-step recursion, with
the correct `(m-m')/2` coefficient. Both mass-zero branches are included, and
actual `parisiF` specialization discharges all analytic input hypotheses.
Only `0<v<a` is covered by that derivative theorem. The subsequent
`Section4SplitMonotone.lean` and `Section4NestedMonotone.lean` reuse RSAT's joint
continuity and local Gaussian order preservation to obtain the closed-interval
comparison for the full actual `section4T`. Endpoint derivatives and higher
mixed identities are not inferred from this monotonicity.
`Section4NestedDerivative.lean` then reuses `CoupledParamDeriv.secondStep`
at one coordinate to differentiate the full actual outer scalar recursion.
The derivative is an explicit nested normalized mean of (4.11); its bound
`(m-m_(r-1))/2` survives every outer step without a depth factor. Compact
joint continuity and unit spatial Lipschitz bounds discharge the neighborhood
growth assumptions. This is not a proof of the higher mixed mass derivatives.

`Section4InsertedScheme.lean` was checked against (4.27)--(4.37), pp. 245--246.
The insertion is a genuine admissible scheme at one more level. Its variance
bridge is the existing Section 5 endpoint algebra at `t=1`; its correction is
half the already proved paired correction, after canceling the halved shared
masses. Near-global minimality gives (4.30). At the upper inserted mass, the
existing exact equal-mass merge produces a same-level competitor and gives
(4.31). Thus the optimality hypotheses are connected to the actual variation,
without postulating its first or second derivatives.

`ParisiMassLocal.lean` obtains field-uniform domination on positive compact mass
intervals from the existing tilted first-moment bound and Herbst estimates.
It separately proves `|Step(m,v,A)-Step(0,v,A)|≤|m|v/2` for a 1-Lipschitz
input and **every real mass**. The negative side follows by reflecting both
the input and mass, so the mass-zero derivative is genuinely two-sided.
Mathlib's primed dominated-differentiation theorem needs only a difference
bound anchored at zero; no pairwise local Lipschitz claim is substituted.
`Section4MassDerivative.lean` propagates the positive-mass derivative through
the actual outer normalized means. At zero baseline, scheme monotonicity and
nonnegativity force all outer masses to zero; the Gaussian semigroup collapses
their variance to `β² q_r-v`. This gives the actual baseline derivative on the
closed variance interval and justifies `U=2∂mT` in (4.42), including `U(0)=0`.
`Section4FirstVariation.lean` adds the known affine correction to identify
(4.46) with the baseline derivative of the actual `section4Phi`.
An independent read-only review checked the anchored theorem's hypotheses,
zero-baseline indices, semigroup variance and normalization. The positive
local bound is not uniform as its lower mass endpoint tends to zero. These
earlier modules do not claim uniform second-mass estimates or `U′`, `U″`;
the later zero-inclusive bounds and derivative identities are recorded above.

`Section4UBounds.lean` obtains the unit Lipschitz and monotonicity bounds for
actual `U` from mass difference quotients of the already checked full `T`
variance bound. The interval of increased masses is nonempty when
`m_(r−1)<1`; this is supplied by the strict-mass reduction, not silently
assumed for arbitrary schemes. The limit includes zero baseline mass and both
variance endpoints. Finite differences also give the `β²/2` overlap-Lipschitz
bound for the actual first variation, without claiming `U′` exists.

`Section4VarianceFactor.lean` defines `Q` as the nested normalized mean of the
squared inner spatial derivative. Linearity factors the existing derivative
as `(m−m_(r−1))Q/2` at every depth. Positivity and normalization give `Q∈[0,1]`,
including equal masses, without division by the gap. Mathlib's integrability
and fundamental theorem for a nonnegative derivative yield the endpoint-safe
integral identity. Integrability of `Q` alone is deduced for a strictly positive
mass gap; at baseline no continuity or integrability of `Q` is inferred from
the vanishing product. Proving those facts and passing to the baseline mass
limit requires the separate continuity proof below.

`ParisiJointMassContinuity.lean` proves continuity of the weighted exponential
moment and its normalized slope quotient jointly in mass, variance and field.
The potential itself uses the existing Herbst estimate to connect the mass-zero
expectation with the nonzero branch; no singular division is performed at zero.
`Section4VarianceFactorContinuity.lean` uses the existing compact-path growth
rules and dominated continuity of normalized Gaussian means to propagate the
actual squared-slope observable. The resulting `Q` is continuous on the entire
closed mass/variance rectangle, including mass zero and one, and is integrable
at the baseline independently of the vanishing mass gap.

`Section4UPrime.lean` uses that continuity and `0≤Q≤1` to pass the right mass
limit through the variance integral. The two actual baseline mass derivatives
give `(U(w)-U(v))/2`, while the mass-gap factor gives half the baseline `Q`
integral. Hence `U(v)=∫₀ᵛQ(m_(r−1),z)dz` and the interior FTC proves `U′=Q`.
The baseline must be below one, as in `Section4UBounds`; mass zero is included.
The actual overlap first variation then has derivative `β²(u-Q)/2`, with beta
zero handled by its constant branch. No mixed derivative interchange, endpoint
stationarity, uniform second-mass estimate, or identity for `U″` is assumed.

`Section4UEndpoints.lean` reuses Mathlib's continuous interval projection and
FTC to obtain the same formulas as derivatives within the full closed physical
intervals. A continuous extension of `Q` is used only to prove the FTC; its
integral agrees with the actual `U` on the admissible interval. It does not
silently replace `U` outside its physical domain or assert a two-sided derivative
at variance zero. The `derivWithin` identity requires a positive interval length;
the derivative predicate alone allows a singleton interval without claiming uniqueness.

`Section4EndpointOptimality.lean` proves the noninitial-interval part of
Proposition 4.8 by an actual fixed-level competitor: at the lower overlap the
inserted interval has zero variance, its mass can be raised without changing
either the scalar recursion or correction, and equal-mass compression removes
the redundant level. The baseline derivative then gives `f(q_(r−1))≥0` when
`r≥2` and `m_(r−1)<m_r`. The initial interval is deliberately excluded: its
fixed mass `m₀=0` cannot simply be raised while retaining scheme admissibility.
No initial-interval bound or equality at an interior mass is inferred here.

The optimality comparison was also rechecked: the finite-error inequality
(4.30) alone does not bound its baseline derivative, and the upper-mass
comparison (4.31) is not a proof that the baseline is an exact minimum. The
missing uniform higher-mass estimate must not be replaced by that assumption.

`RightInterpolationAlgebra.lean` reuses `pairCascadeCorrection_eq_split` at
cutoff `r+1` and supplies only the changed two-interval sum. The exact result
is `2*parisiCorrection+(m-m_r)*(β²/2)*(u²-q_r²)`. `Section4RightVariation.lean`
reflects the existing (4.11) by `v↦a-v`, with inner mass `m_r`, outer mass `m`.
Thus the derivative coefficient is `(m-m_r)/2`. The full dual scalar comparison
for `0≤m≤m_r` follows through order-preserving outer steps. The last interval
uses the actual terminal input, not an inadmissible scheme with top mass below 1.
`Section4RightDerivative.lean` now propagates the reflected split derivative
through exactly `r` unchanged outer levels with the existing one-coordinate
normalized parameter rule. Its signed range is `[(m−m_r)/2,0]`, and endpoint
continuity plus Mathlib's mean-value theorem gives the closed-interval
Lipschitz constant `(m_r−m)/2`. The last interval and zero masses are retained;
dual mass-variation stationarity is not part of this result.

The zero-lambda formulas were independently checked against pp. 246 and 253
of the Annals paper: local forward index `p=k+2-j`, total depth `k+3`, and
split `k+3-r` give independent inserted/inner levels and shared outer levels.
`section4T` is the actual scalar nested integral, not half of `V` by definition.
Its Lean argument order is mass then variance, while the paper writes `T(v,m)`.
The outer mass-zero expectation and all split-variance endpoints are retained.

For Lemma 5.9 (p. 255), a normalized tilt of mass `m ∈ [0,1]` sends
`D` to its tilted mean and `E` to its tilted mean plus `m Var(D)`.
Consequently `0 ≤ E ≤ 1-D²` is preserved exactly. This supplies the uniform
constant missing from a naive iteration of RSAT's coarse `c+m` curvature bound.
The actual Section 5 inserted/halved masses are all in `[0,1]` at the baseline
mass. The explicit choice `λ=u-V′(0)` gives (5.33) with denominator 2 and the
proved endpoint comparison transfers it to `η(0)`. This curvature argument alone
does not identify `V′(0)` with `U′`, invoke scheme optimality, or bound `η(1)`.

`Section5LambdaUPrime.lean` proves Lemma 5.8 by reusing the actual RSAT-backed
λ derivative, not by differentiating a zero-λ equality of potentials.
Independent levels at λ=0 propagate a product of the two scalar slopes.
After the inserted independent level, these are the slopes of
`B=parisiStep m v (parisiF ...)`. Shared levels on the diagonal see potential
`2B` and paired mass `m_old/2`, exactly the scalar normalized tilt of mass
`m_old` defining `Q`. The suffix length `r−1`, total depth `k+3` and remaining
variance `β²(q_r−q_(r−1))−v` match the actual Section 4 definitions.

Thus `∂λV(0,m,v)=Q(m,v)` for every `m≥0` and the entire closed variance
interval, including zero masses and coincident endpoints. At baseline mass
below one, the checked `U′=Q` proves Lemma 5.8 for ordinary interior derivatives
and for inward endpoint derivatives. A numerical `derivWithin` equality needs
a positive variance gap; the derivative predicate also covers a singleton
interval without implying uniqueness. The optimized baseline and actual
time-zero gain consequently have the explicit deficit `(Q−u)²/2`, including
baseline masses zero and one. No stationarity or time-one transport is inferred.

The Proposition 2.3 assembly follows p. 232. The bound is relative to `2ψ`,
not `2φ`: the threshold `2K(ψ−φ)+η` supplies the `η/K` deficit needed by
Proposition 2.5. Counting overlap values gives the sharper Ising factor `N+1`
(the paper uses the sufficient `2N+1`); no exponential spin-pair factor is lost.
The fixed-scheme convergence initially assumes the uniform quadratic estimate
and `s.m 1 > 0`. `RSBSchemeReduction.lean` now removes leading zero masses
by exact Gaussian semigroup identities for both scalar and N-site cascades.
The actual functional and pressure are preserved, and padding each smaller
competitor transfers fixed-level minimality. This yields the original Theorem
2.2 quantifiers from the uniform quadratic estimate for positive-first-mass
schemes. It does not by itself assert every strictness condition of (2.19),
in particular strictness at the endpoint overlaps.

`RSBMassPiSemigroup.lean` extends the same product-Gaussian convolution adapter
to every real mass. `RSBSchemeMassReduction.lean` uses it for arbitrary
equal-adjacent-mass deletion. The scalar identity is obtained by the existing
one-site tensorization, not a second reindexing proof. Correction telescoping
and competitor padding preserve the functional and fixed-level minimality.
Induction yields strictness of the entire mass sequence; no strictness of the
overlap sequence is claimed. An independent read-only review also checked
the lambda-curvature/gain modules against the actual paired mass convention.
The final strict-mass conditional bridge reduces the uniform quadratic estimate
to that smaller comparison class without assuming overlap strictness. Strict
masses do not eliminate the baseline mass zero at `r=1`.
`ParisiMassZero.lean` supplies the actual single-step zero-mass derivative via
Mathlib's analytic divided difference and CGF variance formula;
`Section4MassDerivative.lean` now handles the actual nested baseline as described
above. Higher mixed mass/variance identities remain open after the checked
first identity `U′=Q`. Closed-interval inward derivatives are now also proved,
but the remaining endpoint stationarity is not silently inferred from them.

## Historical copies and local ports

All vendored files are Apache-2.0.  Original headers are retained unchanged.

| File in this repo | Origin | Path in origin | Commit | Edits |
|---|---|---|---|---|
| `Lemmas/SpinGlass/Calculus.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Calculus.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Defs.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Defs.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/gaussian_concentration.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/gaussian_concentration.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GuerraBound.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GuerraBound.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Replicas.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Replicas.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/SKModel.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/SKModel.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `ParisiFormula/GuerraToninelli.lean` | njimaMath/research_public | `perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | 2 import lines + provenance header; proof repairs for Lean v4.32.1 (see below) |
| `ParisiFormula/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | provenance header and `Mathlib.MeasureTheory.Integral.Prod` import; compiled local port |
| `port/GuerraInterpolation.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraInterpolation.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraIBP.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraIBP.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraTrace.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraTrace.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraPipeline.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraPipeline.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `lean-toolchain`, `lake-manifest.json`, `LICENSE` | njimaMath/research_public | `RSAT/` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | initial source; manifest subsequently regenerated for this project's dependencies (see above) |

The RSAT core files (`Lemmas/SpinGlass/`) are themselves derived from or4nge19/SpinGlass;
RSAT's own NOTICE says so and is reproduced in our NOTICE.

Toolchains at the time of vendoring: RSAT and perceptronFixed used Lean v4.32.1 / v4.32.0
with matching Mathlib; or4nge19/SpinGlass used Lean v4.28.0-rc1 (hence the `port/` folder).

`ParisiFormula/ParisiOperatorGrowth.lean` is a local extension of the ported semigroup
law to linear-growth functions. The cascade files in `Targets/` and the local Stein
lemmas support the completed SK Theorem 2.1; they are not pending upstream ports.

## Post-vendoring repairs to `ParisiFormula/GuerraToninelli.lean`

The upstream file was verified against a slightly different Mathlib. These compatibility
repairs preserve the theorem statements:

* `cfgEquiv.left_inv` and `cfgJoin_cfgLeft_cfgRight` — `Fin.addCases_castAdd_natAdd` is now
  stated pointwise, and `simpa` cannot close the goal because the `simp` equation lemmas for
  `cfgLeft`/`cfgRight` are in applied form; `exact` (default transparency) does.
* `integrable_log_skZ`, the `hEnergy` continuity step — `simpa` normalised the goal into
  `Pi.add` form, which no longer matches `Continuous.add`; replaced by `simp only [skEnergy]`
  followed by `exact`.

The covariance comparison lemmas `cov_deriv_diag` and `cov_deriv_offdiag_nonpos` were
also made public for reuse.
