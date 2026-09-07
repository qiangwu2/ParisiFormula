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
outer expectation, with the exact factor `N`. This supplies the disorder term
used by the combined trace-plus-heat identity completed in Step 30 below.

`CoupledReplicaHeat.lean` reuses the exact level-addition identity and bounded
transport linearity to carry inner Hessian and heat expressions through the
unchanged outer levels. The products remain at their original split level;
only their remaining outer depth increases. Packed independent and nested
equal-mass normalized means agree by uniqueness of genuine derivatives of
bounded perturbations, reusing the checked equality of potentials. Both actual
`constrainedLevelVarianceD` generators are identified with their coordinate
sums of replica expressions divided by two, through all remaining outer levels.
The algebraic identities include zero variances; they do not assert a variance
derivative there. Step 30 below completes coordinate contraction into overlaps,
outer averaging of the heat terms and the physical coefficient sum with the
disorder trace. The desired interpolation inequality is not inferred merely
from the square completion; the actual derivative is first identified.

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
Step 30 completes the nested second mass derivative using
`CoupledParamDeriv.tiltSecond`, actual scalar second-mass regularity and the
now-checked invariant `|E|+D²≤K₂+K₁²` for outer masses in `[0,1]`.
Proposition 4.6 remains open.

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

## Step 30: actual covariance interpolation and nested mass estimates

The field contractions reuse the local spin-contraction identities, which in
turn reuse RSAT's overlap sums. Actual split-weight measurability and normalized
moments justify the disorder average. `Section5ReplicaDerivative.lean` reuses
the checked trace-plus-heat derivative rather than reproving Gaussian
differentiation. The zero-variance alternative supplies zero actual velocity.

`CoupledCovarianceTelescope.lean` uses Mathlib's `sum_Ico_Ico_comm'`,
`sum_range_by_parts`, `sum_Ico_reflect` and `sum_range_reflect` to combine the
backward heat and disorder expressions. The physical increment is exactly the
difference of adjacent trial-field covariance kernels. The actual averaged
split at backward index `κ-p` is the paper's measure at forward index `p+1`.
The endpoint masses are explicit; positivity and normalization are used only
when applying the existing square-completion inequality. The final Section 5
bounds use the allowed inserted-mass intervals and the existing mean-value
and endpoint-continuity results. This proves the SK positive-overlap instances
used in (5.9) and its dual, not a new proof of the general signed Theorem 3.1.

The nested mass argument reuses the existing scalar cumulant bounds, mass
reflection, normalized-tilt linearity/integrability, and
`CoupledParamDeriv.tiltSecond`. Field dilation and reflection extend local
scalar domination to an open neighborhood of `[0,1]`. The invariant
`|E|+D²≤K₂+K₁²` propagates without depth loss because the fixed outer masses
lie in `[0,1]`. This proves genuine second derivatives of the actual `T` and
inserted `Φ`, including both mass and physical variance endpoints. Mathlib's
mean-value bound, applied twice, gives a quadratic Taylor error with constant
`K₂(β²)+K₁(β²)²` (not optimized by a factor of two). The baseline uses the
existing `U/2` and first-variation identifications.

Independent reviews checked the normalization, index reversal, zero cases,
actual derivative identifications and uniform constants. Quantitative
optimality, the initial/remaining overlap and sign cases, Theorem 2.4 and
unconditional Theorem 2.2 remain separate obligations. No dependency pins or
upstream sources were changed.

## Step 31: quantitative optimality, stationarity and pressure gains

`Section4QuantitativeOptimality.lean` follows Proposition 4.6, p. 249 of
Talagrand (2006). It reuses the actual inserted competitors and the checked
full mass Taylor bound. The explicit constant is `2√(C(β)+1)`; strict adjacent
masses are assumed as in (2.19), but the baseline may be zero. No optimizer
or stationarity hypothesis has been replaced by a sign condition on `f`.

`Section4Stationarity.lean` reuses the existing variance integral identity and
Mathlib's inward FTC and tangent-cone Fermat rule. At zero split variance,
the actual normalized observable is independent of the inserted mass.
`Section4StationarityInterior.lean` lowers a nonterminal mass, then reuses
the original insertion and equal-mass compression to obtain the opposite
fixed-level competitor. The actual endpoint observable is identified through
all remaining outer levels, including zero masses. This proves Proposition
4.7 and the upper derivative in Proposition 4.8 for `1≤r≤local k`, with
strict adjacent masses and the stated inward overlap directions. Boundary
overlaps zero and one use `0≤Q≤1`; numerical inward derivatives require
a nondegenerate interval. The final compulsory mass and coincident interior
overlaps remain open. `β≠0` is needed for stationarity; the target assumes `β>0`.

`Section4Concavity.lean` uses Mathlib's
`concaveOn_of_hasDerivWithinAt2_nonpos` and supporting-line inequalities,
with the already proved actual `U′=Q`, `Q′=-R` and endpoint continuity.
Thus (5.34) uses a proved inward slope at the endpoints, not Lean's default
value for an unproved derivative. Zero variance gaps are included.

`Section5PressureGain.lean` and `Section5RightPressureGain.lean` reuse the
actual second-interpolation endpoint bounds and lambda curvature estimate.
The correction cancels to `2ψ(t)`, not `2φ(t)`. The full mass Taylor estimate
allows both directions at a positive baseline; the explicit decrease
`min(m_(r-1)/2, D/(4(C(β)+1)))` stays admissible and gives deficit at least
`Dδ/2`. Together with Proposition 4.6 and (5.34), this proves the
positive-baseline far-left strict bound in Proposition 5.5's argument.
The deficit is retained before system size and disorder are quantified.
`Section5FarLeft.lean` uses the SK quadratic convexity defect to express
the hypothesis uniformly over `t≤t₀` and `L₁(q_r-u)≥1-t₀`, with beta-only
`L₃=4L`. The factor four turns the non-strict smallness assumption into a
strict gain. This does not assert the infimum defining (5.4) has the same
formula outside its physical, nonempty range.
The initial mass-zero case, remaining dual/signed/far-overlap constructions,
Lemma 4.9/Proposition 4.10 and the uniform Theorem 2.4 remain separate obligations.
No dependency pins or upstream sources changed.

## Step 32: stationarity reduction, endpoint regularity and conditional curvature

The paper comparison is Talagrand (2006), pp. 249--251, Propositions 4.7--4.10
and Lemma 4.9, together with the scheme reduction near (2.19).
`Section4StationarityTerminal.lean` reuses the existing insertion and equal-mass
compression. Its base scheme moves the last overlap to one, never lowers the
compulsory terminal mass, and merges an inserted mass-one level. The actual
endpoint observable is identified through all outer means. This completes the
terminal stationarity competitor, including local depth zero, under the same
inward-direction conditions as the earlier nonterminal proof.

`RSBSchemeOverlapReduction.lean` reuses `raiseMass`, the zero-variance step
identity, `mergeEqualMass`, and the existing competitor-padding proof of
minimality preservation. It proves invariance for the actual arbitrary N-site
cascade, not just the scalar functional. Iteration removes coincident interior
overlaps without destroying strict masses. Combined with mass compression, it
preserves the functional, `ψ`, `φ_N` on `[0,1]`, and fixed-level minimality.
`Section4StationarityReduction.lean` extracts the inward directions from the
reduced overlap list. Thus stationarity needs no new strictness hypothesis on
the original Theorem 2.2 scheme. The conditional convergence transfer remains
explicitly conditional on the uniform two-replica quadratic estimate.

`Section4HessianRegularity.lean` reuses local
`continuousOn_pairedSecondMean_paths`, `section4Cascade_baseline`, RSAT-derived
joint C2 continuity and the existing interior negative-square identity.
At baseline, outer potentials are independent of split variance by the actual
semigroup identity. Mathlib's FTC and the existing interval-projection argument
then give an integral representation and inward `Q′=-R` at both endpoints.
The factor is the actual `section4THessianSquare`; continuity is not substituted
for Lipschitz regularity. Numerical derivatives on singleton intervals are not
asserted.

`Section4Curvature.lean` identifies the actual overlap second derivative
`β²(1-β²R)/2` and formalizes the short/long-gap argument. The initial
lower-endpoint mass variation is not admissible because `m₀=0` is compulsory.
`Section4InitialCurvature.lean` instead uses stationarity, `Q≥0`, and the actual
FTC to obtain `∫_0^(β²q₁) R ≤ q₁`. With an explicit Lipschitz bound `L` on
the actual `R`, this gives `-f″(q₁)≤Lβ⁶q₁/4`. No initial sign `f(0)≥0` is
assumed or claimed.

`Section4CubicTaylor.lean` reuses Mathlib's
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` twice to obtain the cubic
remainder, with constant `β⁶L/2`, from that same actual-`R` Lipschitz premise.
`Section4CurvatureRegularity.lean` combines the initial short-gap bound,
the initial long-gap Taylor test and the noninitial two-gap argument. Its
sixth-root curvature estimate covers all physical levels with positive left
overlap gap, including zero tolerance, under genuine fixed-level minimality
and near-global optimality. Independent review checked endpoint directions,
beta scaling, the zero-tolerance branch and the unchanged target quantifiers.

**Reuse boundary:** the local `ParisiThirdSpatial.abs_stepD3_le` bound is
singular like `1/√v` as split variance tends to zero. It cannot supply the
required full-interval, depth-uniform Lipschitz constant. Terminal smoothness
in the pinned dependency does not by itself give that constant through the
nested recursion either. No such constant is constructed in Step 32:
Lemma 4.9 and unconditional Proposition 4.10 remain open. The local quadratic
and remaining overlap cases of Section 5, uniform Theorem 2.4 and unconditional
Theorem 2.2 are still separate obligations. No dependency pins, original target
statements or upstream sources changed.

## Step 33: uniform derivatives and the local-left/initial estimates

The source comparison is Talagrand (2006), Lemma 4.9 and Proposition 4.10
(pp. 250--251), and the proofs of Propositions 5.1 and 5.3 (pp. 255--256).
This checkpoint follows the paper's derivative/optimality/Jensen argument;
it does not replace it with a different proof of the Parisi formula.

**Reuse:** `ParisiThirdUniform.lean` applies the existing finite-coordinate
dominated differentiation theorem to normalized scalar observables.
`ParisiFourthUniform.lean` reuses that rule, the existing `HasParisiC2`
invariant and normalized-mean bounds. The new exponential derivative
polynomials obey exact averaging identities at fixed mass. Their mass-change
bounds telescope along the existing monotone masses, yielding genuine
depth-independent C3/C4 bounds 6 and 43, including zero mass/variance.
These are new bridges for actual finite Parisi inputs, not copied upstream
smoothness assertions. The coarser extra-step bounds 14 and 143 are used only
once; iterating those coarse bounds would not prove depth independence.

`ParisiHessianVariance.lean` reuses local Gaussian domination and joint
continuity. `ParisiHessianVarianceBound.lean` applies the existing Gaussian
variance heat-generator theorem with its factor `1/2`, giving the actual
Hessian variance bound 83. `ParisiHessianSquareFlow.lean` reuses
`integral_gaussian_mul_tilted_observable` to eliminate the inverse square-root
outer variance after actual differentiation under the integral. The resulting
constant is `2*83 + 14² + 143 + 2*14 + 2 = 535`. Measurability and local
domination of the actual derivative integrand are proved, including mass zero.

`Section4HessianDerivative.lean` reuses `hasDerivAt_pairedSecondMean` and the
proved zero baseline outer velocity. `Section4HessianLipschitz.lean` uses
positive normalized-mean contraction and Mathlib's scalar mean-value theorem;
existing endpoint continuity extends the interior bound to the full closed
interval without differentiating outside the physical domain. The actual
integration in `Section4HessianUniform.lean` supplies all regularity premises.
`Section4ThirdVariation.lean` verifies the positive chain factor `β⁶/2` and
handles β=0 separately. `Section4CurvatureUniform.lean` reuses Step 32's
deterministic argument; Proposition 4.10 no longer assumes Lipschitz regularity.

`Section4InitialHessian.lean` reuses the existing weighted Cauchy--Schwarz
inequality at zero mass and `parisiStep_add` to prove the actual `R(v)≤R(0)`.
`Section5LocalLeft.lean` and `Section5InitialLeft.lean` combine the actual
slope derivative with the already checked pressure gain. `Section5LeftUniform.lean`
discharges regularity and supplies a beta-only constant for Propositions 5.1
and 5.3. All free-energy bounds retain the baseline `2ψ`, not `2φ`.

**Remaining boundary:** the genuine third derivative is asserted on the open
physical overlap interval; closed-interval Taylor estimates use inward
derivatives and continuity. Dual and remaining far-overlap/sign estimates and
uniform Theorem 2.4 assembly are not implied by the completed left/initial
cases. Theorem 2.2 remains open. No dependency pins, original target statements,
upstream sources or original placeholders changed.

## Step 34: exact reflection for the local-right estimate

Talagrand describes the dual split at the end of Section 4 (p. 250) and states
Proposition 5.2 on p. 251; on p. 257 he refers to the analogous left proof.
The formalization reuses that left analysis via exact identities rather than
duplicating a second Gaussian calculus development.

`Section5RightLambdaFactor.lean` proves agreement of the actual paired mass
arrays, reversed variance arrays and sharing cutoff. A finite-cascade
congruence lemma permits parameter reindexing without changing the underlying
lambda family. The existing `hasDerivAt_section5V_zero_Q` then identifies the
genuine right zero-lambda derivative. Half-masses at shared levels are retained;
this is not a comparison of two different baseline measures.

`Section4RightFactor.lean` reuses the proved `Q′=-R` within-set chain rule
and the uniform 535 bound. Reflection changes the derivative sign to positive
without changing its Lipschitz constant. `Section4NeighborFactors.lean` uses
the actual `parisiFDeriv`/`parisiFSecond` recursions, zero-variance evaluation
and baseline outer-potential identities to match neighboring endpoint factors.

`Section5LocalRight.lean` reuses Mathlib's mean-value estimate and the checked
actual right interpolation/lambda gain. `Section5RightUniform.lean` supplies
stationarity and curvature from the original scheme via the endpoint identities.
The resulting quadratic deficit has the same beta-only constant as the left
estimate and remains relative to `2ψ`, not `2φ`.

**Scope at the Step 34 checkpoint:** the uniform result requires `1 ≤ r ≤ k` and a positive
left overlap gap. The scheme's terminal overlap is `q(k+2)=1`; one cannot
discard the right interval at `r=k+1`. Also the existing curvature theorem
cannot be applied when the first overlap equals zero. These extensions remain
open, so unrestricted Proposition 5.2 and Theorem 2.4 are not claimed complete.
For terminal reuse, a redundant mass-one/zero-variance padding is a candidate,
but equality of the whole shifted `Q/R` and paired recursions is not proved.
The existing `section4TVarianceQ_terminalBase_endpoint` only matches one
endpoint of a modified scheme and is insufficient for that purpose.
No original targets, dependency pins or upstream sources were changed.

## Step 35: terminal padding reuses the checked right-interval proof

`RSBSchemeTerminalPadding.lean` appends mass one and repeats terminal overlap
one. The new innermost scalar step has zero variance. The existing
`parisiStep_zero_var` gives the exact recursion shift; uniqueness of genuine
derivatives gives the first- and second-derivative shifts. All original physical
masses and overlaps are preserved. No minimization statement about the padded
scheme is introduced.

`Section4TerminalFactors.lean` transports the entire split scalar recursion and
normalized squared-slope/squared-Hessian factors. The identities include the
auxiliary left index `k+2`, which was outside the earlier calculus theorem's
range. Applying the existing nonterminal calculus to the padded scheme gives
the original terminal right factor's inward derivative, continuity, universal
535 Lipschitz bound and neighboring endpoint identities.

`Section5TerminalLambda.lean` deletes one zero-variance independent step in the
actual paired recursion. This lemma allows arbitrary masses, including zero.
Reusing `splitScalarCascade_congr_at` proves equality of the entire right lambda
family for arbitrary inserted mass and split variance. Thus the genuine
zero-lambda derivative, not just the value at zero, is transported exactly.

The existing `Section5LocalRight.lean` and `Section5RightUniform.lean` proofs
now accept `r ≤ k+1` in place of `r ≤ k`. The mean-value and pressure-gain
arguments are reused unchanged. Stationarity, curvature, near-optimality,
constrained free energy and `2ψ` all refer to the original scheme. This closes
the terminal interval with a positive left gap, including a nontrivial
`[q_(k+1),1]`; it does not close unrestricted Proposition 5.2.

**Remaining reuse mismatch:** at `q_1=0`, the admissible same-level right
variation has inner mass `m_1` and outer mass zero. The existing equal-mass
baseline derivative `Q′=-R` is not its derivative. The relevant comparator is
already available from `section4Phi_stationarityBase_min` or, when `k=0`,
`section4Phi_terminalBase_min`. What remains is the endpoint derivative of its
squared-gradient expectation and the resulting one-sided curvature inequality.
`Section4ZeroOverlap.lean` reuses zero-variance evaluation and all-level
stationarity to prove that the initial `Q/R` factors are scalar derivative
squares and that the first derivative vanishes. These are checked reductions,
not a proof of the still-missing curvature inequality.
No new Gaussian framework or different proof route is justified by this gap.

**Candidate recorded at Step 35 (completed in Step 36 below):** write
`S(v,x) = stepD1 A A' m v x`, with positive total variance `a` and
`S(a,h)=0`. For fixed Gaussian coordinate `z`, apply the existing
`hasDerivAt_stepD1_variance_curve` to `S(a-θ²,h+θz)` at `θ=0`.
The variance velocity is zero and the derivative is the scalar Hessian times
`z`. `HasDerivAt.tendsto_slope_zero_right` then supplies the difference-quotient
limit. The existing `abs_stepD1Variance_le_on_Icc` on `[a/2,a]` and the scalar
C2 spatial bound suggest domination by a constant times `(1+|z|)²` after
squaring; `memLp_id_gaussianReal 2` supplies integrability. Dominated convergence
with `θ=√u`, followed by `hasDerivWithinAt_iff_tendsto_slope`, would establish
the missing inward derivative of the squared-gradient expectation. A
one-sided second-order minimum argument would then give the curvature
inequality. At the Step 35 checkpoint, neither the limiting argument nor the
resulting curvature inequality was checked. Step 36 completes this route.

## Step 36: zero-first-overlap curvature and the complete local-right case

Talagrand's dual construction is described on p. 250 and Proposition 5.2 on
p. 251 of the [2006 Annals paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n1-p04.pdf).
The local scheme reduction retains possible boundary overlaps zero and one.
The new boundary proof treats these explicitly while preserving the original
convergence quantifiers and the exact-covariance SK normalization.

`ParisiZeroOverlapDerivative.lean` reuses
`hasDerivAt_stepD1_variance_curve` and
`HasDerivAt.tendsto_slope_zero_right` on the amplitude path
`S(a-θ²,h+θz)`. Existing positive-variance slope bounds and the C2 spatial
bound give an integrable quadratic Gaussian envelope. Mathlib's
`tendsto_integral_filter_of_dominated_convergence`,
`memLp_id_gaussianReal 2`, and the standard Gaussian second moment identify
the actual inward variance derivative with the squared Hessian. There is
no assumed endpoint heat formula or unproved interchange of limit and integral.

`Section4ZeroOverlapVariation.lean` reuses the actual
`section4Phi_stationarityBase_min` and `section4Phi_terminalBase_min`
competitors and `hasDerivWithinAt_section4Phi_overlap`. Zero-variance evaluation,
zero-mass weights and scalar prefix identities identify the derivative exactly
as `β²*m_1/2 * (u-Q0(β²*u))`. The existence theorem requires only zero first
overlap and the original fixed-level minimality; positive variance, nonzero
beta and a positive mass gap are used later, where necessary.

`OneSidedCurvature.lean` reuses Mathlib's derivative-as-slope limit and
`exists_hasDerivAt_eq_slope`. It requires a genuine one-sided minimum,
genuine first derivatives on a nondegenerate interval, a zero endpoint first
derivative, and only the second derivative at that endpoint. No continuity
of a second derivative throughout the interval is assumed.

`Section4ZeroOverlapCurvature.lean` assembles these results with the checked
scalar-square identities and original stationarity. The coefficient
`β²*m_1/2` is positive; composing `Q0` with `β²*u` contributes the second
factor `β²`. The resulting bound is exactly `β² R_1(0) ≤ 1`, with no epsilon
error. `Section5RightBoundary.lean` reuses the proved local slope/pressure
gain and the existing common constant. The previously private constant bounds
are exposed, not reproved. Its combined theorem proves Proposition 5.2 for
the reduced schemes used on the critical path, including both boundary cases.

**Next reuse boundary:** baseline right/left reflection identifies the lambda
family at the baseline mass, not the entire variable-mass families. A proof
of the far-right strict gain must identify the actual right mass derivative
and its optimality deficit; it cannot simply assume those variable-mass
families agree. The signed and outside-neighbor constructions and subsequent
compactness remain open. No dependency pins or upstream sources changed.

## Step 37: the actual right mass variation and far-right improvement

`Section4RightInsertedScheme.lean` constructs a genuine right insertion in
the original scheme and identifies its scalar recursion and correction.
The existing equal-mass merge gives a same-level competitor at the lower
mass endpoint. Thus only original fixed-level minimality is used, including
the first and terminal intervals; no minimality of a padded scheme is added.

`Section4RightMassDerivative.lean` applies the existing scalar mass calculus
to the actual fixed inner transform, then uses `CoupledParamDeriv.secondStep`
through the unchanged outer levels. `Section4RightMassSecond.lean` reuses
the scalar local-uniform bounds and `pairedSecondCovariance_mass_invariant`,
giving the same depth-uniform Taylor constant as for the left insertion.
`quadratic_remainder_of_second_bound` and
`firstVariation_sq_le_of_quadratic_comparisons` are exposed for reuse, with
their statements and proofs unchanged. The dual optimality proof applies the
latter to the negative of the actual right first variation; it does not
duplicate the mean-value or quadratic optimization arguments.

`Section5RightMassGain.lean` uses the existing actual right interpolation
endpoint bound and zero-lambda scalar identity. Its admissible inserted
scalar mass extends to twice the original mass, because the corresponding
paired mass is halved. A negative corrected derivative therefore gives a
strict gain by increasing the mass, even when the original mass is one.
`Section5RightScalarGain.lean` combines this with the already identified
right lambda square gain. Its deficit is chosen before system size and
disorder, not extracted separately from a finite-size strict inequality.

These two directions must remain distinct: scalar optimality decreases the
inserted mass, whereas the coupled-pressure improvement increases it.
Baseline lambda reflection does not identify the variable-mass scalar
families.

`Section4RightVarianceFactor.lean` removes the prefactor from the actual
right variance derivative without dividing by the mass gap. The existing
`guerraGrowth_one` and `pairedTiltMean_mem_Icc` helpers are exposed unchanged
to prove the normalized range. `Section4RightVarianceBaseline.lean` identifies
the normalized baseline recursion itself by scalar mass-array equality and
the existing variance reflection. This algebra includes the terminal interval
directly. Fixed-variance mass continuity then allows bounded dominated
convergence in `Section4RightUPrime.lean`. The limit is taken from below, so
positive baseline mass suffices even at mass one. A clamped continuous
extension of the factor supplies the inward endpoint derivative by FTC.

`Section4RightConvexity.lean` uses the existing all-level `Q_+' = R_+` and
nonnegative Hessian-square factor, with Mathlib's derivative criterion for
convexity. `Section5FarRight.lean` combines its supporting line with actual
dual optimality and the mass-or-lambda gain. The existing far-left smallness
arithmetic is exposed unchanged, and the same beta-only constant suffices.
The result is Proposition 5.6 in the exact-covariance SK setting, with a
positive scalar deficit chosen before system size and disorder. Uniformity
over time/overlap and the other signed/outside-neighbor cases remain separate.
The statement and the dual proof route were checked against
[Talagrand, pp. 251 and 257](https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n1-p04.pdf#page=31).
No dependency revision or upstream source is changed.

## Step 38: signed initial Gaussian estimates and the retained shared field

This records the ingredients available at Step 38. The pressure-transport
obligation described here is closed in Step 39 below.

The signed scalar factor follows the opposite-field Gaussian product in
[Talagrand's proof of Proposition 5.4, p. 257](https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n1-p04.pdf#page=37).
`Section4SignedGaussianFactor` uses the existing actual `HasParisiC2` scalar
calculus, variance differentiation, and Gaussian Stein. The pinned RSAT
small-negative-overlap calculations are specialized to terminal `tanh` and
do not directly supply this arbitrary-depth scalar statement.
`Section4SignedHessianBound` reuses Mathlib's Gaussian reflection law and
the local zero-mass Jensen/semigroup estimate. The two bounded-Gaussian
helpers in `Section4InitialHessian` are exposed unchanged for this reuse.

`Section5SignedInitialLambda` applies the existing independent-prefix
identities and `UnitLambdaCurvature.finiteStep` to opposite signed Gaussian
coefficients. The existing `section5_scalar_prefix` is exposed unchanged;
no nonlinear cascade calculus or curvature induction is duplicated.

The physical construction needs an additional distinction. Under the
original local `constrainedPhi` definition, the initial frozen field has
positive shared variance `(1−t)β²q₁`. The negative interpolating field must
be added separately, as in (2.23), (3.18)--(3.20), and (5.7), with the external
field unchanged. `Section5SignedInitialInterpolation` reuses arbitrary linear
Gaussian steps, the positive construction's exact reindexing identity at
time one, and its independent-prefix variance arrays. It proves exact
endpoints and the combined kernel algebra. At time zero the combined cross
covariance is `(1−t)β²q₁+tβ²u`; its sign need not be negative. The pure signed
scalar display alone is therefore not an endpoint bridge for this local
construction. The full signed pressure derivative remains a separate
obligation, not an assumed identity or a claim that Proposition 5.4 is
finished. No paper-error claim is made.

`Section5RetainedSignedInitialLambda` reuses the same finite-step curvature
invariant twice, keeping both outer Gaussian means. `Section5RetainedSignedSlope`
avoids a new covariance-law equivalence: condition on the frozen positive
field, use the generic signed factor bound at the shifted field, and apply
bounded Gaussian Fubini and the already checked scalar semigroup. The
resulting bound is for the actual double-Gaussian lambda derivative.
`Section5SignedInitialEndpoint` reuses the terminal lambda comparison,
growth-controlled Gaussian monotonicity, and finite-site tensorization to
bound the original zero-time field endpoint. Combined with the retained
slope estimate, it supplies a quantitative zero-time deficit under the
actual initial curvature condition. Full signed pressure transport is still
open; a pure signed display is never substituted for the retained field.

## Step 39: exact reflection and conditioning close Proposition 5.4

The retained-field transport left open in Step 38 is now proved for the actual
SK constrained free energy. `SKSpinFlip` derives almost-sure Hamiltonian
evenness from the existing exact spectral covariance identity and Mathlib's
zero-variance Gaussian law; no symmetry axiom or positive spectral-variance
assumption is added. `Section5SignedCascadeFlip` uses Mathlib's Gaussian
reflection law, finite-product measure preservation, and the existing
independent cascade. It reflects the second replica together with its field.

`Section5ConditionedInitialInterpolation` reuses the actual arbitrary-field
trace/heat derivative, normalized replica covariance estimate, and
closed-interval endpoint transport. `Section5SignedInitialConditioning`
uses the existing `CoupledGrowth` Gaussian integrability bounds, fixed-face
joint continuity, the disorder Lipschitz estimate, and Mathlib Fubini to
average over the retained positive shared field. The reflected fields are
explicitly `x = h + √((1−t)β²q₁) z` and `−x`; after averaging and undoing
reflection the endpoint is the original constrained free energy at field `h`.
There is no wholesale replacement of the frozen positive field by a negative
one, nor a claim of a general signed Theorem 3.1.

`Section5InitialSigned` combines this transport with the actual retained-field
gain from Step 38 and the original minimizing-scheme curvature estimate.
The curvature extraction is moved unchanged into
`section5Initial_curvature_data` for reuse by Propositions 5.3 and 5.4.
The final quantitative and strict conclusions retain the reduced-scheme
hypotheses and the same explicit beta-only smallness constant.
This is an exact SK reformulation of the signed interpolation in
Talagrand's Proposition 5.4, not an alternative route to the Parisi formula.
No dependency pins or upstream sources are changed.

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
