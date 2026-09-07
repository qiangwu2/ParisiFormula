/-
# Regression checks for the SK Guerra identity and the Theorem 2.2 supporting results

These guards are part of `lake build Targets`. They reject any reintroduced
`sorryAx` or additional axiom in Theorem 2.1, its upper-bound consequences,
Lemma 2.7, the replica-measure decomposition, Lemma 2.6, Proposition 2.5 on
interior times, and the deduction of Theorem 2.2 from an explicit overlap-concentration hypothesis.
The latter guards certify the implication, not its unproved concentration input.
The Lemma 2.6 guards include Gaussian concentration and its change of law to
the abstract disorder, not just a conditional or standard-coordinate estimate.
The Section 5 guards cover both endpoints, the actual covariance derivative
inequality and endpoint transport for the positive-overlap left/right
constructions, including (5.9). The general signed version of Theorem 3.1
and the uniform improvement of Theorem 2.4 are not certified.
The terminal Hessian and covariance-algebra guards alone do not identify the
algebraic expression with the derivative of the full nested pressure; the new
actual averaged covariance identity makes that connection.
The newer guards cover full-depth disorder and separate-field mixed derivatives,
Gaussian Stein, scalar mass/variance calculus including (4.11), the zero-lambda
baseline, Lemma 5.9, and the optimized time-zero endpoint. Exact equal-mass compression
supplies the original convergence quantifiers from a uniform Theorem 2.4 bound for
strict masses; the guards do not certify that bound.
Further guards cover analytic scalar mass-zero differentiation, closed-interval
scalar comparison and Lipschitz control, the actual full T variance derivative,
inserted-scheme optimality inputs (4.30)--(4.31), one-level coupled heat generators,
and right-interval endpoints/baseline/gain. These earlier guards alone do not
assert the full nested interpolation derivative or the uniform quadratic bound.
Earlier guards add averaged disorder and individual variance derivatives,
constant zero-variance coordinates, the actual nested baseline mass derivative
and first variation (4.46), and the dual correction/scalar comparison. They do
not themselves identify replica weights or prove the identities for U' and U''.
Further guards certify full joint differentiation of the actual
moving cascade, its normalized successor derivative and both physical integrands
at fixed disorder, along with Gaussian-averaged endpoint continuity. Current
guards also certify simultaneous differentiation through the outer Gaussian
average, the actual finite-parameter decomposition and explicit trace-plus-heat
formulas for both physical pressures. Current guards also certify the actual
normalized Gibbs and split-level replica weights and their first-derivative
moments/contractions. New guards identify the actual full disorder/spatial Hessian
with the replica telescope, and the actual SK trace with its outer disorder
expectation under the normalized averaged split law. The original-level
independent/shared heat generators now have their actual replica
expressions through all outer levels. The full combined trace-plus-heat
covariance identity, its inequality and endpoint transport are now checked
for the actual positive-overlap Section 5 paths. Section 4 guards include
monotonicity of U, Lipschitz bounds for U and f, the normalized squared-slope
factor and its closed-interval integral identity, and full right variance calculus.
They now include actual joint mass/variance continuity, baseline integrability
of Q, U'=Q and the overlap derivative of the actual first variation. The new
guards include inward endpoint derivatives, noninitial lower-endpoint optimality,
actual slope variance/joint calculus with uniform interior domination, and the
actual Lemma 5.8 identity and identified Q gain. New guards prove (4.16), the
full actual Q' and U'' negative-square identity, and U'' in [-1,0] on interior
variance. They also certify zero-inclusive uniform first/second scalar mass
bounds and the first mass bound for full T and Phi. New guards certify the
full nested second mass bound and uniform quadratic Taylor expansion,
including baseline mass zero and all physical variance endpoints. Further guards
certify Proposition 4.6, nonterminal stationarity with explicit endpoint-direction
hypotheses, actual closed-interval concavity, both transported lambda gains and
the positive-baseline far-left strict improvement. The mass deficit is
explicit and independent of system size. New guards complete terminal
stationarity and exact interior-overlap reduction, preserving the actual
functional, interpolation and fixed-level minimality. Thus stationarity holds
at every level of an equivalent reduced minimizer. They also certify actual
Hessian-square continuity and inward Q'=-R at the variance endpoints, genuine
first/second derivatives of f, and cubic Taylor/curvature estimates conditional
on Lipschitz regularity of the actual R. The initial interval uses an integral
bound, not an assumed sign for f(0). New uniform C3/C4 and Gaussian-flow
guards now supply the actual universal R Lipschitz constant 535. Thus cubic
Taylor and Proposition 4.10 no longer assume regularity. The genuine interior
third derivative, beta zero, and endpoint-safe Taylor control are checked
separately. Further guards certify Propositions 5.1 and 5.3 for the actual
constrained free energy relative to 2 psi, using an explicit beta-only constant.
The initial interval uses Jensen. Further guards identify the actual right
baseline lambda family by reflection, match neighboring Q/R endpoints and
prove the local-right quadratic estimate for every positive-left-gap level,
including the terminal interval through exact redundant padding of the scalar,
paired and factor recursions. Further guards prove the actual zero-first-overlap
right comparator, its squared-slope endpoint derivative, and one-sided curvature.
The local-right estimate now covers every level of a reduced scheme, including
both boundary cases. Other overlap/sign regimes and the uniform Theorem 2.4
assembly remain open.
Further guards certify actual right insertion, genuine first/second mass
derivatives, depth-uniform Taylor control, and dual quantitative optimality.
The normalized right factor is mass-continuous and identified at baseline;
a mass limit proves the actual U'=Q with inward endpoints, and convexity
gives the dual supporting line. The actual mass-or-lambda gain now proves
Proposition 5.6, including terminal mass one, with a deficit chosen before
system size and disorder. Compactness over time/overlap is not certified.
Signed guards certify genuine Gaussian slope differentiation, endpoint-safe
Hessian and slope bounds, and scalar lambda gains, including the original
frozen positive shared field. Both exact signed interpolation endpoints and
the zero-time scalar comparison are checked. Exact SK spin reflection,
conditioning on the retained frozen field, and the arbitrary-field covariance
inequality now supply the actual signed endpoint transport. Proposition 5.4
is certified under the original minimizing assumptions for reduced schemes,
with an explicit quadratic deficit in the negative initial overlap. This does
not assert a general signed version of Theorem 3.1.
The full Parisi formula is deliberately not listed: Theorem 2.2 is still open.
-/
import Targets.ReplicaMeasure
import Targets.CoupledReplicaHessian
import Targets.CoupledReplicaHeat
import Targets.CoupledReplicaAverage
import Targets.CoupledReplicaTrace
import Targets.ParisiMassUniform
import Targets.Section4MassUniform
import Targets.ParisiThirdSpatial
import Targets.Section4SquaredSlopeDerivative
import Targets.Section4USecond
import Targets.CoupledReplicaWeights
import Targets.ParisiSlopeVariance
import Targets.Section4EndpointOptimality
import Targets.Section4UEndpoints
import Targets.Section5LambdaUPrime
import Targets.TalagrandProposition25
import Targets.CoupledLambdaPressure
import Targets.CoupledFiniteStep
import Targets.TalagrandSecondInterpolation
import Targets.SecondInterpolationAlgebra
import Targets.CoupledCascadeDeriv
import Targets.ParisiMassDerivative
import Targets.ParisiStepSemigroup
import Targets.TalagrandSection5Zero
import Targets.TalagrandOverlapTail
import Targets.CoupledCascadeSecond
import Targets.CoupledCascadeField
import Targets.TalagrandLambdaGain
import Targets.ParisiVarianceDerivative
import Targets.RSBSchemeReduction
import Targets.RSBSchemeMassReduction
import Targets.Section4Variance
import Targets.Section4SplitDerivative
import Targets.ParisiMassZero
import Targets.Section4InsertedScheme
import Targets.Section4NestedDerivative
import Targets.CoupledCascadeVariance
import Targets.TalagrandRightZero
import Targets.CoupledDisorderInterpolation
import Targets.CoupledVariancePressure
import Targets.Section5VarianceFaces
import Targets.RightInterpolationAlgebra
import Targets.Section4RightVariation
import Targets.Section4FirstVariation
import Targets.Section5InterpolationContinuity
import Targets.Section4UBounds
import Targets.Section4RightDerivative
import Targets.Section4VarianceFactor
import Targets.ConstrainedJointTerminal
import Targets.Section5JointInterpolation
import Targets.Section5PressureDerivative
import Targets.Section4UPrime
import Targets.Section5InterpolationBound
import Targets.Section4MassSecond
import Targets.Section4MassTaylor
import Targets.Section4QuantitativeOptimality
import Targets.Section4Concavity
import Targets.Section4Stationarity
import Targets.Section4StationarityInterior
import Targets.Section5PressureGain
import Targets.Section5RightPressureGain
import Targets.Section5FarLeft
import Targets.RSBSchemeOverlapReduction
import Targets.Section4StationarityReduction
import Targets.Section4StationarityTerminal
import Targets.Section4HessianRegularity
import Targets.Section4Curvature
import Targets.Section4CubicTaylor
import Targets.Section4InitialCurvature
import Targets.Section4CurvatureRegularity
import Targets.ParisiThirdUniform
import Targets.ParisiFourthUniform
import Targets.ParisiHessianVariance
import Targets.ParisiHessianVarianceBound
import Targets.ParisiHessianSquareFlow
import Targets.Section4HessianLipschitz
import Targets.Section4HessianDerivative
import Targets.Section4ThirdVariation
import Targets.Section4InitialHessian
import Targets.Section4HessianUniform
import Targets.Section4CurvatureUniform
import Targets.Section5LocalLeft
import Targets.Section5InitialLeft
import Targets.Section5LeftUniform
import Targets.Section4RightFactor
import Targets.Section4NeighborFactors
import Targets.Section5RightLambdaFactor
import Targets.Section5LocalRight
import Targets.Section5RightUniform
import Targets.Section4ZeroOverlap
import Targets.Section5RightBoundary
import Targets.Section4RightOptimality
import Targets.Section5RightScalarGain
import Targets.Section5FarRight
import Targets.Section5RetainedSignedSlope
import Targets.Section5SignedInitialEndpoint
import Targets.Section5InitialSigned

/-! The new critical-path results are checked against the same three standard
axioms as the explicit print guards below. Checking the allowed set also
accepts results which need fewer of those axioms. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``SpinGlass.Targets.constrainedPhi_initial_signed_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_initial_signed_uniform,
    ``SpinGlass.Targets.constrainedPhi_initial_signed_lt,
    ``SpinGlass.Targets.section5Initial_curvature_data,
    ``SpinGlass.Targets.coupledLinearStep_zero_signed_shared_commute,
    ``SpinGlass.Targets.continuous_constrainedPairFieldCascade_joint,
    ``SpinGlass.Targets.integrable_constrainedPairFieldCascade_frozen_pair,
    ``SpinGlass.Targets.section5SignedInitialInterpolation_eq_conditioned_average,
    ``SpinGlass.Targets.integrable_section5ConditionedInitialInterpolation_frozen,
    ``SpinGlass.Targets.section5SignedInitialInterpolation_endpoint_bound,
    ``SpinGlass.Targets.measurePreserving_neg_piGauss,
    ``SpinGlass.Targets.independentStepPi_flip_second,
    ``SpinGlass.Targets.coupledFieldCascade_independent_flip_second,
    ``SpinGlass.Targets.coupledLinearStep_anti_flip_second,
    ``SpinGlass.Targets.section5SignedInitial_anti_prefix_eq_conditioned,
    ``SpinGlass.Targets.section5ConditionedInitialVariance_nonneg,
    ``SpinGlass.Targets.hasDerivAt_section5ConditionedInitialVariance,
    ``SpinGlass.Targets.section5ConditionedInitialVariance_pos_or_eq_zero,
    ``SpinGlass.Targets.section5ConditionedInitialVelocity_zero_of_not_pos,
    ``SpinGlass.Targets.continuousOn_section5ConditionedInitialInterpolation,
    ``SpinGlass.Targets.hasDerivAt_section5ConditionedInitialInterpolation_replica,
    ``SpinGlass.Targets.deriv_section5ConditionedInitialInterpolation_le,
    ``SpinGlass.Targets.section5ConditionedInitialInterpolation_endpoint_bound,
    ``SpinGlass.Targets.configFlip_configFlip,
    ``SpinGlass.Targets.spin_configFlip,
    ``SpinGlass.Targets.overlap_configFlip_right,
    ``SpinGlass.Targets.overlap_configFlip_left,
    ``SpinGlass.Targets.constrainedPairFieldBase_flip,
    ``SpinGlass.Targets.attainableOverlap_neg,
    ``SpinGlass.Targets.constrainedPair_nonempty_neg,
    ``SpinGlass.Targets.skDisorder_basis_even_of_variance_ne_zero,
    ``SpinGlass.Targets.skDisorder_even_ae,
    ``SpinGlass.Targets.section5SignedInitialFieldEndpoint_quantitative_gain,
    ``SpinGlass.Targets.section5SignedInitialFieldEndpoint_le,
    ``SpinGlass.Targets.section5SignedInitialInterpolation_zero_le,
    ``SpinGlass.Targets.section5RetainedSignedInitial_unitCurvature,
    ``SpinGlass.Targets.hasDerivAt_section5RetainedSignedInitialV,
    ``SpinGlass.Targets.hasDerivAt_section5RetainedSignedInitialV_zero,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_zero,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_second_derivative,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_lambda_gain,
    ``SpinGlass.Targets.section5SignedInitial_unitCurvature,
    ``SpinGlass.Targets.hasDerivAt_section5SignedInitialV,
    ``SpinGlass.Targets.section5SignedInitialPrefixD_zero,
    ``SpinGlass.Targets.hasDerivAt_section5SignedInitialV_zero,
    ``SpinGlass.Targets.section5SignedInitialPrefix_zero,
    ``SpinGlass.Targets.section5SignedInitialV_zero,
    ``SpinGlass.Targets.section5SignedInitialV_second_derivative,
    ``SpinGlass.Targets.section5SignedInitialV_lambda_gain,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_deriv_lower_bound,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_slope_lower_bound,
    ``SpinGlass.Targets.section5RetainedSignedInitialV_quantitative_gain,
    ``SpinGlass.Targets.signedSplitSlope_parisiF_lower_bound,
    ``SpinGlass.Targets.signedSplitSlope_sub_overlap_lower_bound,
    ``SpinGlass.Targets.coupledLinearStep_zero_mass_zero_variance,
    ``SpinGlass.Targets.section5SignedInitialOuter_one,
    ``SpinGlass.Targets.section5SignedInitial_outer_kernel,
    ``SpinGlass.Targets.section5SignedInitial_variances_nonneg,
    ``SpinGlass.Targets.section5SignedInitialCascade_one,
    ``SpinGlass.Targets.section5SignedInitialInterpolation_one,
    ``SpinGlass.Targets.section5SignedInitialInterpolation_zero,
    ``SpinGlass.Targets.signedSplitSlope_top,
    ``SpinGlass.Targets.signedSplitSlope_top_nonneg,
    ``SpinGlass.Targets.continuous_signedSplitSlope,
    ``SpinGlass.Targets.hasDerivAt_signedSplitSlope_before_ibp,
    ``SpinGlass.Targets.hasDerivAt_signedSplitSlope,
    ``SpinGlass.Targets.hasDerivAt_signedSplitSlope_parisiF,
    ``SpinGlass.Targets.parisiStep_zero_signed_product_le,
    ``SpinGlass.Targets.signedSplitHessian_le_unsplit,
    ``SpinGlass.Targets.signedSplitHessian_parisiF_le_initial,
    ``SpinGlass.Targets.signedSplitSlope_lower_bound,
    ``SpinGlass.Targets.section5_scalar_prefix,
    ``SpinGlass.Targets.integrable_gaussian_bounded_shift,
    ``SpinGlass.Targets.abs_parisiStep_zero_le_one,
    ``SpinGlass.Targets.section4RightVarianceQ_mass_continuous_paths,
    ``SpinGlass.Targets.continuousOn_section4RightTVarianceQ_mass,
    ``SpinGlass.Targets.section4RightVarianceD_eq_massGap_mul,
    ``SpinGlass.Targets.measurable_section4RightVarianceQ,
    ``SpinGlass.Targets.section4RightVarianceQ_mem_Icc,
    ``SpinGlass.Targets.section4RightTVarianceD_eq_massGap_mul,
    ``SpinGlass.Targets.section4RightTVarianceQ_mem_Icc,
    ``SpinGlass.Targets.section4Mass_baseline_eq_next,
    ``SpinGlass.Targets.section4RightCascade_baseline_eq_reflected_next,
    ``SpinGlass.Targets.section4RightVarianceQ_baseline_eq_reflected_next,
    ``SpinGlass.Targets.section4RightTVarianceQ_baseline_eq,
    ``SpinGlass.Targets.guerraGrowth_one,
    ``SpinGlass.Targets.pairedTiltMean_mem_Icc,
    ``SpinGlass.Targets.hasDerivAt_section4RightT_variance_factor,
    ``SpinGlass.Targets.intervalIntegrable_section4RightT_variance_factor,
    ``SpinGlass.Targets.section4RightT_sub_eq_massGap_mul_integral,
    ``SpinGlass.Targets.intervalIntegrable_section4RightTVarianceQ_closed,
    ``SpinGlass.Targets.continuousOn_integral_section4RightTVarianceQ,
    ``SpinGlass.Targets.section4RightU_sub_eq_integral,
    ``SpinGlass.Targets.section4RightU_eq_integral,
    ``SpinGlass.Targets.hasDerivWithinAt_section4RightU,
    ``SpinGlass.Targets.section4RightR_nonneg,
    ``SpinGlass.Targets.convexOn_section4RightU,
    ``SpinGlass.Targets.section4RightU_ge_supportingLine,
    ``SpinGlass.Targets.section4RightU_interpolation_slope_upper_bound,
    ``SpinGlass.Targets.section4RightU_interpolation_slope_upper_bound_of_factor_eq,
    ``SpinGlass.Targets.section5FarLeft_smallness,
    ``SpinGlass.Targets.exists_constrainedPhi_right_gap_uniform_in_size,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_right_gap,
    ``SpinGlass.Targets.exists_constrainedPhi_far_right_uniform_in_size,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_far_right,
    ``SpinGlass.Targets.section4_right_inserted_variance,
    ``SpinGlass.Targets.parisiF_insertRightLevel,
    ``SpinGlass.Targets.parisiCorrection_insertRightLevel,
    ``SpinGlass.Targets.parisiFunctional_insertRightLevel,
    ``SpinGlass.Targets.section4RightPhi_baseline,
    ``SpinGlass.Targets.section4RightPhi_at_lower_overlap,
    ``SpinGlass.Targets.section4RightPhi_near_min,
    ``SpinGlass.Targets.section4RightPhi_lower_mass_min,
    ``SpinGlass.Targets.scalarMass_coupledParamDeriv,
    ``SpinGlass.Targets.section4RightMassD_base_props,
    ``SpinGlass.Targets.section4RightMassD_props,
    ``SpinGlass.Targets.hasDerivAt_section4RightT_mass,
    ``SpinGlass.Targets.hasDerivAt_section4RightT_mass_baseline,
    ``SpinGlass.Targets.section4RightU_zero_variance,
    ``SpinGlass.Targets.measurable_section4RightMassD,
    ``SpinGlass.Targets.section4RightMassD_abs_le_uniform,
    ``SpinGlass.Targets.measurable_section4RightMassE,
    ``SpinGlass.Targets.section4RightMassE_invariant,
    ``SpinGlass.Targets.section4RightMassE_deriv_props,
    ``SpinGlass.Targets.hasDerivAt_deriv_section4RightT_mass,
    ``SpinGlass.Targets.abs_second_deriv_section4RightT_mass_le_uniform,
    ``SpinGlass.Targets.section4RightT_mass_taylor_bound,
    ``SpinGlass.Targets.quadratic_remainder_of_second_bound,
    ``SpinGlass.Targets.firstVariation_sq_le_of_quadratic_comparisons,
    ``SpinGlass.Targets.hasDerivAt_section4RightPhi_mass_baseline,
    ``SpinGlass.Targets.section4RightPhi_mass_taylor_baseline,
    ``SpinGlass.Targets.section4RightFirstVariation_upper_bound,
    ``SpinGlass.Targets.constrainedPhi_le_two_guerraPsi_right_mass_variation,
    ``SpinGlass.Targets.exists_section5RightMass_improvement,
    ``SpinGlass.Targets.exists_constrainedPhi_right_mass_gap_uniform_in_size,
    ``SpinGlass.Targets.exists_constrainedPhi_right_scalar_gain_uniform_in_size,
    ``SpinGlass.Targets.stepD1_initial_totalVariance,
    ``SpinGlass.Targets.stepD2_initial_totalVariance,
    ``SpinGlass.Targets.section5LocalLeftConstant_bounds,
    ``SpinGlass.Targets.oneSidedCurvature_nonneg_of_localMin,
    ``SpinGlass.Targets.oneSidedCurvature_nonneg_of_min,
    ``SpinGlass.Targets.zeroOuterSquaredSlope_zero,
    ``SpinGlass.Targets.hasDerivWithinAt_zeroOuterSquaredSlope_zero,
    ``SpinGlass.Targets.hasDerivWithinAt_zeroOuterSquaredSlope_parisiF_zero,
    ``SpinGlass.Targets.section4TVarianceQ_zeroOverlap_stationarityBase,
    ``SpinGlass.Targets.section4TVarianceQ_zeroOverlap_terminalBase,
    ``SpinGlass.Targets.exists_section4ZeroOverlap_comparator,
    ``SpinGlass.Targets.section4THessianSquare_initial_zero_le_of_min,
    ``SpinGlass.Targets.constrainedPhi_local_right_initial_zero,
    ``SpinGlass.Targets.constrainedPhi_local_right_of_reduced_min,
    ``SpinGlass.Targets.section4TVarianceQ_initial_zero_eq_sq,
    ``SpinGlass.Targets.section4THessianSquare_initial_zero_eq_sq,
    ``SpinGlass.Targets.parisiFDeriv_initial_zero_of_min,
    ``SpinGlass.Targets.RSBScheme.padOneLast_m,
    ``SpinGlass.Targets.RSBScheme.padOneLast_q,
    ``SpinGlass.Targets.parisiF_padOneLast_succ,
    ``SpinGlass.Targets.parisiFDeriv_padOneLast_succ,
    ``SpinGlass.Targets.parisiFSecond_padOneLast_succ,
    ``SpinGlass.Targets.section4Cascade_padOneLast_succ,
    ``SpinGlass.Targets.section4VarianceQ_padOneLast,
    ``SpinGlass.Targets.section4VarianceR_padOneLast,
    ``SpinGlass.Targets.section4TVarianceQ_padOneLast,
    ``SpinGlass.Targets.section4THessianSquare_padOneLast,
    ``SpinGlass.Targets.section4RightQ_padOneLast,
    ``SpinGlass.Targets.section4RightR_padOneLast,
    ``SpinGlass.Targets.hasDerivWithinAt_section4RightQ_all_levels,
    ``SpinGlass.Targets.continuousOn_section4RightQ_all_levels,
    ``SpinGlass.Targets.section4RightR_lipschitz_uniform_all_levels,
    ``SpinGlass.Targets.section4RightQ_padOneLast_zero,
    ``SpinGlass.Targets.section4RightR_padOneLast_zero,
    ``SpinGlass.Targets.section4TVarianceQ_neighbor_full_eq_zero_all_levels,
    ``SpinGlass.Targets.section4THessianSquare_neighbor_full_eq_zero_all_levels,
    ``SpinGlass.Targets.splitScalarCascade_delete_zero_first,
    ``SpinGlass.Targets.section5RightMass_padOneLast,
    ``SpinGlass.Targets.section5RightVariance_padOneLast,
    ``SpinGlass.Targets.section5RightV_padOneLast,
    ``SpinGlass.Targets.hasDerivAt_section5RightV_zero_Q_padded,
    ``SpinGlass.Targets.deriv_section5RightV_zero_eq_Q_padded,
    ``SpinGlass.Targets.hasDerivAt_section5RightV_zero_Q_all_levels,
    ``SpinGlass.Targets.deriv_section5RightV_zero_eq_Q_all_levels,
    ``SpinGlass.Targets.hasDerivWithinAt_section5RightSlope,
    ``SpinGlass.Targets.section5RightSlope_le_local_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_le_two_guerraPsi_sub_right_factor_sq,
    ``SpinGlass.Targets.constrainedPhi_local_right_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_local_right_uniform,
    ``SpinGlass.Targets.section4Right_reflectedVariance_mem,
    ``SpinGlass.Targets.hasDerivWithinAt_section4RightQ,
    ``SpinGlass.Targets.continuousOn_section4RightQ,
    ``SpinGlass.Targets.section4RightR_lipschitz_uniform,
    ``SpinGlass.Targets.splitScalarCascade_congr_at,
    ``SpinGlass.Targets.section5RightMass_baseline_eq_next,
    ``SpinGlass.Targets.section5RightVariance_eq_reflected_next,
    ``SpinGlass.Targets.section5RightV_baseline_eq_reflected_next,
    ``SpinGlass.Targets.hasDerivAt_section5RightV_zero_Q,
    ``SpinGlass.Targets.deriv_section5RightV_zero_eq_Q,
    ``SpinGlass.Targets.stepD2_parisiF_zero_variance,
    ``SpinGlass.Targets.section4VarianceQ_neighbor_full_eq_zero,
    ``SpinGlass.Targets.section4VarianceR_neighbor_full_eq_zero,
    ``SpinGlass.Targets.section4TVarianceQ_neighbor_full_eq_zero,
    ``SpinGlass.Targets.section4THessianSquare_neighbor_full_eq_zero,
    ``SpinGlass.Targets.parisiStep_zero_sq_le,
    ``SpinGlass.Targets.parisiStep_zero_split_square_le,
    ``SpinGlass.Targets.stepD2_zero_mass_eq_parisiStep,
    ``SpinGlass.Targets.section4THessianSquare_initial_le_zero,
    ``SpinGlass.Targets.section4FirstVariation_cubic_taylor_uniform,
    ``SpinGlass.Targets.section4FirstVariation_curvature_bound_uniform,
    ``SpinGlass.Targets.scalarObservableHeat_abs_le,
    ``SpinGlass.Targets.hasDerivAt_tiltP_variance_heat,
    ``SpinGlass.Targets.scalarTiltMean_variance_derivative_bound,
    ``SpinGlass.Targets.abs_stepD2Variance_le_of_C4,
    ``SpinGlass.Targets.abs_stepD2Variance_parisiF_le,
    ``SpinGlass.Targets.hasDerivAt_stepD3_parisiF_uniform,
    ``SpinGlass.Targets.section4HessianInitialDerivative_props,
    ``SpinGlass.Targets.hasDerivAt_section4THessianSquare_uniform,
    ``SpinGlass.Targets.abs_deriv_section4THessianSquare_le_uniform,
    ``SpinGlass.Targets.section4THessianSquare_lipschitz_uniform,
    ``SpinGlass.Targets.abs_deriv3_section4FirstVariation_le_uniform,
    ``SpinGlass.Targets.section4VarianceR_baseline_deriv_props,
    ``SpinGlass.Targets.hasDerivAt_section4THessianSquare_of_initial_derivative,
    ``SpinGlass.Targets.abs_deriv_section4THessianSquare_le_of_initial_derivative,
    ``SpinGlass.Targets.hasDerivAt_splitBaselineHessianSquare_before_ibp,
    ``SpinGlass.Targets.measurable_splitBaselineHessianDerivative,
    ``SpinGlass.Targets.abs_splitBaselineHessianDerivative_le,
    ``SpinGlass.Targets.abs_deriv_splitBaselineHessianSquare_le,
    ``SpinGlass.Targets.section5LeftSlope_initial_ge_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_initial_left_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_initial_left_of_hessian_lipschitz,
    ``SpinGlass.Targets.pairedTiltMean_abs_sub_le,
    ``SpinGlass.Targets.section4VarianceR_baseline_lipschitz_of_initial_factor,
    ``SpinGlass.Targets.section4THessianSquare_lipschitz_of_initial_factor,
    ``SpinGlass.Targets.section4VarianceR_initial_eq_scalar_integral,
    ``SpinGlass.Targets.section4THessianSquare_lipschitz_of_scalar_integral,
    ``SpinGlass.Targets.abs_sub_le_of_derivative_bound_on_open_interval,
    ``SpinGlass.Targets.section4THessianSquare_lipschitz_of_initial_derivative,
    ``SpinGlass.Targets.abs_parisiFourthPolynomial_le,
    ``SpinGlass.Targets.hasDerivAt_stepD3Uniform,
    ``SpinGlass.Targets.parisiFourthPolynomial_stepD4Uniform,
    ``SpinGlass.Targets.abs_stepD4Uniform_le,
    ``SpinGlass.Targets.continuous_stepD4Uniform_variance_spatial,
    ``SpinGlass.Targets.parisiFourthPolynomial_mass_change,
    ``SpinGlass.Targets.parisiFourthPolynomial_lower_mass_bound,
    ``SpinGlass.Targets.parisiFFourth_props,
    ``SpinGlass.Targets.hasDerivAt_parisiFThird,
    ``SpinGlass.Targets.continuous_parisiFFourth,
    ``SpinGlass.Targets.abs_parisiFFourth_le_43,
    ``SpinGlass.Targets.abs_stepD4Uniform_parisiF_le,
    ``SpinGlass.Targets.hasDerivAt_stepD3Uniform_parisiF,
    ``SpinGlass.Targets.constrainedPhi_local_left_uniform,
    ``SpinGlass.Targets.constrainedPhi_initial_left_uniform,
    ``SpinGlass.Targets.hasDerivAt_gaussian_weighted_exp_variance,
    ``SpinGlass.Targets.hasDerivAt_stepD2_variance,
    ``SpinGlass.Targets.continuousOn_stepD2Variance,
    ``SpinGlass.Targets.continuousOn_stepD3_variance_spatial,
    ``SpinGlass.Targets.hasFDerivAt_stepD2_variance_spatial,
    ``SpinGlass.Targets.hasDerivAt_stepD2_variance_curve,
    ``SpinGlass.Targets.hasDerivAt_deriv_section4FirstVariation,
    ``SpinGlass.Targets.hasDerivAt_section4FirstVariationD2_of_hessian_derivative,
    ``SpinGlass.Targets.hasDerivAt_deriv2_section4FirstVariation_of_hessian_derivative,
    ``SpinGlass.Targets.abs_deriv3_section4FirstVariation_le_of_hessian_derivative,
    ``SpinGlass.Targets.hasDerivAt_deriv2_section4FirstVariation_beta_zero,
    ``SpinGlass.Targets.abs_deriv3_section4FirstVariation_le_of_initial_derivative,
    ``SpinGlass.Targets.hasDerivWithinAt_section5LeftSlope,
    ``SpinGlass.Targets.section5LeftSlope_ge_local_of_endpoint_curvature,
    ``SpinGlass.Targets.constrainedPhi_local_left_of_endpoint_curvature,
    ``SpinGlass.Targets.section5LocalLeftConstant_pos,
    ``SpinGlass.Targets.constrainedPhi_local_left_of_hessian_lipschitz,
    ``SpinGlass.Targets.hasDerivAt_tiltP_spatial,
    ``SpinGlass.Targets.hasDerivAt_scalarTiltMean_spatial,
    ``SpinGlass.Targets.hasDerivAt_stepD2_uniform,
    ``SpinGlass.Targets.scalarTiltMean_abs_le,
    ``SpinGlass.Targets.continuous_scalarTiltMean_joint,
    ``SpinGlass.Targets.parisiThirdPolynomial_mass_change,
    ``SpinGlass.Targets.parisiThirdPolynomial_lower_mass_bound,
    ``SpinGlass.Targets.parisiThirdPolynomial_stepD3Uniform,
    ``SpinGlass.Targets.parisiFThird_props,
    ``SpinGlass.Targets.hasDerivAt_parisiFSecond,
    ``SpinGlass.Targets.continuous_parisiFThird,
    ``SpinGlass.Targets.abs_parisiFThird_le_six,
    ``SpinGlass.Targets.abs_parisiThirdPolynomial_le,
    ``SpinGlass.Targets.abs_stepD3Uniform_le,
    ``SpinGlass.Targets.continuous_stepD3Uniform_variance_spatial,
    ``SpinGlass.Targets.hasDerivAt_stepD2_parisiF_uniform,
    ``SpinGlass.Targets.abs_stepD3Uniform_parisiF_le,
    ``SpinGlass.Targets.stepD3_eq_stepD3Uniform,
    ``SpinGlass.Targets.abs_stepD3_parisiF_le_uniform,
    ``SpinGlass.Targets.pairFieldPotential_independent_contraction,
    ``SpinGlass.Targets.pairFieldPotential_shared_contraction,
    ``SpinGlass.Targets.pairFieldCovariance_diagonal,
    ``SpinGlass.Targets.constrainedReplicaHeat_contraction,
    ``SpinGlass.Targets.constrainedLevelVarianceD_independent_overlap,
    ``SpinGlass.Targets.constrainedLevelVarianceD_shared_overlap,
    ``SpinGlass.Targets.integrable_constrainedReplicaHeatExpression,
    ``SpinGlass.Targets.integral_constrainedReplicaHeatExpression,
    ``SpinGlass.Targets.integral_constrainedLevelVarianceD_independent_overlap,
    ``SpinGlass.Targets.integral_constrainedLevelVarianceD_shared_overlap,
    ``SpinGlass.Targets.normalized_trace_heat_eq_replica,
    ``SpinGlass.Targets.section5InterpolationVelocity_zero_of_not_pos,
    ``SpinGlass.Targets.section5RightInterpolationVelocity_zero_of_not_pos,
    ``SpinGlass.Targets.hasDerivAt_section5Interpolation_replica,
    ``SpinGlass.Targets.hasDerivAt_section5RightInterpolation_replica,
    ``SpinGlass.Targets.replicaHeatSum_telescope,
    ``SpinGlass.Targets.replicaHeatSum_telescope_fin,
    ``SpinGlass.Targets.replicaHeatSum_weighted_fin,
    ``SpinGlass.Targets.replicaCovariance_mass_telescope,
    ``SpinGlass.Targets.replicaTrace_sub_heatSum,
    ``SpinGlass.Targets.replicaTrace_sub_weighted_heat_fin,
    ``SpinGlass.Targets.pairFieldCovariance_split_increment,
    ``SpinGlass.Targets.replicaHeatTail_reverse_increments,
    ``SpinGlass.Targets.pairFieldCovariance_split_increment_kernel,
    ``SpinGlass.Targets.replicaHeatTail_pairFieldCovariance,
    ``SpinGlass.Targets.sum_pairField_heat_diagonal,
    ``SpinGlass.Targets.replicaMassGap_reverse,
    ``SpinGlass.Targets.pairCovarianceExpression_eq_trace_sub_heat,
    ``SpinGlass.Targets.averagedReplicaPressureDerivative_eq_covariance,
    ``SpinGlass.Targets.averagedReplicaPressureDerivative_le,
    ``SpinGlass.Targets.deriv_section5Interpolation_le,
    ``SpinGlass.Targets.section5Interpolation_endpoint_bound,
    ``SpinGlass.Targets.deriv_section5RightInterpolation_le,
    ``SpinGlass.Targets.section5RightInterpolation_endpoint_bound,
    ``SpinGlass.Targets.pairedTiltMean_sq_le,
    ``SpinGlass.Targets.pairedSecondCovariance_mass_invariant,
    ``SpinGlass.Targets.parisiStep_mass_derivatives_local_uniform,
    ``SpinGlass.Targets.measurable_second_deriv_parisiStep_mass,
    ``SpinGlass.Targets.measurable_section4MassE,
    ``SpinGlass.Targets.section4MassSecondBound_nonneg,
    ``SpinGlass.Targets.section4MassE_invariant,
    ``SpinGlass.Targets.section4MassE_abs_le_uniform,
    ``SpinGlass.Targets.section4MassE_deriv_props,
    ``SpinGlass.Targets.hasDerivAt_section4TMassD,
    ``SpinGlass.Targets.hasDerivAt_deriv_section4T_mass,
    ``SpinGlass.Targets.section4T_second_mass_derivative_uniform,
    ``SpinGlass.Targets.abs_second_deriv_section4T_mass_le_uniform,
    ``SpinGlass.Targets.section4Phi_second_mass_derivative_uniform,
    ``SpinGlass.Targets.abs_second_deriv_section4Phi_mass_le_uniform,
    ``SpinGlass.Targets.section4T_mass_derivative_lipschitz,
    ``SpinGlass.Targets.section4T_mass_taylor_bound,
    ``SpinGlass.Targets.section4Phi_mass_derivative_lipschitz,
    ``SpinGlass.Targets.section4Phi_mass_taylor_bound,
    ``SpinGlass.Targets.section4T_mass_taylor_baseline,
    ``SpinGlass.Targets.section4Phi_mass_taylor_baseline,
    ``SpinGlass.Targets.section4OptimalityBound_pos,
    ``SpinGlass.Targets.section4FirstVariation_lower_bound,
    ``SpinGlass.Targets.exists_section4FirstVariation_lower_bound,
    ``SpinGlass.Targets.antitoneOn_section4TVarianceQ_baseline,
    ``SpinGlass.Targets.concaveOn_section4U,
    ``SpinGlass.Targets.section4U_le_supportingLine,
    ``SpinGlass.Targets.section4U_sub_ge_supportingLine,
    ``SpinGlass.Targets.section4U_interpolation_slope_lower_bound,
    ``SpinGlass.Targets.section4U_interpolation_slope_lower_bound_of_factor_eq,
    ``SpinGlass.Targets.stepD1_parisiF_zero_variance,
    ``SpinGlass.Targets.section4Cascade_zero_variance_mass_independent,
    ``SpinGlass.Targets.section4VarianceQ_zero_mass_independent,
    ``SpinGlass.Targets.section4TVarianceQ_zero_mass_independent,
    ``SpinGlass.Targets.hasDerivWithinAt_section4T_variance_factor,
    ``SpinGlass.Targets.hasDerivWithinAt_section4Phi_overlap,
    ``SpinGlass.Targets.derivative_nonpos_of_min_at_right,
    ``SpinGlass.Targets.section4_overlap_le_endpointQ_of_min,
    ``SpinGlass.Targets.constrainedPhi_le_two_guerraPsi_sub_factor_sq,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_factor_ne,
    ``SpinGlass.Targets.constrainedPhi_le_two_guerraPsi_mass_taylor,
    ``SpinGlass.Targets.constrainedPhi_le_two_guerraPsi_sub_mass_gain,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_mass_slope_pos,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_left_gap,
    ``SpinGlass.Targets.exists_constrainedPhi_left_gap_uniform_in_size,
    ``SpinGlass.Targets.constrainedPhi_le_guerraPsi_right_lambda_gain,
    ``SpinGlass.Targets.constrainedPhi_le_guerraPsi_right,
    ``SpinGlass.Targets.constrainedPhi_lt_guerraPsi_right_of_lambda_deriv_ne,
    ``SpinGlass.Targets.parisiF_lowerMass_prefix,
    ``SpinGlass.Targets.parisiFDeriv_lowerMass_prefix,
    ``SpinGlass.Targets.section4Phi_stationarityBase_min,
    ``SpinGlass.Targets.derivative_nonneg_of_min_at_left,
    ``SpinGlass.Targets.pairedSecondMean_zero_variance,
    ``SpinGlass.Targets.section4Cascade_stationarityBase_endpoint,
    ``SpinGlass.Targets.section4VarianceQ_stationarityBase_endpoint_base,
    ``SpinGlass.Targets.section4VarianceQ_stationarityBase_endpoint,
    ``SpinGlass.Targets.section4TVarianceQ_stationarityBase_endpoint,
    ``SpinGlass.Targets.section4_endpointQ_le_overlap_of_min,
    ``SpinGlass.Targets.section4TVarianceQ_zero_eq_overlap_of_min,
    ``SpinGlass.Targets.hasDerivWithinAt_section4U_zero_of_min,
    ``SpinGlass.Targets.hasDerivWithinAt_section4FirstVariation_upper_zero_of_min,
    ``SpinGlass.Targets.derivWithin_section4U_zero_of_min,
    ``SpinGlass.Targets.derivWithin_section4FirstVariation_upper_zero_of_min,
    ``SpinGlass.Targets.section5FarLeftBound_pos,
    ``SpinGlass.Targets.constrainedPhi_lt_two_guerraPsi_of_far_left,
    ``SpinGlass.Targets.exists_constrainedPhi_far_left_uniform_in_size,
    ``SpinGlass.Targets.section4FirstVariationD2_lipschitz_of_hessian_lipschitz,
    ``SpinGlass.Targets.section4FirstVariation_cubic_taylor_of_hessian_lipschitz,
    ``SpinGlass.Targets.section4FirstVariation_stationary_cubic_of_hessian_lipschitz,
    ``SpinGlass.Targets.section4FirstVariation_curvature_lower_bound_of_hessian_lipschitz,
    ``SpinGlass.Targets.RSBScheme.overlap_directions_of_strict,
    ``SpinGlass.Targets.section4TVarianceQ_zero_eq_overlap_of_reduced_min,
    ``SpinGlass.Targets.exists_stationary_reduction_of_min,
    ``SpinGlass.Targets.section4Phi_terminalBase_min,
    ``SpinGlass.Targets.section4Cascade_terminalBase_endpoint,
    ``SpinGlass.Targets.section4VarianceQ_terminalBase_endpoint,
    ``SpinGlass.Targets.section4TVarianceQ_terminalBase_endpoint,
    ``SpinGlass.Targets.section4_terminal_endpointQ_le_overlap_of_min,
    ``SpinGlass.Targets.section4TVarianceQ_terminal_zero_eq_overlap_of_min,
    ``SpinGlass.Targets.section4TVarianceQ_zero_eq_overlap_of_min_all_levels,
    ``SpinGlass.Targets.hasDerivWithinAt_section4U_zero_of_min_all_levels,
    ``SpinGlass.Targets.hasDerivWithinAt_section4FirstVariation_upper_zero_of_min_all_levels,
    ``SpinGlass.Targets.derivWithin_section4U_zero_of_min_all_levels,
    ``SpinGlass.Targets.derivWithin_section4FirstVariation_upper_zero_of_min_all_levels,
    ``SpinGlass.Targets.section4THessianSquare_initial_integral_le_overlap_of_min,
    ``SpinGlass.Targets.section4FirstVariation_initial_curvature_le_of_hessian_lipschitz,
    ``SpinGlass.Targets.section4FirstVariation_initial_short_curvature_bound,
    ``SpinGlass.Targets.section4VarianceR_baseline_continuous_paths,
    ``SpinGlass.Targets.continuousOn_section4THessianSquare,
    ``SpinGlass.Targets.section4TVarianceQ_baseline_sub_eq_integral,
    ``SpinGlass.Targets.hasDerivWithinAt_section4TVarianceQ_baseline,
    ``SpinGlass.Targets.derivWithin_section4TVarianceQ_baseline_eq,
    ``SpinGlass.Targets.section4FirstVariation_initial_curvature_bound_of_hessian_lipschitz,
    ``SpinGlass.Targets.section4FirstVariation_curvature_bound_of_hessian_lipschitz_all_levels,
    ``SpinGlass.Targets.cascadeT_raiseMass_zero_variance,
    ``SpinGlass.Targets.parisiCorrection_raiseMass_zero_variance,
    ``SpinGlass.Targets.guerraPsi_raiseMass_zero_variance,
    ``SpinGlass.Targets.RSBScheme.mergeEqualOverlap_mass,
    ``SpinGlass.Targets.RSBScheme.mergeEqualOverlap_strict_mass,
    ``SpinGlass.Targets.parisiFunctional_mergeEqualOverlap,
    ``SpinGlass.Targets.guerraPsi_mergeEqualOverlap,
    ``SpinGlass.Targets.minimizer_mergeEqualOverlap,
    ``SpinGlass.Targets.guerraPhi_raiseMass_zero_variance,
    ``SpinGlass.Targets.guerraPhi_mergeEqualOverlap,
    ``SpinGlass.Targets.exists_strict_overlap_reduction,
    ``SpinGlass.Targets.exists_strict_mass_overlap_reduction,
    ``SpinGlass.Targets.talagrand_theorem_2_2_of_strict_mass_overlap_quadratic_bound,
    ``SpinGlass.Targets.neg_curvature_le_of_cubic_upper,
    ``SpinGlass.Targets.neg_curvature_le_sixth_root_of_cubic_remainder,
    ``SpinGlass.Targets.hasDerivWithinAt_section4FirstVariation_D,
    ``SpinGlass.Targets.hasDerivWithinAt_section4FirstVariationD_D2,
    ``SpinGlass.Targets.hasDerivWithinAt_derivWithin_section4FirstVariation,
    ``SpinGlass.Targets.derivWithin2_section4FirstVariation_eq,
    ``SpinGlass.Targets.section4FirstVariationD_upper_zero_of_min,
    ``SpinGlass.Targets.section4FirstVariation_curvature_lower_bound_of_cubic_remainder] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

/--
info: 'SpinGlass.Targets.guerra_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerra_identity

/--
info: 'SpinGlass.Targets.guerra_rsb_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerra_rsb_bound

/--
info: 'SpinGlass.Targets.limsup_free_entropy_le_parisiValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.limsup_free_entropy_le_parisiValue

/--
info: 'SpinGlass.Targets.hasDerivAt_guerraGap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_guerraGap

/--
info: 'SpinGlass.Targets.guerraRemainder_le_of_overlapTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraRemainder_le_of_overlapTail

/--
info: 'SpinGlass.Targets.guerraPhi_uniform_of_overlap_concentration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraPhi_uniform_of_overlap_concentration

/--
info: 'SpinGlass.Targets.talagrand_theorem_2_2_of_overlap_concentration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_theorem_2_2_of_overlap_concentration

/--
info: 'SpinGlass.Targets.coupledPhi_eq_two_guerraPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledPhi_eq_two_guerraPhi

/--
info: 'SpinGlass.Targets.coupledObservable_eq_replicaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledObservable_eq_replicaMeasure

/--
info: 'SpinGlass.Targets.guerraReplicaExpectation_eq_sum_measures' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraReplicaExpectation_eq_sum_measures

/--
info: 'SpinGlass.Targets.guerraOverlapTail_le_of_replicaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraOverlapTail_le_of_replicaMeasure

/--
info: 'SpinGlass.Targets.independentStepPi_eq_nested' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.independentStepPi_eq_nested

/--
info: 'SpinGlass.Targets.constrainedBase_eq_add_log_event' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedBase_eq_add_log_event

/--
info: 'SpinGlass.Targets.coupledEvent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledEvent_pos

/--
info: 'SpinGlass.Targets.log_coupledEvent_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.log_coupledEvent_le_gap

/--
info: 'SpinGlass.Targets.coupledCascade_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledCascade_dist_le

/--
info: 'SpinGlass.Targets.gaussianCoupledGap_upper_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.gaussianCoupledGap_upper_tail

/--
info: 'SpinGlass.Targets.integrable_gaussianCoupledGap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_gaussianCoupledGap

/--
info: 'SpinGlass.Targets.integrable_gaussianCoupledEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_gaussianCoupledEvent

/--
info: 'SpinGlass.Targets.gaussianCoupledEvent_small' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.gaussianCoupledEvent_small

/--
info: 'SpinGlass.Targets.coupledGaussian_pair_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledGaussian_pair_map

/--
info: 'SpinGlass.Targets.gaussianCoupledGap_mean_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.gaussianCoupledGap_mean_eq

/--
info: 'SpinGlass.Targets.gaussianCoupledEvent_mean_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.gaussianCoupledEvent_mean_eq

/--
info: 'SpinGlass.Targets.talagrand_lemma_2_6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_lemma_2_6

/--
info: 'SpinGlass.Targets.talagrand_proposition_2_5' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_proposition_2_5

/--
info: 'SpinGlass.Targets.coupledSite_spin_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledSite_spin_sum

/--
info: 'SpinGlass.Targets.hasDerivAt_coupledSite_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_coupledSite_zero

/--
info: 'SpinGlass.Targets.lambdaCoupledBase_time_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.lambdaCoupledBase_time_zero

/--
info: 'SpinGlass.Targets.constrainedBase_time_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedBase_time_zero_le

/--
info: 'SpinGlass.Targets.constrainedCascade_le_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascade_le_lambda

/--
info: 'SpinGlass.Targets.lambdaCoupledPhi_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.lambdaCoupledPhi_zero

/--
info: 'SpinGlass.Targets.constrainedPhi_le_lambdaCoupledPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPhi_le_lambdaCoupledPhi

/--
info: 'SpinGlass.Targets.lambdaCoupledPhi_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.lambdaCoupledPhi_dist_le

/--
info: 'SpinGlass.Targets.coupledSite_eq_gtTerminal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledSite_eq_gtTerminal

/--
info: 'SpinGlass.Targets.sharedStepPi_eq_gtVectorStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.sharedStepPi_eq_gtVectorStep

/--
info: 'SpinGlass.Targets.independentStepPi_eq_gtVectorSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.independentStepPi_eq_gtVectorSteps

/--
info: 'SpinGlass.Targets.pairedScalarCascade_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedScalarCascade_good

/--
info: 'SpinGlass.Targets.pairedVectorCascade_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedVectorCascade_eq_sum

/--
info: 'SpinGlass.Targets.pairedVectorCascade_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedVectorCascade_const

/--
info: 'SpinGlass.Targets.hasDerivAt_pairedScalarCascade' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_pairedScalarCascade

/--
info: 'SpinGlass.Targets.coupledFieldCascade_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_eq_sum

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_le

/--
info: 'SpinGlass.Targets.coupledFieldCascade_insert_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_insert_zero

/--
info: 'SpinGlass.Targets.coupledFieldCascade_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_affine

/--
info: 'SpinGlass.Targets.section5Mass_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Mass_mono

/--
info: 'SpinGlass.Targets.section5Rho_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Rho_mono

/--
info: 'SpinGlass.Targets.section5InterpolationVariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5InterpolationVariance_nonneg

/--
info: 'SpinGlass.Targets.section5FieldEndpoint_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5FieldEndpoint_le

/--
info: 'SpinGlass.Targets.hasDerivAt_section5V' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5V

/--
info: 'SpinGlass.Targets.section5Interpolation_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Interpolation_zero

/--
info: 'SpinGlass.Targets.section5Interpolation_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Interpolation_one

/--
info: 'SpinGlass.Targets.section5Interpolation_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Interpolation_zero_le

/--
info: 'SpinGlass.Targets.constrainedPairFieldBase_eq_gtStateLogPartition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldBase_eq_gtStateLogPartition

/--
info: 'SpinGlass.Targets.contDiff_constrainedPairFieldBase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.contDiff_constrainedPairFieldBase

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase_second

/--
info: 'SpinGlass.Targets.pairSKCovariance_spectral_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairSKCovariance_spectral_sum

/--
info: 'SpinGlass.Targets.constrainedPairSecond_SK_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairSecond_SK_trace

/--
info: 'SpinGlass.Targets.independent_pair_spin_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.independent_pair_spin_contraction

/--
info: 'SpinGlass.Targets.shared_pair_spin_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.shared_pair_spin_contraction

/--
info: 'SpinGlass.Targets.pairCovariance_completion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCovariance_completion

/--
info: 'SpinGlass.Targets.pairCovarianceDefect_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCovarianceDefect_self

/--
info: 'SpinGlass.Targets.pairCascadeCorrection_telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCascadeCorrection_telescope

/--
info: 'SpinGlass.Targets.pairCovarianceExpression_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCovarianceExpression_eq

/--
info: 'SpinGlass.Targets.pairCovarianceExpression_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCovarianceExpression_le

/--
info: 'SpinGlass.Targets.pairCascadeCorrection_eq_signed_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairCascadeCorrection_eq_signed_split

/--
info: 'SpinGlass.Targets.section5Correction_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Correction_eq

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_mass_entropy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_mass_entropy

/--
info: 'SpinGlass.Targets.integral_tiltWeight_mul_log_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integral_tiltWeight_mul_log_nonneg

/--
info: 'SpinGlass.Targets.monotoneOn_parisiStep_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotoneOn_parisiStep_mass_pos

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_mass

/--
info: 'SpinGlass.Targets.parisiStep_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_add

/--
info: 'SpinGlass.Targets.section5V_zero_eq_two_section4T' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5V_zero_eq_two_section4T

/--
info: 'SpinGlass.Targets.section4T_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_baseline

/--
info: 'SpinGlass.Targets.section5V_zero_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5V_zero_baseline

/--
info: 'SpinGlass.Targets.card_attainableOverlaps_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.card_attainableOverlaps_le

/--
info: 'SpinGlass.Targets.guerraReplicaMeasure_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraReplicaMeasure_finset_sum

/--
info: 'SpinGlass.Targets.guerraReplicaMeasure_overlapTail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraReplicaMeasure_overlapTail_le

/--
info: 'SpinGlass.Targets.talagrand_replica_tail_of_quadratic_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_replica_tail_of_quadratic_bound

/--
info: 'SpinGlass.Targets.talagrand_proposition_2_3_of_quadratic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_proposition_2_3_of_quadratic_bound

/--
info: 'SpinGlass.Targets.guerraOverlapTail_eventually_of_quadratic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraOverlapTail_eventually_of_quadratic_bound

/--
info: 'SpinGlass.Targets.guerraPhi_uniform_of_quadratic_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraPhi_uniform_of_quadratic_bound

/--
info: 'SpinGlass.Targets.pairedTiltMean_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedTiltMean_abs_le

/--
info: 'SpinGlass.Targets.CoupledParamDeriv.fieldCascade' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledParamDeriv.fieldCascade

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeD_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeD_abs_le

/--
info: 'SpinGlass.Targets.hasDerivAt_pairedSecondMean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_pairedSecondMean

/--
info: 'SpinGlass.Targets.hasDerivAt_pairedSharedMean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_pairedSharedMean

/--
info: 'SpinGlass.Targets.constrainedPairSecond_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairSecond_abs_le

/--
info: 'SpinGlass.Targets.hasDerivAt_sharedConstrainedPair_second' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_sharedConstrainedPair_second

/--
info: 'SpinGlass.Targets.CoupledParamDeriv.fieldCascadeSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledParamDeriv.fieldCascadeSecond

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_second

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeSecond_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeSecond_eq

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeSecond_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeSecond_abs_le

/--
info: 'SpinGlass.Targets.measurable_constrainedPairFieldCascadeSecond' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedPairFieldCascadeSecond

/--
info: 'SpinGlass.Targets.continuous_constrainedPairFieldCascadeDirection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_constrainedPairFieldCascadeDirection

/--
info: 'SpinGlass.Targets.measurable_constrainedPairFieldCascadeSecond_disorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedPairFieldCascadeSecond_disorder

/--
info: 'SpinGlass.Targets.stein_constrainedPairFieldCascadeDirection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stein_constrainedPairFieldCascadeDirection

/--
info: 'SpinGlass.Targets.stein_constrainedPairFieldCascadeTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stein_constrainedPairFieldCascadeTrace

/--
info: 'SpinGlass.Targets.UnitLambdaCurvature.finiteStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.UnitLambdaCurvature.finiteStep

/--
info: 'SpinGlass.Targets.section5V_second_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5V_second_derivative

/--
info: 'SpinGlass.Targets.talagrand_lemma_5_9' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_lemma_5_9

/--
info: 'SpinGlass.Targets.section5V_lambda_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5V_lambda_gain

/--
info: 'SpinGlass.Targets.section5Interpolation_zero_lambda_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Interpolation_zero_lambda_gain

/--
info: 'SpinGlass.Targets.hasDerivAt_integral_gaussian_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_integral_gaussian_variance

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_variance

/--
info: 'SpinGlass.Targets.parisiStepPi_zero_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStepPi_zero_add

/--
info: 'SpinGlass.Targets.parisiFunctional_dropZeroFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiFunctional_dropZeroFirst

/--
info: 'SpinGlass.Targets.minimizer_dropZeroFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.minimizer_dropZeroFirst

/--
info: 'SpinGlass.Targets.guerraCascade_dropZeroFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraCascade_dropZeroFirst

/--
info: 'SpinGlass.Targets.exists_positive_first_mass_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.exists_positive_first_mass_reduction

/--
info: 'SpinGlass.Targets.talagrand_theorem_2_2_of_positive_mass_quadratic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_theorem_2_2_of_positive_mass_quadratic_bound

/--
info: 'SpinGlass.Targets.hasParisiC2_parisiStep_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasParisiC2_parisiStep_nonneg

/--
info: 'SpinGlass.Targets.parisiF_C2_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiF_C2_props

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_variance

/--
info: 'SpinGlass.Targets.continuous_parisiStep_variance_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_parisiStep_variance_spatial

/--
info: 'SpinGlass.Targets.continuous_parisiFSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_parisiFSecond

/--
info: 'SpinGlass.Targets.hasFDerivAt_parisiStep_variance_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasFDerivAt_parisiStep_variance_spatial

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_split_field' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_split_field

/--
info: 'SpinGlass.Targets.deriv_parisiStep_parisiF_variance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_parisiStep_parisiF_variance_mem_Icc

/--
info: 'SpinGlass.Targets.parisiStepPi_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStepPi_add

/--
info: 'SpinGlass.Targets.cascadeT_mergeEqualMass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.cascadeT_mergeEqualMass

/--
info: 'SpinGlass.Targets.parisiFunctional_mergeEqualMass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiFunctional_mergeEqualMass

/--
info: 'SpinGlass.Targets.minimizer_mergeEqualMass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.minimizer_mergeEqualMass

/--
info: 'SpinGlass.Targets.guerraPhi_mergeEqualMass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.guerraPhi_mergeEqualMass

/--
info: 'SpinGlass.Targets.exists_strict_mass_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.exists_strict_mass_reduction

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase_field' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldBase_field

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldDirection_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldDirection_field

/--
info: 'SpinGlass.Targets.constrainedPairFieldBase_fieldParamDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldBase_fieldParamDeriv

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_field

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_field_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairFieldCascade_field_second

/--
info: 'SpinGlass.Targets.constrainedPairCascadeSpatialFirst_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairCascadeSpatialFirst_abs_le

/--
info: 'SpinGlass.Targets.constrainedPairCascadeSpatialSecond_abs_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairCascadeSpatialSecond_abs_le

/--
info: 'SpinGlass.Targets.measurable_constrainedPairCascadeSpatialSecond' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedPairCascadeSpatialSecond

/--
info: 'SpinGlass.Targets.pairFieldPotential_left_single' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairFieldPotential_left_single

/--
info: 'SpinGlass.Targets.pairFieldPotential_shared_single' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairFieldPotential_shared_single

/--
info: 'SpinGlass.Targets.talagrand_theorem_2_2_of_strict_mass_quadratic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_theorem_2_2_of_strict_mass_quadratic_bound

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_param_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_param_local

/--
info: 'SpinGlass.Targets.hasDerivAt_split_parisiStep_before_ibp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_split_parisiStep_before_ibp

/--
info: 'SpinGlass.Targets.integral_mul_first_tiltWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integral_mul_first_tiltWeight

/--
info: 'SpinGlass.Targets.hasDerivAt_split_parisiStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_split_parisiStep

/--
info: 'SpinGlass.Targets.hasDerivAt_split_parisiF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_split_parisiF

/--
info: 'SpinGlass.Targets.deriv_split_parisiStep_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_split_parisiStep_nonneg

/--
info: 'SpinGlass.Targets.parisiStep_eq_dslope_cgf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_eq_dslope_cgf

/--
info: 'SpinGlass.Targets.analyticAt_parisiStep_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.analyticAt_parisiStep_mass

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_mass_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_mass_zero

/--
info: 'SpinGlass.Targets.differentiable_parisiStep_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiable_parisiStep_mass

/--
info: 'SpinGlass.Targets.deriv_parisiStep_mass_nonneg_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_parisiStep_mass_nonneg_all

/--
info: 'SpinGlass.Targets.monotone_parisiStep_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotone_parisiStep_mass

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_mass_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_parisiF_mass_zero

/--
info: 'SpinGlass.Targets.parisiF_insertLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiF_insertLevel

/--
info: 'SpinGlass.Targets.parisiCorrection_insertLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiCorrection_insertLevel

/--
info: 'SpinGlass.Targets.parisiFunctional_insertLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiFunctional_insertLevel

/--
info: 'SpinGlass.Targets.section4Phi_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_baseline

/--
info: 'SpinGlass.Targets.section4Phi_at_upper_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_at_upper_overlap

/--
info: 'SpinGlass.Targets.section4Phi_near_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_near_min

/--
info: 'SpinGlass.Targets.section4Phi_upper_mass_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_upper_mass_min

/--
info: 'SpinGlass.Targets.continuous_split_parisiStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_split_parisiStep

/--
info: 'SpinGlass.Targets.monotoneOn_split_parisiStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotoneOn_split_parisiStep

/--
info: 'SpinGlass.Targets.monotoneOn_split_parisiF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotoneOn_split_parisiF

/--
info: 'SpinGlass.Targets.parisiStep_mono_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_mono_of_growth

/--
info: 'SpinGlass.Targets.section4Cascade_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Cascade_split

/--
info: 'SpinGlass.Targets.section4Cascade_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Cascade_monotoneOn

/--
info: 'SpinGlass.Targets.monotoneOn_section4T' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotoneOn_section4T

/--
info: 'SpinGlass.Targets.continuousOn_section4T' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4T

/--
info: 'SpinGlass.Targets.section4T_zero_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_zero_variance

/--
info: 'SpinGlass.Targets.parisiF_le_section4T' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiF_le_section4T

/--
info: 'SpinGlass.Targets.section4VarianceD_base_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceD_base_props

/--
info: 'SpinGlass.Targets.section4VarianceD_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceD_props

/--
info: 'SpinGlass.Targets.hasDerivAt_section4T_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4T_variance

/--
info: 'SpinGlass.Targets.abs_deriv_section4T_variance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_deriv_section4T_variance_le

/--
info: 'SpinGlass.Targets.constrainedPairCascadeSpatialFirst_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairCascadeSpatialFirst_sum

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairCascadeSpatialLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairCascadeSpatialLine

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairCascadeSpatialFirst_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairCascadeSpatialFirst_line

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStepPi_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStepPi_variance

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairField_linear_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairField_linear_variance

/--
info: 'SpinGlass.Targets.hasDerivAt_sharedStepPi_constrained_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_sharedStepPi_constrained_variance

/--
info: 'SpinGlass.Targets.measurePreserving_pairedGaussianSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurePreserving_pairedGaussianSplit

/--
info: 'SpinGlass.Targets.independentStepPi_eq_packed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.independentStepPi_eq_packed

/--
info: 'SpinGlass.Targets.hasDerivAt_independentStepPi_constrained_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_independentStepPi_constrained_variance

/--
info: 'SpinGlass.Targets.sharedStepPi_variance_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.sharedStepPi_variance_zero

/--
info: 'SpinGlass.Targets.coupledFieldCascade_insert_shared_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_insert_shared_zero

/--
info: 'SpinGlass.Targets.coupledFieldCascade_cutoff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_cutoff_zero

/--
info: 'SpinGlass.Targets.section5RightMass_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightMass_mono

/--
info: 'SpinGlass.Targets.section5RightRho_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightRho_mono

/--
info: 'SpinGlass.Targets.section5RightMass_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightMass_endpoints

/--
info: 'SpinGlass.Targets.section5RightRho_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightRho_endpoints

/--
info: 'SpinGlass.Targets.section5RightVariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightVariance_nonneg

/--
info: 'SpinGlass.Targets.section5RightInterpolationVariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolationVariance_nonneg

/--
info: 'SpinGlass.Targets.section5RightInterpolation_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolation_zero

/--
info: 'SpinGlass.Targets.section5RightInterpolation_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolation_one

/--
info: 'SpinGlass.Targets.section5RightInterpolation_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolation_zero_le

/--
info: 'SpinGlass.Targets.section5RightV_zero_eq_two_section4RightT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightV_zero_eq_two_section4RightT

/--
info: 'SpinGlass.Targets.section4RightT_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4RightT_baseline

/--
info: 'SpinGlass.Targets.section5RightV_zero_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightV_zero_baseline

/--
info: 'SpinGlass.Targets.section5RightV_lambda_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightV_lambda_gain

/--
info: 'SpinGlass.Targets.section5RightInterpolation_zero_lambda_gain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolation_zero_lambda_gain

/--
info: 'SpinGlass.Targets.deriv_section4T_variance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_section4T_variance_mem_Icc

/--
info: 'SpinGlass.Targets.section4T_variance_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_variance_dist_le

/--
info: 'SpinGlass.Targets.pairedIndependentMean_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedIndependentMean_sum

/--
info: 'SpinGlass.Targets.constrainedPairDirection_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairDirection_sum

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeDirection_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeDirection_sum

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascade_disorder_dist_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascade_disorder_dist_le

/--
info: 'SpinGlass.Targets.continuous_constrainedPairFieldCascade_disorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_constrainedPairFieldCascade_disorder

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeDirection_radial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeDirection_radial

/--
info: 'SpinGlass.Targets.stein_constrainedPairFieldCascade_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stein_constrainedPairFieldCascade_scaled

/--
info: 'SpinGlass.Targets.measurable_constrainedPairFieldCascade_radial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedPairFieldCascade_radial

/--
info: 'SpinGlass.Targets.integrable_constrainedPairFieldCascade_amplitude' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_constrainedPairFieldCascade_amplitude

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_amplitude' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_amplitude

/--
info: 'SpinGlass.Targets.stein_constrainedPairFieldCascade_radial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stein_constrainedPairFieldCascade_radial

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_amplitude_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_amplitude_trace

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedDisorderPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedDisorderPressure

/--
info: 'SpinGlass.Targets.continuous_constrainedDisorderPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_constrainedDisorderPressure

/--
info: 'SpinGlass.Targets.constrainedLinearStep_paramDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLinearStep_paramDeriv

/--
info: 'SpinGlass.Targets.constrainedLevelVarianceD_base_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLevelVarianceD_base_props

/--
info: 'SpinGlass.Targets.constrainedLevelVarianceD_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLevelVarianceD_props

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_variance

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_variance_deriv_abs_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_variance_deriv_abs_le

/--
info: 'SpinGlass.Targets.constrainedLevelHeatBound_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLevelHeatBound_eq

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_variance_deriv_abs_le_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_variance_deriv_abs_le_explicit

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_variance_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_variance_before

/--
info: 'SpinGlass.Targets.measurable_constrainedLevelVarianceD_disorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedLevelVarianceD_disorder

/--
info: 'SpinGlass.Targets.integrable_constrainedLevelVarianceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_constrainedLevelVarianceD

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_variance

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedDisorderPressure_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedDisorderPressure_variance

/--
info: 'SpinGlass.Targets.affineVariance_pos_or_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.affineVariance_pos_or_eq_zero

/--
info: 'SpinGlass.Targets.section5InterpolationVariance_pos_or_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5InterpolationVariance_pos_or_eq_zero

/--
info: 'SpinGlass.Targets.section5RightInterpolationVariance_pos_or_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightInterpolationVariance_pos_or_eq_zero

/--
info: 'SpinGlass.Targets.section5RightCorrection_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightCorrection_eq

/--
info: 'SpinGlass.Targets.section5RightCorrection_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5RightCorrection_baseline

/--
info: 'SpinGlass.Targets.hasDerivAt_right_split_parisiF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_right_split_parisiF

/--
info: 'SpinGlass.Targets.hasDerivAt_section4RightCascade_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4RightCascade_split

/--
info: 'SpinGlass.Targets.antitoneOn_section4RightT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.antitoneOn_section4RightT

/--
info: 'SpinGlass.Targets.continuousOn_section4RightT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4RightT

/--
info: 'SpinGlass.Targets.section4RightT_zero_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4RightT_zero_variance

/--
info: 'SpinGlass.Targets.section4RightT_le_parisiF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4RightT_le_parisiF

/--
info: 'SpinGlass.Targets.stepK_mono_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stepK_mono_variance

/--
info: 'SpinGlass.Targets.measurable_constrainedLevelVarianceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedLevelVarianceD

/--
info: 'SpinGlass.Targets.constrainedDisorderPressure_variance_deriv_abs_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedDisorderPressure_variance_deriv_abs_le

/--
info: 'SpinGlass.Targets.measurable_deriv_parisiStep_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_deriv_parisiStep_mass

/--
info: 'SpinGlass.Targets.abs_tilted_self_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_tilted_self_sub_le

/--
info: 'SpinGlass.Targets.abs_deriv_parisiStep_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_deriv_parisiStep_mass_le

/--
info: 'SpinGlass.Targets.parisiStep_neg_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_neg_input

/--
info: 'SpinGlass.Targets.abs_parisiStep_mass_sub_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_parisiStep_mass_sub_zero_le

/--
info: 'SpinGlass.Targets.hasDerivAt_integral_of_anchored_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_integral_of_anchored_bound

/--
info: 'SpinGlass.Targets.hasDerivAt_mass_zero_outer_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_mass_zero_outer_expectation

/--
info: 'SpinGlass.Targets.section4MassD_base_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4MassD_base_props

/--
info: 'SpinGlass.Targets.section4MassD_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4MassD_props

/--
info: 'SpinGlass.Targets.hasDerivAt_section4T_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4T_mass_pos

/--
info: 'SpinGlass.Targets.section4T_of_zero_baseline_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_of_zero_baseline_mass

/--
info: 'SpinGlass.Targets.hasDerivAt_section4T_mass_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4T_mass_zero

/--
info: 'SpinGlass.Targets.differentiableAt_section4T_mass_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_section4T_mass_baseline

/--
info: 'SpinGlass.Targets.hasDerivAt_section4T_mass_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4T_mass_baseline

/--
info: 'SpinGlass.Targets.section4U_zero_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_zero_baseline

/--
info: 'SpinGlass.Targets.section4U_zero_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_zero_variance

/--
info: 'SpinGlass.Targets.hasDerivAt_section4Phi_mass_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4Phi_mass_baseline

/--
info: 'SpinGlass.Targets.section4FirstVariation_at_upper_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4FirstVariation_at_upper_overlap

/--
info: 'SpinGlass.Targets.continuousOn_parisiStepPi_param' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_parisiStepPi_param

/--
info: 'SpinGlass.Targets.CoupledContinuousOn.growth_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledContinuousOn.growth_at

/--
info: 'SpinGlass.Targets.CoupledContinuousOn.linearStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledContinuousOn.linearStep

/--
info: 'SpinGlass.Targets.CoupledContinuousOn.fieldCascade' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledContinuousOn.fieldCascade

/--
info: 'SpinGlass.Targets.hasDerivAt_sqrt_affineVariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_sqrt_affineVariance

/--
info: 'SpinGlass.Targets.hasDerivAt_sqrt_mul_time' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_sqrt_mul_time

/--
info: 'SpinGlass.Targets.hasDerivAt_section5InterpolationVariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5InterpolationVariance

/--
info: 'SpinGlass.Targets.hasDerivAt_section5InterpolationAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5InterpolationAmplitude

/--
info: 'SpinGlass.Targets.hasDerivAt_section5RightInterpolationVariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5RightInterpolationVariance

/--
info: 'SpinGlass.Targets.hasDerivAt_section5RightInterpolationAmplitude' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5RightInterpolationAmplitude

/--
info: 'SpinGlass.Targets.continuousOn_constrainedPairFieldBase_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_constrainedPairFieldBase_paths

/--
info: 'SpinGlass.Targets.coupledContinuousOn_constrainedPairFieldBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledContinuousOn_constrainedPairFieldBase

/--
info: 'SpinGlass.Targets.coupledContinuousOn_constrainedPairFieldCascade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledContinuousOn_constrainedPairFieldCascade

/--
info: 'SpinGlass.Targets.continuousOn_constrainedPairFieldCascade_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_constrainedPairFieldCascade_paths

/--
info: 'SpinGlass.Targets.continuousOn_constrainedPairGaussian_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_constrainedPairGaussian_path

/--
info: 'SpinGlass.Targets.continuousOn_section5Interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section5Interpolation

/--
info: 'SpinGlass.Targets.continuousOn_section5RightInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section5RightInterpolation

/--
info: 'SpinGlass.Targets.section4U_sub_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_sub_mem_Icc

/--
info: 'SpinGlass.Targets.monotoneOn_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.monotoneOn_section4U

/--
info: 'SpinGlass.Targets.section4U_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_dist_le

/--
info: 'SpinGlass.Targets.lipschitzOnWith_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.lipschitzOnWith_section4U

/--
info: 'SpinGlass.Targets.continuousOn_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4U

/--
info: 'SpinGlass.Targets.section4U_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_mem_Icc

/--
info: 'SpinGlass.Targets.section4FirstVariation_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4FirstVariation_dist_le

/--
info: 'SpinGlass.Targets.continuousOn_section4FirstVariation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4FirstVariation

/--
info: 'SpinGlass.Targets.abs_section4FirstVariation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_section4FirstVariation_le

/--
info: 'SpinGlass.Targets.section4RightVarianceD_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4RightVarianceD_props

/--
info: 'SpinGlass.Targets.hasDerivAt_section4RightT_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4RightT_variance

/--
info: 'SpinGlass.Targets.abs_deriv_section4RightT_variance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_deriv_section4RightT_variance_le

/--
info: 'SpinGlass.Targets.deriv_section4RightT_variance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_section4RightT_variance_mem_Icc

/--
info: 'SpinGlass.Targets.section4RightT_variance_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4RightT_variance_dist_le

/--
info: 'SpinGlass.Targets.section4VarianceD_eq_massGap_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceD_eq_massGap_mul

/--
info: 'SpinGlass.Targets.measurable_section4VarianceQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_section4VarianceQ

/--
info: 'SpinGlass.Targets.section4VarianceQ_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceQ_mem_Icc

/--
info: 'SpinGlass.Targets.section4TVarianceD_eq_massGap_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4TVarianceD_eq_massGap_mul

/--
info: 'SpinGlass.Targets.section4TVarianceQ_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4TVarianceQ_mem_Icc

/--
info: 'SpinGlass.Targets.hasDerivAt_section4T_variance_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4T_variance_factor

/--
info: 'SpinGlass.Targets.intervalIntegrable_section4T_variance_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.intervalIntegrable_section4T_variance_factor

/--
info: 'SpinGlass.Targets.section4T_sub_eq_massGap_mul_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_sub_eq_massGap_mul_integral

/--
info: 'SpinGlass.Targets.intervalIntegrable_section4TVarianceQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.intervalIntegrable_section4TVarianceQ

/--
info: 'SpinGlass.Targets.contDiff_constrainedPairFieldBase_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.contDiff_constrainedPairFieldBase_joint

/--
info: 'SpinGlass.Targets.differentiableAt_constrainedPairFieldBase_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_constrainedPairFieldBase_joint

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_variances_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_variances_dist_le

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_path_anchored_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_path_anchored_bound

/--
info: 'SpinGlass.Targets.hasFDerivAt_gaussianLogLaplace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasFDerivAt_gaussianLogLaplace

/--
info: 'SpinGlass.Targets.hasFDerivAt_jointGaussianStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasFDerivAt_jointGaussianStep

/--
info: 'SpinGlass.Targets.differentiableAt_constrainedFieldCascade_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_constrainedFieldCascade_joint

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_fderiv

/--
info: 'SpinGlass.Targets.hasFDerivAt_constrainedFieldCascade_joint_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasFDerivAt_constrainedFieldCascade_joint_succ

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_succ

/--
info: 'SpinGlass.Targets.differentiableAt_section5Interpolation_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_section5Interpolation_joint

/--
info: 'SpinGlass.Targets.differentiableAt_section5Interpolation_integrand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_section5Interpolation_integrand

/--
info: 'SpinGlass.Targets.differentiableAt_section5RightInterpolation_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_section5RightInterpolation_joint

/--
info: 'SpinGlass.Targets.differentiableAt_section5RightInterpolation_integrand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_section5RightInterpolation_integrand

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_amplitude_path_anchored_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_amplitude_path_anchored_bound

/--
info: 'SpinGlass.Targets.measurable_constrainedFieldCascadePathD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedFieldCascadePathD

/--
info: 'SpinGlass.Targets.constrainedPairGaussian_path_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairGaussian_path_derivative

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_path

/--
info: 'SpinGlass.Targets.hasDerivAt_section5Interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5Interpolation

/--
info: 'SpinGlass.Targets.differentiableOn_section5Interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableOn_section5Interpolation

/--
info: 'SpinGlass.Targets.hasDerivAt_section5RightInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5RightInterpolation

/--
info: 'SpinGlass.Targets.differentiableOn_section5RightInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableOn_section5RightInterpolation

/--
info: 'SpinGlass.Targets.continuous_gaussian_weighted_exp_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_gaussian_weighted_exp_joint

/--
info: 'SpinGlass.Targets.continuous_tiltE_mass_variance_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_tiltE_mass_variance_spatial

/--
info: 'SpinGlass.Targets.continuous_stepD1_mass_variance_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_stepD1_mass_variance_spatial

/--
info: 'SpinGlass.Targets.continuousOn_parisiStep_parisiF_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_parisiStep_parisiF_joint

/--
info: 'SpinGlass.Targets.continuousOn_stepD1_parisiF_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_stepD1_parisiF_joint

/--
info: 'SpinGlass.Targets.continuousOn_normalized_gaussianMean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_normalized_gaussianMean

/--
info: 'SpinGlass.Targets.continuousOn_pairedSecondMean_paths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_pairedSecondMean_paths

/--
info: 'SpinGlass.Targets.CoupledContinuousOn.scalarStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.CoupledContinuousOn.scalarStep

/--
info: 'SpinGlass.Targets.section4VarianceQ_continuous_paths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceQ_continuous_paths

/--
info: 'SpinGlass.Targets.continuousOn_section4TVarianceQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4TVarianceQ

/--
info: 'SpinGlass.Targets.continuousOn_section4TVarianceQ_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4TVarianceQ_mass

/--
info: 'SpinGlass.Targets.continuousOn_section4TVarianceQ_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_section4TVarianceQ_variance

/--
info: 'SpinGlass.Targets.intervalIntegrable_section4TVarianceQ_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.intervalIntegrable_section4TVarianceQ_closed

/--
info: 'SpinGlass.Targets.continuousOn_integral_section4TVarianceQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_integral_section4TVarianceQ

/--
info: 'SpinGlass.Targets.section4U_sub_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_sub_eq_integral

/--
info: 'SpinGlass.Targets.section4U_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4U_eq_integral

/--
info: 'SpinGlass.Targets.hasDerivAt_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4U

/--
info: 'SpinGlass.Targets.deriv_section4U_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_section4U_mem_Icc

/--
info: 'SpinGlass.Targets.hasDerivAt_section4FirstVariation_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4FirstVariation_overlap

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_multi_anchored_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_multi_anchored_bound

/--
info: 'SpinGlass.Targets.differentiableAt_constrainedFieldCascade_multi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_constrainedFieldCascade_multi

/--
info: 'SpinGlass.Targets.differentiableAt_constrainedFieldCascade_activeFace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.differentiableAt_constrainedFieldCascade_activeFace

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedFieldCascade_path_decomposition

/--
info: 'SpinGlass.Targets.constrainedFieldCascade_path_fderiv_eq_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedFieldCascade_path_fderiv_eq_decomposition

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeDirection_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeDirection_smul

/--
info: 'SpinGlass.Targets.integrable_constrainedPairFieldCascade_radial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_constrainedPairFieldCascade_radial

/--
info: 'SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_path_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_constrainedPairGaussian_path_trace

/--
info: 'SpinGlass.Targets.hasDerivAt_section5Interpolation_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5Interpolation_trace

/--
info: 'SpinGlass.Targets.hasDerivAt_section5RightInterpolation_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5RightInterpolation_trace

/--
info: 'SpinGlass.Targets.constrainedCascadeGibbs_measurable_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeGibbs_measurable_bound

/--
info: 'SpinGlass.Targets.constrainedCascadeGibbs_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeGibbs_nonneg

/--
info: 'SpinGlass.Targets.constrainedCascadeGibbs_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeGibbs_moment

/--
info: 'SpinGlass.Targets.sum_constrainedCascadeGibbs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.sum_constrainedCascadeGibbs

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeDirection_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeDirection_eq_replica

/--
info: 'SpinGlass.Targets.constrainedPairCascadeSpatialFirst_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairCascadeSpatialFirst_eq_replica

/--
info: 'SpinGlass.Targets.constrainedCascadeDirection_SK_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeDirection_SK_square

/--
info: 'SpinGlass.Targets.constrainedCascadeSpatialFirst_independent_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeSpatialFirst_independent_square

/--
info: 'SpinGlass.Targets.constrainedCascadeSpatialFirst_shared_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeSpatialFirst_shared_square

/--
info: 'SpinGlass.Targets.coupledFieldCascade_add_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascade_add_levels

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_measurable_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_measurable_bound

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_nonneg

/--
info: 'SpinGlass.Targets.sum_constrainedCascadeReplica' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.sum_constrainedCascadeReplica

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_moment

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_product_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_product_moment

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_disorder_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_disorder_product

/--
info: 'SpinGlass.Targets.constrainedCascadeReplica_spatial_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedCascadeReplica_spatial_product

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD1_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD1_variance

/--
info: 'SpinGlass.Targets.continuous_gaussian_firstMoment_variance_spatial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuous_gaussian_firstMoment_variance_spatial

/--
info: 'SpinGlass.Targets.continuousOn_stepD1Variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.continuousOn_stepD1Variance

/--
info: 'SpinGlass.Targets.hasFDerivAt_stepD1_variance_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasFDerivAt_stepD1_variance_spatial

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD1_parisiF_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD1_parisiF_variance

/--
info: 'SpinGlass.Targets.stepD1Variance_eq_tilt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.stepD1Variance_eq_tilt

/--
info: 'SpinGlass.Targets.abs_stepD1Variance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_stepD1Variance_le

/--
info: 'SpinGlass.Targets.integrable_stepD1Variance_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_stepD1Variance_gaussian

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD1_parisiF_split_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD1_parisiF_split_sq

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD1_parisiF_variance_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD1_parisiF_variance_curve

/--
info: 'SpinGlass.Targets.abs_stepD1Variance_le_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_stepD1Variance_le_on_Icc

/--
info: 'SpinGlass.Targets.parisiF_raiseMass_zero_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiF_raiseMass_zero_variance

/--
info: 'SpinGlass.Targets.parisiFunctional_raiseMass_zero_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiFunctional_raiseMass_zero_variance

/--
info: 'SpinGlass.Targets.section4Phi_lower_overlap_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_lower_overlap_min

/--
info: 'SpinGlass.Targets.section4FirstVariation_lower_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4FirstVariation_lower_nonneg

/--
info: 'SpinGlass.Targets.hasDerivWithinAt_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivWithinAt_section4U

/--
info: 'SpinGlass.Targets.derivWithin_section4U_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.derivWithin_section4U_eq

/--
info: 'SpinGlass.Targets.hasDerivWithinAt_section4FirstVariation_overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivWithinAt_section4FirstVariation_overlap

/--
info: 'SpinGlass.Targets.splitScalarCascade_independent_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.splitScalarCascade_independent_zero

/--
info: 'SpinGlass.Targets.splitScalarCascadeD_inserted_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.splitScalarCascadeD_inserted_zero

/--
info: 'SpinGlass.Targets.splitScalarCascadeD_shared_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.splitScalarCascadeD_shared_zero

/--
info: 'SpinGlass.Targets.hasDerivAt_section5V_zero_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section5V_zero_Q

/--
info: 'SpinGlass.Targets.deriv_section5V_zero_eq_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv_section5V_zero_eq_Q

/--
info: 'SpinGlass.Targets.talagrand_lemma_5_8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_lemma_5_8

/--
info: 'SpinGlass.Targets.hasDerivWithinAt_section4U_eq_section5V_lambda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivWithinAt_section4U_eq_section5V_lambda

/--
info: 'SpinGlass.Targets.talagrand_lemma_5_8_within' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.talagrand_lemma_5_8_within

/--
info: 'SpinGlass.Targets.section5V_baseline_lambda_gain_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5V_baseline_lambda_gain_Q

/--
info: 'SpinGlass.Targets.section5Interpolation_zero_lambda_gain_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section5Interpolation_zero_lambda_gain_Q

/--
info: 'SpinGlass.Targets.pairedIndependentCovariance_eq_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.pairedIndependentCovariance_eq_mean

/--
info: 'SpinGlass.Targets.coupledOuterMean_cascadeD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledOuterMean_cascadeD

/--
info: 'SpinGlass.Targets.coupledFieldCascadeDD_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascadeDD_expansion

/--
info: 'SpinGlass.Targets.coupledFieldCascadeDD_constrained_replica' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledFieldCascadeDD_constrained_replica

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeSecond_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeSecond_eq_replica

/--
info: 'SpinGlass.Targets.constrainedPairCascadeSpatialSecond_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairCascadeSpatialSecond_eq_replica

/--
info: 'SpinGlass.Targets.constrainedReplicaHessianExpression_mass_telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedReplicaHessianExpression_mass_telescope

/--
info: 'SpinGlass.Targets.constrainedSpatialHeat_eq_replica' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedSpatialHeat_eq_replica

/--
info: 'SpinGlass.Targets.measurable_coupledFieldCascade_disorder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_coupledFieldCascade_disorder

/--
info: 'SpinGlass.Targets.measurable_coupledFieldCascadeD_disorder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_coupledFieldCascadeD_disorder

/--
info: 'SpinGlass.Targets.measurable_constrainedCascadeGibbs_disorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedCascadeGibbs_disorder

/--
info: 'SpinGlass.Targets.measurable_constrainedCascadeReplica_disorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_constrainedCascadeReplica_disorder

/--
info: 'SpinGlass.Targets.integrable_constrainedCascadeReplica' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_constrainedCascadeReplica

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_nonneg

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_moment

/--
info: 'SpinGlass.Targets.sum_averagedConstrainedCascadeReplica' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.sum_averagedConstrainedCascadeReplica

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_disorder_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_disorder_product

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_spatial_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_spatial_product

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_covariance_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_covariance_completion

/--
info: 'SpinGlass.Targets.averagedConstrainedCascadeReplica_defect_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.averagedConstrainedCascadeReplica_defect_nonneg

/--
info: 'SpinGlass.Targets.constrainedReplicaBilinear_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedReplicaBilinear_contraction

/--
info: 'SpinGlass.Targets.integrable_constrainedReplicaMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integrable_constrainedReplicaMoment

/--
info: 'SpinGlass.Targets.integral_constrainedReplicaMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integral_constrainedReplicaMoment

/--
info: 'SpinGlass.Targets.constrainedPairFieldCascadeSecond_SK_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedPairFieldCascadeSecond_SK_trace

/--
info: 'SpinGlass.Targets.integral_constrainedPairFieldCascadeSecond_SK_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integral_constrainedPairFieldCascadeSecond_SK_trace

/--
info: 'SpinGlass.Targets.iteratedDeriv_three_cgf_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.iteratedDeriv_three_cgf_scalar

/--
info: 'SpinGlass.Targets.massGaussianMomentBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.massGaussianMomentBound_nonneg

/--
info: 'SpinGlass.Targets.abs_centered_tilt_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_centered_tilt_moment_le

/--
info: 'SpinGlass.Targets.parisiMassFirstBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiMassFirstBound_nonneg

/--
info: 'SpinGlass.Targets.parisiMassSecondBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiMassSecondBound_nonneg

/--
info: 'SpinGlass.Targets.parisiStep_mass_derivatives_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_mass_derivatives_uniform

/--
info: 'SpinGlass.Targets.parisiStep_parisiF_mass_derivatives_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_parisiF_mass_derivatives_uniform

/--
info: 'SpinGlass.Targets.measurable_section4MassD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.measurable_section4MassD

/--
info: 'SpinGlass.Targets.section4MassD_abs_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4MassD_abs_le_uniform

/--
info: 'SpinGlass.Targets.section4T_mass_derivative_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4T_mass_derivative_uniform

/--
info: 'SpinGlass.Targets.abs_deriv_section4T_mass_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_deriv_section4T_mass_le_uniform

/--
info: 'SpinGlass.Targets.section4Phi_mass_derivative_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4Phi_mass_derivative_uniform

/--
info: 'SpinGlass.Targets.abs_deriv_section4Phi_mass_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_deriv_section4Phi_mass_le_uniform

/--
info: 'SpinGlass.Targets.hasDerivAt_integral_stepD1_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_integral_stepD1_variance

/--
info: 'SpinGlass.Targets.parisiStep_heatVelocity_sub_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.parisiStep_heatVelocity_sub_eq_integral

/--
info: 'SpinGlass.Targets.hasDerivAt_parisiStep_heatVelocity_spatial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_parisiStep_heatVelocity_spatial

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD2_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD2_spatial

/--
info: 'SpinGlass.Targets.abs_stepD3_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.abs_stepD3_le

/--
info: 'SpinGlass.Targets.hasDerivAt_stepD2_parisiF_spatial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_stepD2_parisiF_spatial

/--
info: 'SpinGlass.Targets.splitBaselineWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.splitBaselineWeight_eq

/--
info: 'SpinGlass.Targets.integral_gaussian_mul_tilted_observable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.integral_gaussian_mul_tilted_observable

/--
info: 'SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ_before_ibp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ_before_ibp

/--
info: 'SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ

/--
info: 'SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ_parisiF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_splitBaselineSlopeQ_parisiF

/--
info: 'SpinGlass.Targets.section4VarianceR_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceR_mem_Icc

/--
info: 'SpinGlass.Targets.section4VarianceQ_baseline_deriv_props' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4VarianceQ_baseline_deriv_props

/--
info: 'SpinGlass.Targets.section4THessianSquare_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.section4THessianSquare_mem_Icc

/--
info: 'SpinGlass.Targets.hasDerivAt_section4TVarianceQ_baseline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_section4TVarianceQ_baseline

/--
info: 'SpinGlass.Targets.hasDerivAt_deriv_section4U' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.hasDerivAt_deriv_section4U

/--
info: 'SpinGlass.Targets.deriv2_section4U_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.deriv2_section4U_mem_Icc

/--
info: 'SpinGlass.Targets.coupledOuterMean_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledOuterMean_comp

/--
info: 'SpinGlass.Targets.coupledOuterMean_replicaBilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledOuterMean_replicaBilinear

/--
info: 'SpinGlass.Targets.coupledOuterMean_replicaHessian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledOuterMean_replicaHessian

/--
info: 'SpinGlass.Targets.coupledOuterMean_constrainedSpatialHeat_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledOuterMean_constrainedSpatialHeat_eq_replica

/--
info: 'SpinGlass.Targets.coupledLinearMean_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledLinearMean_independent

/--
info: 'SpinGlass.Targets.coupledLinearMean_shared' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.coupledLinearMean_shared

/--
info: 'SpinGlass.Targets.constrainedLevelVarianceD_independent_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLevelVarianceD_independent_eq_replica

/--
info: 'SpinGlass.Targets.constrainedLevelVarianceD_shared_eq_replica' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SpinGlass.Targets.constrainedLevelVarianceD_shared_eq_replica
