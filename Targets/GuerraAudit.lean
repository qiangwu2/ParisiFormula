/-
# Regression checks for the SK Guerra identity and the Theorem 2.2 supporting results

These guards are part of `lake build Targets`. They reject any reintroduced
`sorryAx` or additional axiom in Theorem 2.1, its upper-bound consequences,
Lemma 2.7, the replica-measure decomposition, Lemma 2.6, Proposition 2.5 on
interior times, and the deduction of Theorem 2.2 from an explicit overlap-concentration hypothesis.
The latter guards certify the implication, not its unproved concentration input.
The Lemma 2.6 guards include Gaussian concentration and its change of law to
the abstract disorder, not just a conditional or standard-coordinate estimate.
The Section 5 guards cover both endpoints of the positive-overlap left-interval
second interpolation, including (5.8) and (5.17), but not its covariance
derivative inequality (Theorem 3.1) or Theorem 2.4.
The terminal Hessian and covariance-algebra guards do not identify the
algebraic expression with the derivative of the full nested pressure.
The newer guards cover full-depth disorder and separate-field mixed derivatives,
Gaussian Stein, scalar mass/variance calculus including (4.11), the zero-lambda
baseline, Lemma 5.9, and the optimized time-zero endpoint. Exact equal-mass compression
supplies the original convergence quantifiers from a uniform Theorem 2.4 bound for
strict masses; the guards do not certify that bound.
The full Parisi formula is deliberately not listed: Theorem 2.2 is still open.
-/
import Targets.ReplicaMeasure
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
