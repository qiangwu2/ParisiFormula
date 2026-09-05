/-
# Regression checks for the SK Guerra identity and the Theorem 2.2 supporting results

These guards are part of `lake build Targets`. They reject any reintroduced
`sorryAx` or additional axiom in Theorem 2.1, its upper-bound consequences,
Lemma 2.7, the replica-measure decomposition, the deterministic comparison in
Lemma 2.6, and the deduction of Theorem 2.2 from an explicit overlap-concentration hypothesis.
The latter guards certify the implication, not its unproved concentration input.
The Lemma 2.6 guards do not certify its still-open Gaussian concentration step.
The full Parisi formula is deliberately not listed: Theorem 2.2 is still open.
-/
import Targets.ReplicaMeasure
import Targets.ConstrainedCascade

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
