/-
# Regression checks for the completed SK Guerra identity

These guards are part of `lake build Targets`. They reject any reintroduced
`sorryAx` or additional axiom in Theorem 2.1 and its upper-bound consequences.
The full Parisi formula is deliberately not listed: Theorem 2.2 is still open.
-/
import Targets.Talagrand

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
