/-
# Exact one-ended influence bound from the two source branches

The occurrence-pair source partitions into exceptional and nonexceptional
pairs.  The nonexceptional component switch is unconditional.  The
exceptional path-safe injection supplies the chain-carrier term once its
unchanged finite target-validity package is discharged.  This file composes
the two branches and specializes the Boolean restrictions to the public
one-ended quantities.
-/

import YMGap.Continuum.XiNonexceptionalSummation

namespace YMGap.Continuum.XiOneEndedInfluenceBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiOneEndedInfluence
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalSourcePartition
open YMGap.Continuum.XiNonexceptionalSummation

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

theorem restriction_product_le_opposite_add_carrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hfacts : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b1 b2 →
        PathSafeRoutedFacts Gamma qP b1 b2 entry) :
    XiR w (fun X => qP X && !(b1 X)) Gamma label *
        XiR w (fun X => qP X && !(b2 X)) Gamma label ≤
      XiR w (fun X => qP X && !((fun X => b1 X || b2 X) X))
          Gamma label *
        XiR w (fun X => qP X && !((fun _ : Polymer L => false) X))
          Gamma label +
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  let exceptional := qListSum
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (exceptionalSourceCodes Gamma qP b1 b2)
  let nonexceptional := qListSum
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (nonexceptionalSourceCodes Gamma qP b1 b2)
  let opposite :=
    XiR w (fun X => qP X && !((fun X => b1 X || b2 X) X))
        Gamma label *
      XiR w (fun X => qP X && !((fun _ : Polymer L => false) X))
        Gamma label
  let carrier := connectingChainMajorant w qP b1 b2 Gamma label *
    XiR w qP Gamma label
  have hpartition :=
    restriction_product_eqv_exceptional_add_nonexceptional
      w qP b1 b2 Gamma label
  have hexceptional : exceptional ≤ carrier := by
    exact full_exceptional_source_le_chain_mul_XiR hw Gamma qP b1 b2
      label hfacts
  have hnonexceptional : nonexceptional ≤ opposite := by
    exact nonexceptional_source_le_opposite_product hw Gamma qP b1 b2 label
  have hsum : exceptional + nonexceptional ≤ carrier + opposite :=
    Q'.add_le_add hexceptional hnonexceptional
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition) ?_
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (Q'.add_comm_eqv carrier opposite))

private theorem source_second_predicate_eq
    (qP : Polymer L → Bool) (head : Polymer L) :
    (fun X => qP X && !(!(compatibleB head X))) =
      (fun X => qP X && compatibleB head X) := by
  funext X
  cases qP X <;> cases compatibleB head X <;> rfl

private theorem opposite_first_predicate_eq
    (qP b : Polymer L → Bool) (head : Polymer L) :
    (fun X => qP X && !(b X || !(compatibleB head X))) =
      (fun X => qP X && (!(b X) && compatibleB head X)) := by
  funext X
  cases qP X <;> cases b X <;> cases compatibleB head X <;> rfl

private theorem opposite_second_predicate_eq
    (qP : Polymer L → Bool) :
    (fun X => qP X && !false) = (fun X => qP X && true) := by
  funext X
  cases qP X <;> rfl

theorem oneEndedLeft_le_right_add_influence
    {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b : Polymer L → Bool) (head : Polymer L)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (hfacts : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b
        (fun X => !(compatibleB head X)) →
      PathSafeRoutedFacts Gamma qP b
        (fun X => !(compatibleB head X)) entry) :
    oneEndedLeft w qP b head Gamma label ≤
      oneEndedRight w qP b head Gamma label +
        oneEndedInfluenceCarrier w qP b head Gamma label *
          XiR w qP Gamma label := by
  have hbound := restriction_product_le_opposite_add_carrier hw Gamma qP b
    (fun X => !(compatibleB head X)) label hfacts
  unfold oneEndedLeft oneEndedRight restrictionPair
    oneEndedInfluenceCarrier
  rw [← source_second_predicate_eq qP head]
  rw [← opposite_first_predicate_eq qP b head]
  rw [← opposite_second_predicate_eq qP]
  exact hbound

#print axioms restriction_product_le_opposite_add_carrier
#print axioms oneEndedLeft_le_right_add_influence

end YMGap.Continuum.XiOneEndedInfluenceBound
