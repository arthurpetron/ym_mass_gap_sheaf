/-
# One-ended influence bound from right-only original residuals

This is the one-ended consumer for the original-source parallel allocator.
It replaces the switched path-safe exceptional premise by two finite,
checkable properties: the original left residual is empty, and the original
right residual mask distinguishes exceptional source entries.  The
nonexceptional branch and the public one-ended quantities are unchanged.
-/

import YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
import YMGap.Continuum.XiNonexceptionalSummation

namespace YMGap.Continuum.XiOneEndedRightOnlyResidualBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiOneEndedInfluence
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalSourcePartition
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiNonexceptionalSummation

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- The complete restriction-product bound using the original-source
right-only residual exceptional consumer. -/
theorem restriction_product_le_opposite_add_carrier_of_rightOnlyResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b1 b2 →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = [])
    (hresidualInjective : ∀ a,
      a ∈ fullExceptionalSource Gamma qP b1 b2 → ∀ b,
      b ∈ fullExceptionalSource Gamma qP b1 b2 →
      rightPathResidual Gamma qP b1 b2 a =
        rightPathResidual Gamma qP b1 b2 b → a = b) :
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
    exact full_exceptional_source_le_chain_mul_XiR_of_rightOnlyResidual
      hw Gamma qP b1 b2 label hleftEmpty hresidualInjective
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

/-- Public one-ended inequality with the original residual consumer spliced
into the exceptional branch. -/
theorem oneEndedLeft_le_right_add_influence_of_rightOnlyResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b : Polymer L → Bool) (head : Polymer L)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b
        (fun X => !(compatibleB head X)) →
      selectByBits Gamma
        (leftPathResidual Gamma qP b
          (fun X => !(compatibleB head X)) entry) = [])
    (hresidualInjective : ∀ a,
      a ∈ fullExceptionalSource Gamma qP b
        (fun X => !(compatibleB head X)) → ∀ c,
      c ∈ fullExceptionalSource Gamma qP b
        (fun X => !(compatibleB head X)) →
      rightPathResidual Gamma qP b
          (fun X => !(compatibleB head X)) a =
        rightPathResidual Gamma qP b
          (fun X => !(compatibleB head X)) c → a = c) :
    oneEndedLeft w qP b head Gamma label ≤
      oneEndedRight w qP b head Gamma label +
        oneEndedInfluenceCarrier w qP b head Gamma label *
          XiR w qP Gamma label := by
  have hbound :=
    restriction_product_le_opposite_add_carrier_of_rightOnlyResidual
      hw Gamma qP b (fun X => !(compatibleB head X)) label
      hleftEmpty hresidualInjective
  unfold oneEndedLeft oneEndedRight restrictionPair
    oneEndedInfluenceCarrier
  rw [← source_second_predicate_eq qP head]
  rw [← opposite_first_predicate_eq qP b head]
  rw [← opposite_second_predicate_eq qP]
  exact hbound

#print axioms restriction_product_le_opposite_add_carrier_of_rightOnlyResidual
#print axioms oneEndedLeft_le_right_add_influence_of_rightOnlyResidual

end YMGap.Continuum.XiOneEndedRightOnlyResidualBound
