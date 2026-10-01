/-
# Constructed signed time preserves the ORIGINAL maximal derivative graph

Actual positive-real Cayley time commutes with the same positive resolvent.
Injectivity transports that equality to its computed inverse and hence to
signed time. The ORIGINAL unit resolvent then constructs the graph image from
G_t(input+output); its two inverse laws pin BOTH new graph components.

This removes an assumed domain-invariance premise on EVERY original maximal
graph class. It does not yet prove that the signed infinitesimal generator is
-2i times the derivative beyond the existing second core. Nome and width are
fixed; physical spacing/scaling, survival, mass and continuum QFT remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue)
open YMGap.Continuum.SignedRealTimeData (SignedTimeValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output input_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolventDomain input_resolventDomain graph_sum inverse_left shifted)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation (pairResolvent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit
  (positiveRealAction_pairResolvent_commute)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
  (positiveRealAction_injective)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
  (inverseRealAction positiveRealAction_inverse_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction pairAction signedAction_add_state signedAction_addTime
    signedAction_zero signedAction_neg_left)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_smul bondValue_add)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedNeg)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_one completedAdd_assoc completedNeg_add completedZero_add)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "J" => pairResolvent hw0 hw1
local notation "G" => signedAction hw0 hw1

theorem inverseRealAction_pairResolvent_commute (s : Q') (hs : (0 : Q') < s)
    (time : PositiveTimeValue) (x : H) :
    inverseRealAction hw0 hw1 time (J s hs x) =
      J s hs (inverseRealAction hw0 hw1 time x) := by
  apply positiveRealAction_injective hw0 hw1 time
  rw [positiveRealAction_inverse_right,positiveRealAction_pairResolvent_commute,
    positiveRealAction_inverse_right]

/-- The ACTUAL signed group commutes with every original positive resolvent. -/
theorem signedAction_pairResolvent_commute (s : Q') (hs : (0 : Q') < s)
    (time : SignedTimeValue) (x : H) :
    G time (J s hs x) = J s hs (G time x) := by
  refine Quotient.inductionOn time ?_
  intro p
  change pairAction hw0 hw1 p (J s hs x) = J s hs (pairAction hw0 hw1 p x)
  rw [pairAction,inverseRealAction_pairResolvent_commute,
    positiveRealAction_pairResolvent_commute]
  rfl

private def onePos : (0 : Q') < 1 := by decide

private theorem real_scale_one
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 1 x = x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,completedSmul_one]

private def unitDomain (x : H) : D :=
  (resolventDomain hw0 hw1 1 onePos x.1,
   resolventDomain hw0 hw1 1 onePos x.2)

private theorem unitDomain_graph_sum (x : H) :
    A (In (unitDomain hw0 hw1 x)) (Out (unitDomain hw0 hw1 x)) = x := by
  apply Prod.ext
  · have h := graph_sum hw0 hw1 1 onePos x.1
    rw [real_scale_one] at h
    exact h
  · have h := graph_sum hw0 hw1 1 onePos x.2
    rw [real_scale_one] at h
    exact h

private theorem unit_resolvent_graph_sum (d : D) :
    J 1 onePos (A (In d) (Out d)) = In d := by
  apply Prod.ext
  · have h := congrArg (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1)
      (inverse_left hw0 hw1 1 onePos d.1)
    rw [input_resolventDomain,shifted,real_scale_one] at h
    exact h
  · have h := congrArg (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1)
      (inverse_left hw0 hw1 1 onePos d.2)
    rw [input_resolventDomain,shifted,real_scale_one] at h
    exact h

/-- A domain witness, not merely an assertion that some graph output exists. -/
def signedGraphMap (time : SignedTimeValue) (d : D) : D :=
  unitDomain hw0 hw1 (G time (A (In d) (Out d)))

theorem signedGraphMap_input (time : SignedTimeValue) (d : D) :
    In (signedGraphMap hw0 hw1 time d) = G time (In d) := by
  change J 1 onePos (G time (A (In d) (Out d))) = G time (In d)
  rw [← signedAction_pairResolvent_commute,unit_resolvent_graph_sum]

private theorem add_left_cancel (a b c : H) (h : A a b = A a c) : b = c := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    have hv := congrArg (fun z : H => bondValue hw0 hw1 z.1) h
    simp only [BF4WilsonAllNomeComplexBondOSTime.add,bondValue_add] at hv
    have hc := congrArg (completedAdd hw0 hw1 (completedNeg hw0 hw1
      (bondValue hw0 hw1 a.1))) hv
    rw [← completedAdd_assoc,← completedAdd_assoc,completedNeg_add,
      completedZero_add,completedZero_add] at hc
    exact hc
  · apply bondValue_injective hw0 hw1
    have hv := congrArg (fun z : H => bondValue hw0 hw1 z.2) h
    simp only [BF4WilsonAllNomeComplexBondOSTime.add,bondValue_add] at hv
    have hc := congrArg (completedAdd hw0 hw1 (completedNeg hw0 hw1
      (bondValue hw0 hw1 a.2))) hv
    rw [← completedAdd_assoc,← completedAdd_assoc,completedNeg_add,
      completedZero_add,completedZero_add] at hc
    exact hc

/-- Both graph pins use the same constructed witness on the maximal domain. -/
theorem signedGraphMap_output (time : SignedTimeValue) (d : D) :
    Out (signedGraphMap hw0 hw1 time d) = G time (Out d) := by
  apply add_left_cancel hw0 hw1 (G time (In d))
  have h := unitDomain_graph_sum hw0 hw1 (G time (A (In d) (Out d)))
  change A (In (signedGraphMap hw0 hw1 time d))
    (Out (signedGraphMap hw0 hw1 time d)) = G time (A (In d) (Out d)) at h
  rw [signedGraphMap_input,signedAction_add_state] at h
  exact h

/-- Original domain quotients inherit actual signed composition without choice. -/
theorem signedGraphMap_addTime (s t : SignedTimeValue) (d : D) :
    signedGraphMap hw0 hw1 (SignedRealTimeData.addTime s t) d =
      signedGraphMap hw0 hw1 s (signedGraphMap hw0 hw1 t d) := by
  apply input_injective hw0 hw1
  rw [signedGraphMap_input,signedGraphMap_input,signedGraphMap_input,
    signedAction_addTime]

theorem signedGraphMap_zero (d : D) :
    signedGraphMap hw0 hw1 SignedRealTimeData.zeroTime d = d := by
  apply input_injective hw0 hw1
  rw [signedGraphMap_input,signedAction_zero]

theorem signedGraphMap_neg_left (time : SignedTimeValue) (d : D) :
    signedGraphMap hw0 hw1 (SignedRealTimeData.negTime time)
      (signedGraphMap hw0 hw1 time d) = d := by
  apply input_injective hw0 hw1
  rw [signedGraphMap_input,signedGraphMap_input,signedAction_neg_left]

#print axioms inverseRealAction_pairResolvent_commute
#print axioms signedAction_pairResolvent_commute
#print axioms signedGraphMap
#print axioms signedGraphMap_input
#print axioms signedGraphMap_output
#print axioms signedGraphMap_addTime
#print axioms signedGraphMap_zero
#print axioms signedGraphMap_neg_left

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph
