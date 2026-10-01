/-
# Finite original-resolvent calculus for a Cayley tangent converse

The componentwise scaled resolvent is the already constructed inverse of the
ORIGINAL positive graph shift.  The identities here retain its actual bond
carrier and provide exactly the finite linear, norm and domain pins needed
to transport a supplied normalized signed-time tangent.  No tangent or
generator converse is asserted in this module.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
import YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedSmul_one)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolvent resolventDomain resolvent_add resolvent_smul resolvent_sub
    graph_sum norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (pairResolvent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (realScale imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "R" => resolvent hw0 hw1
local notation "J" => pairResolvent hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "B" => bondCompletedInner hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1

/-- The unit graph shift uses a concrete positive rational witness. -/
def onePos : (0 : Q') < 1 := by decide

/-- The resolvent acts additively on both actual physical bond components. -/
theorem pairResolvent_add (s : Q') (hs : (0 : Q') < s) (x y : H) :
    J s hs (A x y) = A (J s hs x) (J s hs y) :=
  Prod.ext (resolvent_add hw0 hw1 s hs x.1 y.1)
    (resolvent_add hw0 hw1 s hs x.2 y.2)

/-- Only rational scaling is needed; no arbitrary complex-real scalar
continuity or modulus is postulated. -/
theorem pairResolvent_realScale (s : Q') (hs : (0 : Q') < s)
    (c : Q') (x : H) :
    J s hs (realScale hw0 hw1 c x) =
      realScale hw0 hw1 c (J s hs x) :=
  Prod.ext (resolvent_smul hw0 hw1 s hs c x.1)
    (resolvent_smul hw0 hw1 s hs c x.2)

private theorem negate_smul_minus_one (x : RH) : Neg x = Scale (-1) x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_negate,bondValue_smul]
  rfl

private theorem resolvent_negate (s : Q') (hs : (0 : Q') < s) (x : RH) :
    R s hs (Neg x) = Neg (R s hs x) := by
  calc
    R s hs (Neg x) = R s hs (Scale (-1) x) :=
      congrArg (R s hs) (negate_smul_minus_one hw0 hw1 x)
    _ = Scale (-1) (R s hs x) := resolvent_smul hw0 hw1 s hs (-1) x
    _ = Neg (R s hs x) := (negate_smul_minus_one hw0 hw1 _).symm

/-- The signed imaginary cross term remains in the original physical pair. -/
theorem pairResolvent_imagScale (s : Q') (hs : (0 : Q') < s)
    (c : Q') (x : H) :
    J s hs (imagScale hw0 hw1 c x) =
      imagScale hw0 hw1 c (J s hs x) := by
  apply Prod.ext
  · change R s hs (Neg (Scale c x.2)) = Neg (Scale c (R s hs x.2))
    rw [resolvent_negate, resolvent_smul]
  · change R s hs (Scale c x.1) = Scale c (R s hs x.1)
    rw [resolvent_smul]

/-- The difference quotient transports without changing its source vector. -/
theorem pairResolvent_diff (s : Q') (hs : (0 : Q') < s) (x y : H) :
    J s hs (diff hw0 hw1 x y) =
      diff hw0 hw1 (J s hs x) (J s hs y) := by
  apply Prod.ext
  · change R s hs (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x.1 y.1) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (R s hs x.1) (R s hs y.1)
    exact resolvent_sub hw0 hw1 s hs x.1 y.1
  · change R s hs (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x.2 y.2) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (R s hs x.2) (R s hs y.2)
    exact resolvent_sub hw0 hw1 s hs x.2 y.2

/-- Contractivity is for the SAME original two-component physical norm. -/
theorem normSq_pairResolvent_le (s : Q') (hs : (0 : Q') < s) (x : H) :
    RCle (N (J s hs x)) (N x) := by
  change RCle
    (RCadd (B (R s hs x.1) (R s hs x.1))
      (B (R s hs x.2) (R s hs x.2)))
    (RCadd (B x.1 x.1) (B x.2 x.2))
  exact RCadd_le_add (norm_bound hw0 hw1 s hs x.1)
    (norm_bound hw0 hw1 s hs x.2)

/-- The input is represented by two ORIGINAL scaled-resolvent graph points. -/
def unitDomain (x : H) : D :=
  (resolventDomain hw0 hw1 1 (onePos) x.1,
   resolventDomain hw0 hw1 1 (onePos) x.2)

theorem unitDomain_input (x : H) :
    In (unitDomain hw0 hw1 x) = J 1 (onePos) x := rfl

private theorem real_scale_one (x : RH) : Scale 1 x = x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,completedSmul_one]

/-- The exact original unit-shift graph equation, with no surrogate output. -/
theorem unitDomain_graph_sum (x : H) :
    A (In (unitDomain hw0 hw1 x)) (Out (unitDomain hw0 hw1 x)) = x := by
  apply Prod.ext
  · change Add (R 1 (onePos) x.1)
      (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
        (resolventDomain hw0 hw1 1 (onePos) x.1)) = x.1
    have h := graph_sum hw0 hw1 1 (onePos) x.1
    rw [real_scale_one] at h
    exact h
  · change Add (R 1 (onePos) x.2)
      (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
        (resolventDomain hw0 hw1 1 (onePos) x.2)) = x.2
    have h := graph_sum hw0 hw1 1 (onePos) x.2
    rw [real_scale_one] at h
    exact h

#print axioms onePos
#print axioms pairResolvent_add
#print axioms pairResolvent_realScale
#print axioms pairResolvent_imagScale
#print axioms pairResolvent_diff
#print axioms normSq_pairResolvent_le
#print axioms unitDomain
#print axioms unitDomain_input
#print axioms unitDomain_graph_sum

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventTangent
