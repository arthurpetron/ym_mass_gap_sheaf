/-
# Supplied Cauchy representatives of the original Chebyshev words

Every operation here consumes an explicitly supplied original full-action
Cauchy representative and retains the moduli of the existing representative
constructors. The quotient pins identify the SAME completed conditional
sweep, affine rescaling and coupled recurrence. No representative is chosen
from an arbitrary quotient, and no reverse-energy estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSweepChebyshev
import YMGap.Continuum.BF4ExactSlabStarConditionalProjection
import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum.BF4ExactSlabChebyshevRepresentative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.GNSChebyshevEnergy
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

private def classOf (X : CauchyGNS F) : GNSCompletionSpace F :=
  Quotient.mk (cauchySetoid F) X

private theorem classOf_add (X Y : CauchyGNS F) :
    classOf hw0 hw1 K extent hK ((F).cAddCauchy X Y) =
      (F).cAdd (classOf hw0 hw1 K extent hK X)
        (classOf hw0 hw1 K extent hK Y) := rfl

private theorem classOf_sub (X Y : CauchyGNS F) :
    classOf hw0 hw1 K extent hK ((F).subCauchy X Y) =
      (F).cSub (classOf hw0 hw1 K extent hK X)
        (classOf hw0 hw1 K extent hK Y) := rfl

private theorem classOf_smul (c : Q') (X : CauchyGNS F) :
    classOf hw0 hw1 K extent hK ((S).cSmulCauchy c X) =
      (S).cSmul c (classOf hw0 hw1 K extent hK X) := rfl

/-- Apply the original dense conditional representative map at each
physical link in the supplied forward-order word. Its computed modulus is
inherited from `DenseMap.mapRep` at every step. -/
def sweepRep : List (PhysicalLink extent) → CauchyGNS F → CauchyGNS F
  | [], X => X
  | i :: rest, X =>
      sweepRep rest
        ((conditionalDenseMap hw0 hw1 K extent hK i.val i.property).mapRep X)

/-- The representative word descends to exactly the original completed
conditional sweep, including arbitrary finite pruned words. -/
theorem sweepRep_pin (word : List (PhysicalLink extent)) (X : CauchyGNS F) :
    classOf hw0 hw1 K extent hK
      (sweepRep hw0 hw1 K extent hK word X) =
      (P).sweep word (classOf hw0 hw1 K extent hK X) := by
  induction word generalizing X with
  | nil => rfl
  | cons i rest ih =>
      change classOf hw0 hw1 K extent hK
          (sweepRep hw0 hw1 K extent hK rest
            ((conditionalDenseMap hw0 hw1 K extent hK i.val i.property).mapRep X)) =
        (P).sweep rest ((P).op i (classOf hw0 hw1 K extent hK X))
      rw [ih]
      exact congrArg ((P).sweep rest)
        ((conditionalDenseMap hw0 hw1 K extent hK i.val i.property).completionMap_mk X).symm

/-- Literal representative of `c*(S* S)X-X` on the SAME full-action
carrier. The reverse word is the actual list reversal of the physical
schedule; no surrogate color operator is inserted. -/
def affineRep (c : Q') (X : CauchyGNS F) : CauchyGNS F :=
  (F).subCauchy
    ((S).cSmulCauchy c
      (sweepRep hw0 hw1 K extent hK (schedule extent).reverse
        (sweepRep hw0 hw1 K extent hK (schedule extent) X))) X

theorem affineRep_pin (c : Q') (X : CauchyGNS F) :
    classOf hw0 hw1 K extent hK (affineRep hw0 hw1 K extent hK c X) =
      affine hw0 hw1 K extent hK c (classOf hw0 hw1 K extent hK X) := by
  unfold affineRep affine
  rw [classOf_sub, classOf_smul,
    sweepRep_pin hw0 hw1 K extent hK (schedule extent).reverse,
    sweepRep_pin hw0 hw1 K extent hK (schedule extent)]
  rfl

private def classPair (p : CauchyGNS F × CauchyGNS F) :
    GNSCompletionSpace F × GNSCompletionSpace F :=
  (classOf hw0 hw1 K extent hK p.1, classOf hw0 hw1 K extent hK p.2)

private def coupledRepStep (c : Q') (p : CauchyGNS F × CauchyGNS F) :
    CauchyGNS F × CauchyGNS F :=
  let nextAux := (F).cAddCauchy p.1
    (affineRep hw0 hw1 K extent hK c p.2)
  ((F).subCauchy (affineRep hw0 hw1 K extent hK c nextAux) p.2, nextAux)

private theorem coupledRepStep_pin (c : Q') (p : CauchyGNS F × CauchyGNS F) :
    classPair hw0 hw1 K extent hK
      (coupledRepStep hw0 hw1 K extent hK c p) =
      GNSChebyshevEnergy.step (affine hw0 hw1 K extent hK c)
        (classPair hw0 hw1 K extent hK p).1
        (classPair hw0 hw1 K extent hK p).2 := by
  let v := (F).cAddCauchy p.1 (affineRep hw0 hw1 K extent hK c p.2)
  have hv : classOf hw0 hw1 K extent hK v =
      (F).cAdd (classOf hw0 hw1 K extent hK p.1)
        (affine hw0 hw1 K extent hK c
          (classOf hw0 hw1 K extent hK p.2)) := by
    dsimp only [v]
    rw [classOf_add, affineRep_pin]
  calc
    classPair hw0 hw1 K extent hK
        (coupledRepStep hw0 hw1 K extent hK c p) =
      ((F).cSub
        (affine hw0 hw1 K extent hK c (classOf hw0 hw1 K extent hK v))
        (classOf hw0 hw1 K extent hK p.2),
        classOf hw0 hw1 K extent hK v) := by
      change
        (classOf hw0 hw1 K extent hK
            ((F).subCauchy (affineRep hw0 hw1 K extent hK c v) p.2),
          classOf hw0 hw1 K extent hK v) = _
      rw [classOf_sub, affineRep_pin]
    _ = GNSChebyshevEnergy.step (affine hw0 hw1 K extent hK c)
        (classPair hw0 hw1 K extent hK p).1
        (classPair hw0 hw1 K extent hK p).2 := by
      rw [hv]
      rfl

/-- Literal representative-level copy of the coupled first/auxiliary
Chebyshev recurrence. The seed `X` is supplied; the zero seed is the
existing constant Cauchy representative of the original `F.zero`. -/
def coupledRep (c : Q') (X : CauchyGNS F) : Nat → CauchyGNS F × CauchyGNS F
  | 0 => (X, constCauchy F (F).zero)
  | n+1 => coupledRepStep hw0 hw1 K extent hK c (coupledRep c X n)

private theorem coupledRep_pair_pin (c : Q') (X : CauchyGNS F) (n : Nat) :
    classPair hw0 hw1 K extent hK
      (coupledRep hw0 hw1 K extent hK c X n) =
      coupled hw0 hw1 K extent hK c
        (classOf hw0 hw1 K extent hK X) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        classPair hw0 hw1 K extent hK
            (coupledRep hw0 hw1 K extent hK c X (n+1)) =
          GNSChebyshevEnergy.step (affine hw0 hw1 K extent hK c)
            (classPair hw0 hw1 K extent hK
              (coupledRep hw0 hw1 K extent hK c X n)).1
            (classPair hw0 hw1 K extent hK
              (coupledRep hw0 hw1 K extent hK c X n)).2 :=
          coupledRepStep_pin hw0 hw1 K extent hK c _
        _ = GNSChebyshevEnergy.step (affine hw0 hw1 K extent hK c)
            (coupled hw0 hw1 K extent hK c
              (classOf hw0 hw1 K extent hK X) n).1
            (coupled hw0 hw1 K extent hK c
              (classOf hw0 hw1 K extent hK X) n).2 := by rw [ih]
        _ = coupled hw0 hw1 K extent hK c
            (classOf hw0 hw1 K extent hK X) (n+1) := rfl

/-- Both components of the supplied representative recurrence descend to
the literal completed coupled state, not only its Chebyshev first value. -/
theorem coupledRep_pin (c : Q') (X : CauchyGNS F) (n : Nat) :
    classOf hw0 hw1 K extent hK (coupledRep hw0 hw1 K extent hK c X n).1 =
      (coupled hw0 hw1 K extent hK c
        (classOf hw0 hw1 K extent hK X) n).1 ∧
    classOf hw0 hw1 K extent hK (coupledRep hw0 hw1 K extent hK c X n).2 =
      (coupled hw0 hw1 K extent hK c
        (classOf hw0 hw1 K extent hK X) n).2 := by
  have h := coupledRep_pair_pin hw0 hw1 K extent hK c X n
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

#print axioms sweepRep
#print axioms sweepRep_pin
#print axioms affineRep
#print axioms affineRep_pin
#print axioms coupledRep
#print axioms coupledRep_pin

end YMGap.Continuum.BF4ExactSlabChebyshevRepresentative
