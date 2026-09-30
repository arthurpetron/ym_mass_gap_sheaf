/-
The constructed original dyadic derivative belongs to the closure of the
original positive-time range. Every finite quotient row is exactly T(1) of
an explicit Cauchy preimage. The preimages need neither converge nor obey a
uniform norm bound; the existing closure modulus uses one computed row.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedTime_smul)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect time_defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives (rootRepresentative rootRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
  (closureModulus closure_smallTime closureContinuityCertificate)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The unsmoothed difference quotient has a supplied original representative. -/
def preimageRepresentative (depth : Nat) (X : (PD).Cauchy) : (PD).Cauchy :=
  (scalarContinuous hw0 hw1 (Q'.ofNat (2^depth))).mapCauchy
    (differenceCauchy hw0 hw1 X (rootRepresentative hw0 hw1 depth X))

theorem preimageRepresentative_pin (depth : Nat) (X : (PD).Cauchy) :
    Class (preimageRepresentative hw0 hw1 depth X) =
      completedSmul hw0 hw1 (Q'.ofNat (2^depth))
        (defect hw0 hw1 depth (Class X)) := by
  change completedSmul hw0 hw1 (Q'.ofNat (2^depth))
    (completedSub hw0 hw1 (Class X) (Class (rootRepresentative hw0 hw1 depth X))) = _
  rw [rootRepresentative_pin]
  rfl

/-- Every quotient row is an actual original T(1)-image, not merely a
limit point with an unprovided existential preimage. -/
theorem quotient_time_image (depth : Nat) (X : (PD).Cauchy) :
    T 1 (Class (preimageRepresentative hw0 hw1 depth X)) =
      differenceQuotient hw0 hw1 depth (Class X) := by
  rw [preimageRepresentative_pin,completedTime_smul]
  have h := time_defect hw0 hw1 0 1 depth (Class X)
  rw [mesh_original hw0 hw1 1,mesh_original hw0 hw1 1] at h
  rw [h]
  rfl

theorem quotientRows_time_image (X : (PD).Cauchy) (depth : Nat) :
    rowPoint hw0 hw1 (quotientRows hw0 hw1 X) depth =
      T 1 (Class (preimageRepresentative hw0 hw1 depth X)) := by
  rw [quotientRows_pin]
  exact (quotient_time_image hw0 hw1 depth X).symm

/-- A computed depth threshold for all sufficiently small dyadic increments
of this SAME derivative output. The sampled preimage depends on epsilon. -/
def derivativeContinuityModulus (X : (PD).Cauchy) (epsilon : Q') : Nat :=
  closureModulus hw0 hw1 (quotientRows hw0 hw1 X)
    (fun depth => preimageRepresentative hw0 hw1 depth X) epsilon

theorem derivative_smallTime (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (depth steps : Nat)
    (hsmall : steps*2^(derivativeContinuityModulus hw0 hw1 X epsilon) ≤ 2^depth) :
    RCle (dist (BF4WilsonAllNomeDyadicSemigroup.meshAction hw0 hw1 depth steps
        (derivativeAction hw0 hw1 (Class X)))
      (derivativeAction hw0 hw1 (Class X))) (rat epsilon) := by
  rw [derivativeAction_pin]
  exact closure_smallTime hw0 hw1 (quotientRows hw0 hw1 X)
    (fun n => preimageRepresentative hw0 hw1 n X)
    (quotientRows_time_image hw0 hw1 X) epsilon he depth steps hsmall

def derivativeContinuityCertificate (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps*2^k ≤ 2^depth →
      RCle (dist (BF4WilsonAllNomeDyadicSemigroup.meshAction hw0 hw1 depth steps
          (derivativeAction hw0 hw1 (Class X)))
        (derivativeAction hw0 hw1 (Class X))) (rat epsilon)} :=
  ⟨derivativeContinuityModulus hw0 hw1 X epsilon,
    derivative_smallTime hw0 hw1 X epsilon he⟩

/-- The derivative output depends only on the original T(1)-image. This is
not injectivity of T(1) and does not remove its boundary kernel. -/
theorem derivativeAction_time_congr (x y : V)
    (h : T 1 x = T 1 y) :
    derivativeAction hw0 hw1 x = derivativeAction hw0 hw1 y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y hxy
  rw [derivativeAction_pin,derivativeAction_pin]
  apply limit_independent hw0 hw1
  intro n
  rw [quotientRows_pin,quotientRows_pin]
  unfold differenceQuotient
  rw [hxy]

#print axioms preimageRepresentative
#print axioms preimageRepresentative_pin
#print axioms quotient_time_image
#print axioms quotientRows_time_image
#print axioms derivativeContinuityModulus
#print axioms derivative_smallTime
#print axioms derivativeContinuityCertificate
#print axioms derivativeAction_time_congr

end YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
