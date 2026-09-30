/-
# The derivative equation from convergence of actual dyadic state quotients

The state quotients use the original root defects on the same completion.
Their actual T(1)-images are the finite derivative quotients. Thus a supplied
completed-distance limit for these states gives the derivative equation by
the existing represented-limit uniqueness theorem and transfer contraction.
This is an equation criterion; it does not supply a second coordinate or a
range-closure theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows
import YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect time_defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (differenceQuotient derivativeAction derivativeAction_pin quotientRows quotientRows_pin)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedTime_smul)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The normalized actual defect at a dyadic depth, without a preliminary
positive-time image. -/
def stateQuotient (depth : Nat) (u : V) : V :=
  completedSmul hw0 hw1 (Q'.ofNat (2^depth)) (defect hw0 hw1 depth u)

/-- Applying the original one-step transfer to the actual state quotient
recovers exactly the finite derivative quotient. -/
theorem time_stateQuotient (depth : Nat) (u : V) :
    T 1 (stateQuotient hw0 hw1 depth u) =
      differenceQuotient hw0 hw1 depth u := by
  have hcomm := time_defect hw0 hw1 0 1 depth u
  rw [mesh_original hw0 hw1 1, mesh_original hw0 hw1 1] at hcomm
  unfold stateQuotient differenceQuotient
  rw [completedTime_smul, hcomm]

/-- A same-carrier limit of the actual normalized state quotients solves the
original derivative equation after one application of T(1). -/
theorem derivative_equation_of_quotient_limit
    (u v : V) (modulus : Q' → Nat)
    (bound : ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ k,
      modulus epsilon ≤ k →
      RCle (d (stateQuotient hw0 hw1 k u) v) (rat epsilon)) :
    derivativeAction hw0 hw1 u = T 1 v := by
  revert bound
  refine Quotient.inductionOn u ?_
  intro X bound
  rw [derivativeAction_pin]
  apply limit_unique hw0 hw1 (quotientRows hw0 hw1 X) (T 1 v) modulus
  intro epsilon hepsilon k hk
  rw [quotientRows_pin]
  have hstate := bound epsilon hepsilon k hk
  have hcontract := completedDist_time hw0 hw1 1
    (stateQuotient hw0 hw1 k (Class X)) v
  rw [time_stateQuotient] at hcontract
  exact RCle_trans hcontract hstate

#print axioms stateQuotient
#print axioms time_stateQuotient
#print axioms derivative_equation_of_quotient_limit

end YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
