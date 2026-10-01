/-
# Density of explicitly represented twice-time-smoothed graph inputs

Every supplied physical bond Rows object retains two original time-range
witnesses. At each tolerance we sample each witness's own preimage, compute
its rational norm ceiling, and choose a finite inverse sum. The resulting
two-step-smoothed states are inputs of the actual second-core graph points.

This is density only in the represented physical bond carrier. In particular
it does not assert that T² has dense range in the ambient completion or that
arbitrary physical derivative outputs remain in the derivative domain.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore
import YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_add)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_symm completedDist_triangle)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange (inverseSum inverseSum_error_pin)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
  (inverseSumRepresentative inverseSumRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (quarter quarter_positive four_quarters representedTailModulus represented_tail_small)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "T" => completedTime hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "RealState" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "Rows" => BF4WilsonAllNomeComplexBondOSCompletion.Rows hw0 hw1 (width := width)
local notation "Domain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)

/-- The tolerance-dependent preimage is DATA supplied by the original
time-range witness, not a choice from the completed quotient. -/
def baseSource (x : RealState) (e : Q') : (D).Cauchy :=
  x.range.preimage (x.range.modulus (quarter e))

/-- The cutoff reads a rational norm ceiling of this very preimage's
original Cauchy witness; it is not a uniform source bound. -/
def correctionDepth (x : RealState) (e : Q') : Nat :=
  representedTailModulus hw0 hw1 (baseSource hw0 hw1 x e) (quarter e)

def approximationSource (x : RealState) (e : Q') : (D).Cauchy :=
  inverseSumRepresentative hw0 hw1 (correctionDepth hw0 hw1 x e)
    (baseSource hw0 hw1 x e)

theorem approximationSource_pin (x : RealState) (e : Q') :
    Class (approximationSource hw0 hw1 x e) =
      inverseSum hw0 hw1 (correctionDepth hw0 hw1 x e)
        (Class (baseSource hw0 hw1 x e)) :=
  inverseSumRepresentative_pin hw0 hw1 _ _

/-- Constructive one-component density with the actual T² input and an
explicit epsilon-dependent original source. -/
theorem approximationSource_bound (x : RealState) (e : Q')
    (he : (0 : Q') < e) :
    RCle (dist (T 1 (T 1 (Class (approximationSource hw0 hw1 x e)))) x.val)
      (rat e) := by
  let delta := quarter e
  let X := baseSource hw0 hw1 x e
  let k := correctionDepth hw0 hw1 x e
  have hd : (0 : Q') < delta := quarter_positive he
  have hnear : RCle (dist (T 1 (Class X)) x.val) (rat delta) :=
    x.range.bound delta hd (x.range.modulus delta) (Nat.le_refl _)
  have htail : RCle (dist (T 1 (Class X))
      (T 2 (inverseSum hw0 hw1 k (Class X)))) (rat delta) := by
    change RCle
      (B (BF4WilsonAllNomeLinear.completedSub hw0 hw1 (T 1 (Class X))
        (T 2 (inverseSum hw0 hw1 k (Class X))))
       (BF4WilsonAllNomeLinear.completedSub hw0 hw1 (T 1 (Class X))
        (T 2 (inverseSum hw0 hw1 k (Class X))))) (rat delta)
    rw [inverseSum_error_pin]
    exact represented_tail_small hw0 hw1 X delta hd k (Nat.le_refl _)
  have hreverse : RCle (dist (T 2 (inverseSum hw0 hw1 k (Class X)))
      (T 1 (Class X))) (rat delta) := by
    rw [completedDist_symm hw0 hw1 (T 2 (inverseSum hw0 hw1 k (Class X)))
      (T 1 (Class X))]
    exact htail
  have htriangle := completedDist_triangle hw0 hw1
    (T 2 (inverseSum hw0 hw1 k (Class X))) (T 1 (Class X)) x.val
  have hbudget := RCle_trans htriangle
    (RCadd_le_add (RCadd_le_add hreverse hreverse) (RCadd_le_add hnear hnear))
  rw [four_quarters] at hbudget
  change RCle (dist (T 2 (inverseSum hw0 hw1 k (Class X))) x.val) (rat e) at hbudget
  simpa only [approximationSource_pin, show (2 : Nat) = 1+1 by decide,
    completedTime_add] using hbudget

/-- Two original representatives at a fixed precision. Each component
returns the explicit preimage and its own norm-ceiling-based cutoff. -/
def pairSources (X : Rows) (n : Nat) : (D).Cauchy × (D).Cauchy :=
  (approximationSource hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.rowState hw0 hw1 X).1
      (HalfPow.half * Q'.invSucc n),
   approximationSource hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.rowState hw0 hw1 X).2
      (HalfPow.half * Q'.invSucc n))

private theorem half_budget (e : Q') :
    RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves e))

/-- The two-step input approximates the SAME physical Rows class at the
explicit inverse-successor precision. -/
theorem pairSources_bound (X : Rows) (n : Nat) :
    RCle
      (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
        (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
          (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1
            (pairSources hw0 hw1 X n)))
        (BF4WilsonAllNomeComplexBondOSCompletion.ofRows hw0 hw1 X))
      (rat (Q'.invSucc n)) := by
  let S := BF4WilsonAllNomeComplexBondOSCompletion.rowState hw0 hw1 X
  have hh : (0 : Q') < HalfPow.half * Q'.invSucc n :=
    ExpNeg.half_mul_pos _ (Q'.invSucc_pos n)
  have h₁ := approximationSource_bound hw0 hw1 S.1 _ hh
  have h₂ := approximationSource_bound hw0 hw1 S.2 _ hh
  have h := RCadd_le_add h₁ h₂
  rw [half_budget] at h
  rw [BF4WilsonAllNomeComplexBondOSCompletion.distance_value,
    BF4WilsonAllNomeComplexBondOSSecondCore.first_input_value,
    BF4WilsonAllNomeComplexBondOSCompletion.value_ofRows]
  change RCle
    (RCadd
      (dist (T 1 (T 1 (Class (pairSources hw0 hw1 X n).1))) S.1.val)
      (dist (T 1 (T 1 (Class (pairSources hw0 hw1 X n).2))) S.2.val))
    (rat (Q'.invSucc n))
  exact h

/-- Type-valued, all-tail density certificate for INPUTS of represented
second-core points on supplied physical Rows. The modulus `e.den` is computed
from the requested rational tolerance; individual finite inverse-sum depths
also depend constructively on the source's rational norm ceiling. -/
def densityCertificate (X : Rows) :
    Σ' points : Nat → Domain, Σ' modulus : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
        RCle
          (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
            (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1 (points n))
            (BF4WilsonAllNomeComplexBondOSCompletion.ofRows hw0 hw1 X))
          (rat e) :=
  ⟨fun n => BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1
      (pairSources hw0 hw1 X n),
    fun e => e.den,
    by
      intro e he n hn
      exact RCle_trans (pairSources_bound hw0 hw1 X n)
        (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
          (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le e he)))⟩

#print axioms baseSource
#print axioms correctionDepth
#print axioms approximationSource
#print axioms approximationSource_pin
#print axioms approximationSource_bound
#print axioms pairSources
#print axioms pairSources_bound
#print axioms densityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreDensity
