/- # Block locality of upper signed angular directions -/

import YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
import YMGap.Continuum.SU2QuaternionSelectedHaarDerivative

namespace YMGap.Continuum.SU2QuaternionSignedAngularLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian

/-- A polynomial is independent of every upper block except the selected one. -/
def UpperLocalAway (n selected : Nat) (p : RatPoly) : Prop :=
  ∀ block, block < n → block ≠ selected →
    QuaternionBlockIndependent (n+block) p

def localTerms {n : Nat} (selected : Fin n) (terms : List (AngularTerm n)) :
    List (AngularTerm n) :=
  terms.filter (fun term => decide (term.block.val = selected.val))

theorem direction_congr {n : Nat} (terms : List (AngularTerm n))
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (signedAngularDirection terms p)
      (signedAngularDirection terms q) := by
  induction terms with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons term rest ih =>
      exact ((angularDerivative_congr _ _ h).smul term.coefficient).add ih

private theorem ratDerivative_preserves_independent
    {selected block component : Nat} (hne : block ≠ selected)
    (hc : component < 4) {p : RatPoly}
    (hp : QuaternionBlockIndependent selected p) :
    QuaternionBlockIndependent selected
      (ratDerivative (4*block+component) p) := by
  intro term ht
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ht
  change clearQuaternionBlock selected
      (lowerExponentAt (4*block+component) source.1) =
    lowerExponentAt (4*block+component) source.1
  rw [← lowerExponentAt_clearQuaternionBlock_of_ne hne hc,
    hp source hsource]

private theorem angularDerivative_preserves_independent
    {selected block first second : Nat} (hne : block ≠ selected)
    (hf : first < 4) (hs : second < 4) {p : RatPoly}
    (hp : QuaternionBlockIndependent selected p) :
    QuaternionBlockIndependent selected
      (angularDerivative (4*block+first) (4*block+second) p) := by
  unfold angularDerivative
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polyMul
      (quaternionBlockIndependent_polyVar_of_distinctBlock hne hf)
      (ratDerivative_preserves_independent hne hs hp))
    (quaternionBlockIndependent_polySmul (-1)
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyVar_of_distinctBlock hne hs)
        (ratDerivative_preserves_independent hne hf hp)))

private theorem direction_preserves_independent {n selected target : Nat}
    (hne : selected ≠ target) (terms : List (AngularTerm n))
    (hlocal : ∀ term, term ∈ terms → term.block.val = selected)
    {p : RatPoly} (hp : QuaternionBlockIndependent (n+target) p) :
    QuaternionBlockIndependent (n+target)
      (signedAngularDirection (upperTerms terms) p) := by
  induction terms with
  | nil => exact quaternionBlockIndependent_polyZero _
  | cons term rest ih =>
      have ht := hlocal term List.mem_cons_self
      have hblocks : n + term.block.val ≠ n + target := by omega
      exact quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polySmul term.coefficient
          (angularDerivative_preserves_independent hblocks
            term.first.isLt term.second.isLt hp))
        (ih (fun other ho => hlocal other (List.mem_cons_of_mem term ho)))

/-- Every upper generator away from `selected` vanishes coefficientwise, so
the full signed direction reduces exactly to its selected-block subfamily. -/
theorem upperDirection_localize {n : Nat} (selected : Fin n)
    (terms : List (AngularTerm n)) (p : RatPoly)
    (hp : UpperLocalAway n selected.val p) :
    RatPolyCoeffEqv
      (signedAngularDirection (upperTerms terms) p)
      (signedAngularDirection (upperTerms (localTerms selected terms)) p) := by
  induction terms with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons term rest ih =>
      by_cases h : term.block.val = selected.val
      · simp [upperTerms, localTerms, signedAngularDirection, h]
        exact (RatPolyCoeffEqv.refl _).add ih
      · have hz := angularDerivative_blockIndependent_zero
          term.first.isLt term.second.isLt
          (hp term.block.val term.block.isLt h)
        have hs : RatPolyCoeffEqv (applyAngularTerm (upperTerm term) p) polyZero :=
          (hz.smul term.coefficient).trans
            (RatPolyCoeffEqv.smul_zero term.coefficient)
        simp [upperTerms, localTerms, signedAngularDirection, h]
        exact (hs.add ih).trans (RatPolyCoeffEqv.zero_add _)

/-- The same localization holds after two applications provided the localized
first derivative retains independence of the other upper blocks.  This
hypothesis is exactly the algebraic locality condition needed by consumers. -/
theorem upperDirection_second_localize {n : Nat} (selected : Fin n)
    (terms : List (AngularTerm n)) (p : RatPoly)
    (hp : UpperLocalAway n selected.val p)
    (hdp : UpperLocalAway n selected.val
      (signedAngularDirection (upperTerms (localTerms selected terms)) p)) :
    RatPolyCoeffEqv
      (signedAngularDirection (upperTerms terms)
        (signedAngularDirection (upperTerms terms) p))
      (signedAngularDirection (upperTerms (localTerms selected terms))
        (signedAngularDirection (upperTerms (localTerms selected terms)) p)) := by
  let first := upperDirection_localize selected terms p hp
  exact (direction_congr (upperTerms terms) first).trans
    (upperDirection_localize selected terms
      (signedAngularDirection (upperTerms (localTerms selected terms)) p) hdp)

/-- The actual selected relative heat is upper-local away from its endpoint. -/
theorem heatAt_upperLocalAway (n : Nat) (selected : Fin n) (w : Q') (K : Nat) :
    UpperLocalAway n selected.val (heatAt selected.val (n+selected.val) w K) := by
  intro block hblock hne
  exact degree_zero_independent
    (heat_independent (n+block) selected.val (n+selected.val)
      (by omega) (by omega) w K)

/-- The localized first derivative of the actual heat remains independent of
every other upper block, so second localization needs no external premise. -/
theorem heatAt_localDirection_upperLocalAway
    (n : Nat) (selected : Fin n) (terms : List (AngularTerm n))
    (w : Q') (K : Nat) :
    UpperLocalAway n selected.val
      (signedAngularDirection (upperTerms (localTerms selected terms))
        (heatAt selected.val (n+selected.val) w K)) := by
  intro target htarget hne
  apply direction_preserves_independent (n := n) (selected := selected.val)
    (target := target) hne.symm
  · intro term ht
    have hm := List.mem_filter.mp ht
    exact of_decide_eq_true hm.2
  · exact heatAt_upperLocalAway n selected w K target htarget hne

/-- Assumption-free second localization for the actual selected heat factor. -/
theorem heatAt_upperDirection_second_localize
    (n : Nat) (selected : Fin n) (terms : List (AngularTerm n))
    (w : Q') (K : Nat) :
    RatPolyCoeffEqv
      (signedAngularDirection (upperTerms terms)
        (signedAngularDirection (upperTerms terms)
          (heatAt selected.val (n+selected.val) w K)))
      (signedAngularDirection (upperTerms (localTerms selected terms))
        (signedAngularDirection (upperTerms (localTerms selected terms))
          (heatAt selected.val (n+selected.val) w K))) :=
  upperDirection_second_localize selected terms _
    (heatAt_upperLocalAway n selected w K)
    (heatAt_localDirection_upperLocalAway n selected terms w K)

end YMGap.Continuum.SU2QuaternionSignedAngularLocality

#print axioms YMGap.Continuum.SU2QuaternionSignedAngularLocality.upperDirection_localize
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularLocality.upperDirection_second_localize
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularLocality.heatAt_upperLocalAway
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularLocality.heatAt_localDirection_upperLocalAway
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularLocality.heatAt_upperDirection_second_localize
