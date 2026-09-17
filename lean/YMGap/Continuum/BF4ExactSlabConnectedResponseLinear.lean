/-
# The rank-one subtraction in the original face response

The connected numerator is linear in its first observable, with its SAME
original selected action and partition retained. Consequently a direction
whose connected pairing with the actual inserted heat vanishes loses the
entire subtractive square in the diagonal response.

These identities hold at every cutoff, with no positivity or locality
premise. They do not construct a nonzero direction or bound the remaining
third cumulant. Those are separate physical consumers; no susceptibility
estimate or spectral-gap conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4ExactSlabConnectedResponseLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (j : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ j)

private theorem numerator_congr (w : Q') (K extent : Nat) (ids : List Nat)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    numerator w (B extent) extent ids p K ≈ numerator w (B extent) extent ids q K :=
  haar_of_coeff (h.mul_right _)

private theorem numerator_add (w : Q') (K extent : Nat) (ids : List Nat) (p q : RatPoly) :
    numerator w (B extent) extent ids (polyAdd p q) K ≈
      numerator w (B extent) extent ids p K + numerator w (B extent) extent ids q K := by
  unfold numerator
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append _ _ _

private theorem numerator_smul (w : Q') (K extent : Nat) (ids : List Nat) (a : Q') (p : RatPoly) :
    numerator w (B extent) extent ids (polySmul a p) K ≈
      a*numerator w (B extent) extent ids p K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left a p _))
    (quaternionHaar_polySmul _ a _)

/-- Coefficient recoding preserves the same connected pairing. -/
theorem connectedNumerator_congr_left (w : Q') (K extent : Nat) (ids : List Nat)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) (r : RatPoly) :
    connectedNumerator w K extent ids p r ≈ connectedNumerator w K extent ids q r :=
  Q'.add_eqv_congr'
    (qmul (numerator_congr w K extent ids (h.mul_right r)) (Q'.eqv_refl _))
    (Q'.neg_eqv_congr _ _ (qmul (numerator_congr w K extent ids h) (Q'.eqv_refl _)))

/-- Additivity with the original action and its original partition fixed. -/
theorem connectedNumerator_add_left (w : Q') (K extent : Nat) (ids : List Nat)
    (p q h : RatPoly) :
    connectedNumerator w K extent ids (polyAdd p q) h ≈
      connectedNumerator w K extent ids p h + connectedNumerator w K extent ids q h := by
  have hpq : numerator w (B extent) extent ids (polyMul (polyAdd p q) h) K ≈
      numerator w (B extent) extent ids (polyMul p h) K +
        numerator w (B extent) extent ids (polyMul q h) K := by
    rw [polyMul_add_left_exact]
    exact numerator_add w K extent ids _ _
  unfold connectedNumerator
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (qmul hpq (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul (numerator_add w K extent ids p q) (Q'.eqv_refl _)))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
      (.neg (.mul (.add (.var 3) (.var 4)) (.var 5))))
    (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 3) (.var 5))))
      (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 4) (.var 5)))))
    (by decide)
    (fun | 0 => numerator w (B extent) extent ids (polyMul p h) K
         | 1 => numerator w (B extent) extent ids (polyMul q h) K
         | 2 => heatProductHaar w (B extent) extent ids K
         | 3 => numerator w (B extent) extent ids p K
         | 4 => numerator w (B extent) extent ids q K
         | _ => numerator w (B extent) extent ids h K)

/-- Homogeneity for an arbitrary signed rational coefficient. -/
theorem connectedNumerator_smul_left (w : Q') (K extent : Nat) (ids : List Nat)
    (a : Q') (p h : RatPoly) :
    connectedNumerator w K extent ids (polySmul a p) h ≈
      a*connectedNumerator w K extent ids p h := by
  have hprod : numerator w (B extent) extent ids (polyMul (polySmul a p) h) K ≈
      a*numerator w (B extent) extent ids (polyMul p h) K :=
    Q'.eqv_trans _ _ _
      (numerator_congr w K extent ids (RatPolyCoeffEqv.polyMul_smul_left a p h))
      (numerator_smul w K extent ids a (polyMul p h))
  unfold connectedNumerator
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (qmul hprod (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul (numerator_smul w K extent ids a p) (Q'.eqv_refl _)))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.neg (.mul (.mul (.var 0) (.var 3)) (.var 4))))
    (.mul (.var 0)
      (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4)))))
    (by decide)
    (fun | 0 => a | 1 => numerator w (B extent) extent ids (polyMul p h) K
         | 2 => heatProductHaar w (B extent) extent ids K
         | 3 => numerator w (B extent) extent ids p K
         | _ => numerator w (B extent) extent ids h K)

/-- Two signed directions combine before any absolute value or estimate. -/
theorem connectedNumerator_linear_left (w : Q') (K extent : Nat) (ids : List Nat)
    (a b : Q') (p q h : RatPoly) :
    connectedNumerator w K extent ids (polyAdd (polySmul a p) (polySmul b q)) h ≈
      a*connectedNumerator w K extent ids p h + b*connectedNumerator w K extent ids q h :=
  Q'.eqv_trans _ _ _ (connectedNumerator_add_left w K extent ids _ _ h)
    (Q'.add_eqv_congr' (connectedNumerator_smul_left w K extent ids a p h)
      (connectedNumerator_smul_left w K extent ids b q h))

/-- The diagonal subtraction vanishes for a direction orthogonal to the
actual cutoff-dependent inserted heat. The third cumulant remains unchanged. -/
theorem response_eq_third_of_connected_zero (w : Q') (K extent : Nat)
    (ids : List Nat) (id : Nat) (F : RatPoly)
    (hzero : connectedNumerator w K extent ids F (faceHeatPolynomial w K extent id) ≈ 0) :
    response w K extent ids id F F ≈
      numerator w (B extent) extent ids (faceHeatPolynomial w K extent id) K *
        thirdNumerator w K extent ids F F (faceHeatPolynomial w K extent id) := by
  unfold response
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (qmul hzero hzero)))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ =>
        numerator w (B extent) extent ids (faceHeatPolynomial w K extent id) K *
          thirdNumerator w K extent ids F F (faceHeatPolynomial w K extent id)))

end YMGap.Continuum.BF4ExactSlabConnectedResponseLinear

#print axioms YMGap.Continuum.BF4ExactSlabConnectedResponseLinear.connectedNumerator_congr_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedResponseLinear.connectedNumerator_add_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedResponseLinear.connectedNumerator_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedResponseLinear.connectedNumerator_linear_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedResponseLinear.response_eq_third_of_connected_zero
