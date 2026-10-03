/-
# Signed two-output polarization of the ORIGINAL Rayleigh determinant

The two output slots carry V once each. The first/second transformed
differences are built factorwise with the unchanged original transfer T.
Weighted symmetry cancels the mixed terms EXACTLY, leaving D and -D,
where D=ell(A*T A)*ell(b*b)-ell(A*A)*ell(b*T b).

No inverse of A, replacement of the filtered norm, centering, positivity,
finite eigenpin or ambient tensor-operator construction is used. This is
a cancellation-preserving finite producer; its useful relative estimate
on a justified changing family and the continuum/physical joins stay open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction (haar_split_pairing)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight transferStep weightedMass

/-- The unchanged first slot and an explicitly shifted second output slot. -/
def tensor (width : Nat) (p q : RatPoly) : RatPoly :=
  polyMul p (liftBoundary (N width) q)

/-- The original output weight occurs ONCE in EACH of the two slots. -/
def twoCopyMass (w : Q') (K width : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (tensor width (spatialWeight w K width) (spatialWeight w K width)) p)

def twoCopyPair (w : Q') (K width : Nat) (p q : RatPoly) : Q' :=
  twoCopyMass w K width (polyMul p q)

private def pair (w : Q') (K width : Nat) (p q : RatPoly) : Q' :=
  weightedMass w K width (polyMul p q)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Product Haar is factored only between the two separately placed slots.
Each slot retains the complete original spatial insertion. -/
theorem tensor_pair (w : Q') (K width : Nat) {p r : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (hr : SupportedQuaternionBlocks (N width) r) (q s : RatPoly) :
    twoCopyPair w K width (tensor width p q) (tensor width r s) ≈
      weightedMass w K width (polyMul p r) * weightedMass w K width (polyMul q s) := by
  have hc : RatPolyCoeffEqv
      (polyMul (tensor width (spatialWeight w K width) (spatialWeight w K width))
        (polyMul (tensor width p q) (tensor width r s)))
      (polyMul (polyMul (spatialWeight w K width) (polyMul p r))
        (liftBoundary (N width) (polyMul (spatialWeight w K width) (polyMul q s)))) := by
    dsimp only [tensor]
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 4)))
        (.mul (.var 1) (.mul (.var 3) (.var 5))))
      (by decide) (fun
        | 0 => spatialWeight w K width | 1 => liftBoundary (N width) (spatialWeight w K width)
        | 2 => p | 3 => liftBoundary (N width) q | 4 => r | _ => liftBoundary (N width) s)
  unfold weightedMass
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (haar_split_pairing
      (supported_polyMul (spatialWeight_supported w K width) (supported_polyMul hp hr))
      (polyMul (spatialWeight w K width) (polyMul q s)))

private theorem mass_add (w : Q') (K width : Nat) (p q : RatPoly) :
    twoCopyMass w K width (polyAdd p q) ≈ twoCopyMass w K width p+twoCopyMass w K width q :=
  quaternionHaar_polyMul_add_right _ _ p q

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    twoCopyMass w K width (polyNeg p) ≈ -(twoCopyMass w K width p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.refl _).mul (neg_smul p)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ (-1) _ p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => twoCopyMass w K width p)))

private theorem pair_add_sub (w : Q') (K width : Nat) (p q r s : RatPoly) :
    twoCopyPair w K width (polyAdd p q) (polyAdd r (polyNeg s)) ≈
      (twoCopyPair w K width p r + -(twoCopyPair w K width p s))+
        (twoCopyPair w K width q r + -(twoCopyPair w K width q s)) := by
  have hc : RatPolyCoeffEqv (polyMul (polyAdd p q) (polyAdd r (polyNeg s)))
      (polyAdd (polyAdd (polyMul p r) (polyNeg (polyMul p s)))
        (polyAdd (polyMul q r) (polyNeg (polyMul q s)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.neg (.var 3))))
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
        (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 1) (.var 3)))))
      (by decide) (fun | 0 => p | 1 => q | 2 => r | _ => s)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul hc))
    (Q'.eqv_trans _ _ _ (mass_add w K width _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (mass_add w K width _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (mass_neg w K width _)))
        (Q'.eqv_trans _ _ _ (mass_add w K width _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (mass_neg w K width _)))))

/-- Symmetric source paired with a transformed antisymmetric source. -/
def symmetricProduct (width : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (tensor width A b) (tensor width b A)

def antisymmetricProduct (width : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (tensor width A b) (polyNeg (tensor width b A))

/-- Apply the ORIGINAL transfer to the first factor of each displayed tensor. -/
def firstDifference (w : Q') (K width : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (tensor width (transferStep w K width A) b)
    (polyNeg (tensor width (transferStep w K width b) A))

/-- Apply the ORIGINAL transfer to the second factor; no ambient tensor map
or new completion is postulated by these finite polynomial definitions. -/
def secondDifference (w : Q') (K width : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (tensor width A (transferStep w K width b))
    (polyNeg (tensor width b (transferStep w K width A)))

/-- All mixed terms cancel through actual weighted transfer symmetry. -/
theorem first_pairing_determinant (w : Q') (K width : Nat) {A b : RatPoly}
    (hA : SupportedQuaternionBlocks (N width) A)
    (hb : SupportedQuaternionBlocks (N width) b) :
    twoCopyPair w K width (symmetricProduct width A b) (firstDifference w K width A b) ≈
      clearedRayleighCost w K width A b := by
  have hTA := transferStep_supported w K width hA
  have hTb := transferStep_supported w K width hb
  have hs : pair w K width b (transferStep w K width A) ≈
      pair w K width A (transferStep w K width b) :=
    transferStep_weighted_symmetric w K width hA hb
  have hc : pair w K width b A ≈ pair w K width A b :=
    weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b A)
  have he := Q'.eqv_trans _ _ _ (pair_add_sub w K width
    (tensor width A b) (tensor width b A) (tensor width (transferStep w K width A) b)
      (tensor width (transferStep w K width b) A))
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (tensor_pair w K width hA hTA b b)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (tensor_pair w K width hA hTb b A)
          (qmul (Q'.eqv_refl _) hc))))
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (tensor_pair w K width hb hTA A b)
          (qmul hs (Q'.eqv_refl _)))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (tensor_pair w K width hb hTb A A)
          (Q'.mul_comm_eqv _ _)))))
  exact Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
        (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 4) (.var 5)))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 4) (.var 5)))) (by decide)
      (fun
        | 0 => pair w K width A (transferStep w K width A)
        | 1 => pair w K width b b
        | 2 => pair w K width A (transferStep w K width b)
        | 3 => pair w K width A b
        | 4 => pair w K width A A
        | _ => pair w K width b (transferStep w K width b)))

/-- The second-slot pairing is the NEGATIVE of that same determinant. -/
theorem second_pairing_determinant (w : Q') (K width : Nat) {A b : RatPoly}
    (hA : SupportedQuaternionBlocks (N width) A)
    (hb : SupportedQuaternionBlocks (N width) b) :
    twoCopyPair w K width (symmetricProduct width A b) (secondDifference w K width A b) ≈
      -(clearedRayleighCost w K width A b) := by
  have hs : pair w K width b (transferStep w K width A) ≈
      pair w K width A (transferStep w K width b) :=
    transferStep_weighted_symmetric w K width hA hb
  have hc : pair w K width b A ≈ pair w K width A b :=
    weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b A)
  have he := Q'.eqv_trans _ _ _ (pair_add_sub w K width
    (tensor width A b) (tensor width b A) (tensor width A (transferStep w K width b))
      (tensor width b (transferStep w K width A)))
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (tensor_pair w K width hA hA b (transferStep w K width b))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (tensor_pair w K width hA hb b (transferStep w K width A))
          (qmul (Q'.eqv_refl _) hs))))
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
          (tensor_pair w K width hb hA A (transferStep w K width b))
          (qmul hc (Q'.eqv_refl _)))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (tensor_pair w K width hb hb A (transferStep w K width A)) (Q'.mul_comm_eqv _ _)))))
  exact Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 4) (.var 5)) (.neg (.mul (.var 3) (.var 2))))
        (.add (.mul (.var 3) (.var 2)) (.neg (.mul (.var 0) (.var 1)))))
      (.neg (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 4) (.var 5))))) (by decide)
      (fun
        | 0 => pair w K width A (transferStep w K width A)
        | 1 => pair w K width b b
        | 2 => pair w K width A (transferStep w K width b)
        | 3 => pair w K width A b
        | 4 => pair w K width A A
        | _ => pair w K width b (transferStep w K width b)))

/-- Ratio-free antisymmetric transfer difference representing TWICE the
complete original cost. No signed summand is bounded or discarded. -/
theorem antisymmetric_pairing_determinant (w : Q') (K width : Nat) {A b : RatPoly}
    (hA : SupportedQuaternionBlocks (N width) A)
    (hb : SupportedQuaternionBlocks (N width) b) :
    twoCopyPair w K width (symmetricProduct width A b)
      (polyAdd (firstDifference w K width A b) (polyNeg (secondDifference w K width A b))) ≈
      clearedRayleighCost w K width A b + clearedRayleighCost w K width A b := by
  have h := quaternionHaar_polyMul_add_right (N width+N width)
    (tensor width (spatialWeight w K width) (spatialWeight w K width))
    (polyMul (symmetricProduct width A b) (firstDifference w K width A b))
    (polyNeg (polyMul (symmetricProduct width A b) (secondDifference w K width A b)))
  have hc : RatPolyCoeffEqv
      (polyMul (symmetricProduct width A b)
        (polyAdd (firstDifference w K width A b) (polyNeg (secondDifference w K width A b))))
      (polyAdd (polyMul (symmetricProduct width A b) (firstDifference w K width A b))
        (polyNeg (polyMul (symmetricProduct width A b) (secondDifference w K width A b)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun
        | 0 => symmetricProduct width A b
        | 1 => firstDifference w K width A b
        | _ => secondDifference w K width A b)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul hc))
    (Q'.eqv_trans _ _ _ h
      (Q'.add_eqv_congr' (first_pairing_determinant w K width hA hb)
        (Q'.eqv_trans _ _ _ (mass_neg w K width _)
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (second_pairing_determinant w K width hA hb))
            (Q'.neg_neg_eqv _)))))

#print axioms tensor_pair
#print axioms first_pairing_determinant
#print axioms second_pairing_determinant
#print axioms antisymmetric_pairing_determinant

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant
