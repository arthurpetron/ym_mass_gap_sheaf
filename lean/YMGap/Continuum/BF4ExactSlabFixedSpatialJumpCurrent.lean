/-
# Original signed mixed jump current

The doubled-carrier current retains the COMPLETE kinetic kernel and BOTH
spatial weights V(x)V(y), multiplying (b(x)g(y)-g(x)b(y))(f(x)-f(y)).
Original Haar swap symmetry and ordered-head pairing fold it to
2*(ell[b*f*Tg]-ell[b*T(g*f)]). For the actual terminal and centered message
this is -2 times the existing full-source defect at reference a=1.

All statements are finite signed identities at arbitrary rational nome and
cutoff. No current sign, score cancellation, relative estimate, partition
identification, finite stationarity or continuum conclusion is asserted.
The supplied center is retained inside b, not replaced by another mean.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJumpCurrent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
  (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
  (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
  (fullSourceDefectPair fullSourceDefectPair_transfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (kernel_pairing_swap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step_pairing)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted_supported)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

/-- Literal antisymmetric mixed current under the original full edge weight. -/
def signedCurrent (w : Q') (K width : Nat) (g b f : RatPoly) : Q' :=
  let V := spatialWeight w K width
  let lift := liftBoundary (N width)
  quaternionHaar (N width+N width) (polyMul
    (polyMul (kineticWeight w K width) (polyMul V (lift V)))
    (polyMul
      (polyAdd (polyMul b (lift g)) (polyNeg (polyMul g (lift b))))
      (polyAdd f (polyNeg (lift f)))))

private def edgeProduct (w : Q') (K width : Nat) (p q : RatPoly) : RatPoly :=
  polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) p))
    (liftBoundary (N width) (polyMul (spatialWeight w K width) q))

private theorem haar_neg (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => quaternionHaar blocks p)))

private theorem edgeProduct_fold (w : Q') (K width : Nat) (p q : RatPoly) :
    quaternionHaar (N width+N width) (edgeProduct w K width p q) ≈
      weightedMass w K width (polyMul q (transferStep w K width p)) :=
  Q'.eqv_trans _ _ _
    (step_pairing (N width) (N width) (kineticWeight w K width)
      (spatialWeight w K width) p (polyMul (spatialWeight w K width) q))
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide) (fun
        | 0 => transferStep w K width p
        | 1 => spatialWeight w K width
        | _ => q)))

private theorem current_expand (w : Q') (K width : Nat) (g b f : RatPoly) :
    signedCurrent w K width g b f ≈
      (quaternionHaar (N width+N width) (edgeProduct w K width (polyMul b f) g) -
        quaternionHaar (N width+N width) (edgeProduct w K width b (polyMul g f))) +
      (-quaternionHaar (N width+N width) (edgeProduct w K width (polyMul g f) b) +
        quaternionHaar (N width+N width) (edgeProduct w K width g (polyMul b f))) := by
  let L := edgeProduct w K width (polyMul b f) g
  let M := edgeProduct w K width b (polyMul g f)
  let R := edgeProduct w K width (polyMul g f) b
  let S := edgeProduct w K width g (polyMul b f)
  have he : RatPolyCoeffEqv
      (polyMul
        (polyMul (kineticWeight w K width)
          (polyMul (spatialWeight w K width) (liftBoundary (N width) (spatialWeight w K width))))
        (polyMul
          (polyAdd (polyMul b (liftBoundary (N width) g))
            (polyNeg (polyMul g (liftBoundary (N width) b))))
          (polyAdd f (polyNeg (liftBoundary (N width) f)))))
      (polyAdd (polyAdd L (polyNeg M)) (polyAdd (polyNeg R) S)) := by
    dsimp only [L, M, R, S, edgeProduct]
    simp only [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.add (.mul (.var 5) (.var 4)) (.neg (.mul (.var 3) (.var 6))))
          (.add (.var 7) (.neg (.var 8)))))
      (.add
        (.add (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 5) (.var 7))))
          (.mul (.var 2) (.var 4)))
          (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.var 5)))
            (.mul (.var 2) (.mul (.var 4) (.var 8))))))
        (.add (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 7))))
          (.mul (.var 2) (.var 6))))
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 3)))
            (.mul (.var 2) (.mul (.var 6) (.var 8))))))
      (by decide) (fun
        | 0 => kineticWeight w K width
        | 1 => spatialWeight w K width
        | 2 => liftBoundary (N width) (spatialWeight w K width)
        | 3 => g
        | 4 => liftBoundary (N width) g
        | 5 => b
        | 6 => liftBoundary (N width) b
        | 7 => f
        | _ => liftBoundary (N width) f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg _ M)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (haar_neg _ R) (Q'.eqv_refl _)))))

/-- Exact original transfer fold, with both endpoint action factors intact. -/
theorem signedCurrent_transfer (w : Q') (K width : Nat) {g b f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hb : SupportedQuaternionBlocks (N width) b)
    (hf : SupportedQuaternionBlocks (N width) f) :
    signedCurrent w K width g b f ≈ 2*(
      weightedMass w K width (polyMul (polyMul b f) (transferStep w K width g)) -
      weightedMass w K width (polyMul b (transferStep w K width (polyMul g f)))) := by
  have hV := spatialWeight_supported w K width
  have hk := kineticWeight_supported w K width
  have hs := kineticWeight_swap w K width
  have hL := kernel_pairing_swap (blocks := N width) hk
    (supported_polyMul hV (supported_polyMul hb hf)) (supported_polyMul hV hg) hs
  have hM := kernel_pairing_swap (blocks := N width) hk
    (supported_polyMul hV hb) (supported_polyMul hV (supported_polyMul hg hf)) hs
  have hS := edgeProduct_fold w K width g (polyMul b f)
  have hR := edgeProduct_fold w K width (polyMul g f) b
  have hL' := Q'.eqv_trans _ _ _ hL hS
  have hM' := Q'.eqv_trans _ _ _ hM hR
  exact Q'.eqv_trans _ _ _ (current_expand w K width g b f)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hL' (Q'.neg_eqv_congr _ _ hM'))
        (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hR) hS))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.neg (.var 1)) (.var 0)))
        (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide) (fun
          | 0 => weightedMass w K width (polyMul (polyMul b f) (transferStep w K width g))
          | _ => weightedMass w K width (polyMul b (transferStep w K width (polyMul g f))))))

/-- Actual terminal source and fixed centered message at reference one.
No finite zero-mean or terminal eigenvector assertion is used. -/
theorem original_centered_current_source_pin (w : Q') (K width n : Nat)
    (f : RatPoly) (c : Q') (hf : SupportedQuaternionBlocks (N width) f) :
    signedCurrent w K width (terminalMessage w K width n)
      (centeredMessage w K width n f c) f ≈
      (-2)*fullSourceDefectPair w K width n f c 1 := by
  let g := terminalMessage w K width n
  let b := centeredMessage w K width n f c
  have hg := terminalMessage_supported w K width n
  have hb : SupportedQuaternionBlocks (N width) b := transferStep_supported w K width
    (supported_polyMul hg (shifted_supported hf c))
  have h := signedCurrent_transfer w K width hg hb hf
  have hp := fullSourceDefectPair_transfer w K width n f c 1
  have hc : weightedMass w K width (polyMul (polyMul b f) (transferStep w K width g)) ≈
      weightedMass w K width (polyMul b (polyMul (transferStep w K width g) f)) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_assoc b f (transferStep w K width g)).trans
      ((RatPolyCoeffEqv.mul_comm f (transferStep w K width g)).mul_left b)).mul_left
        (spatialWeight w K width))
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 2 _ _ (Q'.add_eqv_congr' hc (Q'.eqv_refl _)))
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.const 2) (.add (.var 1) (.neg (.var 0))))
        (.mul (.const (-2)) (.add (.var 0) (.mul (.neg (.const 1)) (.var 1))))
        (by decide) (fun
          | 0 => weightedMass w K width (polyMul b (transferStep w K width (polyMul g f)))
          | _ => weightedMass w K width (polyMul b (polyMul (transferStep w K width g) f))))
      (Q'.mul_eqv_congr_left (-2) _ _ hp.symm)))

#print axioms signedCurrent
#print axioms signedCurrent_transfer
#print axioms original_centered_current_source_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialJumpCurrent
