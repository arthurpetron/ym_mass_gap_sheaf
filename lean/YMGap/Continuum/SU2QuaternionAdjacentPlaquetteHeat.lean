/-
# Shared-link heat propagation of two original fundamental plaquettes

Retain the shared relative heat kernel. Its quadratic channel is multiplied
by w^8, while the scalar Schur channel is preserved. All retained variables
remain in an arbitrary polynomial insertion. The source link may NOT occur
in that insertion: other action factors using it cannot be discarded.

These are exact selected-action identities, not a bound for the complete
V*T^n1, a claim of positive truncated heat at every cutoff, or a global gap.
The K>=2 guard concerns harmonic transmission only.
-/

import YMGap.Continuum.SU2QuaternionQuadraticHeatProduct
import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.SU2QuaternionHeatCovarianceRates

namespace YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionQuadraticHeatProduct
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionHeatCovarianceRates

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private def environment (p : PolyQuaternion) (i : Nat) : RatPoly :=
  match i with
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => polyVar 0 | 5 => polyVar 1 | 6 => polyVar 2 | _ => polyVar 3

private theorem retained_slim (p : Fin 4 → RatPoly) :
    RatPolyCoeffEqv (retainedLinear (four p))
      (polyAdd (polyMul (polyVar 0) (p 0)) (polyAdd (polyMul (polyVar 1) (p 1))
        (polyAdd (polyMul (polyVar 2) (p 2)) (polyMul (polyVar 3) (p 3))))) :=
  (RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))

private theorem retained_left (p : PolyQuaternion) :
    RatPolyCoeffEqv (retainedLinear (four (signedComponents p)))
      (p ⋄ PolyQuaternion.coordinateVariable 0).scalar := by
  refine (retained_slim _).trans ?_
  simpa only [signedComponents, components, Fin.reduceFinMk,
    Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceEqDiff, ↓reduceIte,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    PolyQuaternion.mul, PolyQuaternion.coordinateVariable, environment, coeffEvalExpr] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 4) (.var 0)) (.add (.mul (.var 5) (.neg (.var 1)))
        (.add (.mul (.var 6) (.neg (.var 2))) (.mul (.var 7) (.neg (.var 3))))))
      (.add (.mul (.var 0) (.var 4)) (.neg (.add (.mul (.var 1) (.var 5))
        (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))))
      (by decide) (environment p))

private theorem retained_right (p : PolyQuaternion) :
    RatPolyCoeffEqv (retainedLinear (four (components p)))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0) ⋄ p).scalar := by
  refine (retained_slim _).trans ?_
  simpa only [components, Fin.reduceFinMk,
    PolyQuaternion.mul, PolyQuaternion.conj, PolyQuaternion.coordinateVariable,
    environment, coeffEvalExpr] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 4) (.var 0)) (.add (.mul (.var 5) (.var 1))
        (.add (.mul (.var 6) (.var 2)) (.mul (.var 7) (.var 3)))))
      (.add (.mul (.var 4) (.var 0)) (.neg (.add (.mul (.neg (.var 5)) (.var 1))
        (.add (.mul (.neg (.var 6)) (.var 2)) (.mul (.neg (.var 7)) (.var 3))))))
      (by decide) (environment p))

private theorem gram_scalar (p q : PolyQuaternion) :
    RatPolyCoeffEqv (gram (four (signedComponents p)) (four (components q)))
      (polySmul SU2QuaternionHeadLinearHaar.quarter (p ⋄ q).scalar) :=
  (linear_pair _ _).symm.trans
    ((partialHaarHead_congr ((left_linear p).mul (right_linear q))).symm.trans
      (scalar_schur p q))

def scalarSource (p q : PolyQuaternion) : RatPoly :=
  polyMul (liftQuaternion p ⋄ PolyQuaternion.coordinateVariable 0).scalar
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0) ⋄ liftQuaternion q).scalar

def scalarTarget (p q : PolyQuaternion) : RatPoly :=
  polyMul (p ⋄ PolyQuaternion.coordinateVariable 0).scalar
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0) ⋄ q).scalar

def scalarImage (w : Q') (p q : PolyQuaternion) : RatPoly :=
  polyAdd (polySmul (qpow w 8) (scalarTarget p q))
    (polySmul ((1 + -(qpow w 8)) * SU2QuaternionHeadLinearHaar.quarter) (p ⋄ q).scalar)

private theorem image_pin (w : Q') (p q : PolyQuaternion) :
    RatPolyCoeffEqv (linearProductImage w (four (signedComponents p)) (four (components q)))
      (scalarImage w p q) :=
  (((retained_left p).mul (retained_right q)).smul _).add
    (((gram_scalar p q).smul _).trans (RatPolyCoeffEqv.smul_assoc _ _ _))

theorem scalar_heat_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (p q : PolyQuaternion) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (scalarSource p q)) (liftHead r)) ≈
      quaternionHaar tailBlocks (polyMul (scalarImage w p q) r) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((((left_linear p).mul (right_linear q)).mul_left _).mul_right _))
    (Q'.eqv_trans _ _ _ (linear_product_transmission tailBlocks hb w K hK _ _ r)
      (haar_of_coeff ((image_pin w p q).mul_right r)))

def pathSource (p q : PolyQuaternion) : RatPoly :=
  polyMul (characterPolynomial (liftQuaternion p ⋄ PolyQuaternion.coordinateVariable 0).scalar 1)
    (characterPolynomial (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0) ⋄ liftQuaternion q).scalar 1)

def pathTarget (p q : PolyQuaternion) : RatPoly :=
  polyMul (characterPolynomial (p ⋄ PolyQuaternion.coordinateVariable 0).scalar 1)
    (characterPolynomial (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0) ⋄ q).scalar 1)

/-- The two actual shared-link channels, not a product of degree-one images. -/
def pathImage (w : Q') (p q : PolyQuaternion) : RatPoly :=
  polyAdd (polySmul (qpow w 8) (pathTarget p q))
    (polySmul ((1 + -(qpow w 8)) * schurFactor) (characterPolynomial (p ⋄ q).scalar 1))

private theorem character_scale (a b : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul 2 a) (polySmul 2 b)) (polySmul 4 (polyMul a b)) :=
  (RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
    (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul 2).trans
      ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : (2 : Q')*2 ≈ 4) _)))

private theorem smul_comm (a b : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul a (polySmul b p)) (polySmul b (polySmul a p)) :=
  (RatPolyCoeffEqv.smul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv a b) p).trans
      (RatPolyCoeffEqv.smul_assoc _ _ _).symm)

private theorem pathImage_scaled (w : Q') (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polySmul 4 (scalarImage w p q)) (pathImage w p q) := by
  have hs : (4 : Q') * ((1 + -(qpow w 8)) * SU2QuaternionHeadLinearHaar.quarter) ≈
      ((1 + -(qpow w 8)) * schurFactor) * 2 := by
    have hc : (4 : Q') * SU2QuaternionHeadLinearHaar.quarter ≈ schurFactor * 2 := by decide
    exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 4) (.var 1)))
      (by decide) (fun | 0 => 1 + -(qpow w 8) | _ => SU2QuaternionHeadLinearHaar.quarter))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc)
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  exact (RatPolyCoeffEqv.smul_add _ _ _).trans
    (((smul_comm _ _ _).trans ((character_scale _ _).symm.smul _)).add
      ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient hs _).trans (RatPolyCoeffEqv.smul_assoc _ _ _).symm)))

/-- Shared-link Schur heat identity, with arbitrary retained paths and tests.
The paths need not be disjoint or independent of the target quaternion. -/
theorem path_heat_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (p q : PolyQuaternion) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (pathSource p q)) (liftHead r)) ≈
      quaternionHaar tailBlocks (polyMul (pathImage w p q) r) := by
  have hscale : RatPolyCoeffEqv
      (polyMul (polyMul (relativeHeat w K) (pathSource p q)) (liftHead r))
      (polySmul 4 (polyMul (polyMul (relativeHeat w K) (scalarSource p q)) (liftHead r))) :=
    (((character_scale _ _).mul_left _).mul_right _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).mul_right _).trans
        (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hscale)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _
        (scalar_heat_transmission tailBlocks hb w K hK p q r))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _))
          (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).symm.trans
            ((pathImage_scaled w p q).mul_right r))))))

/-- Shared source link 0, target link 1, and six outer links 2..7.
Both plaquettes use the SAME source link with opposite orientations. -/
def sourceAdjacentProduct : RatPoly :=
  polyMul (plaquette 2 0 6 7) (plaquette 3 4 5 0)

/-- After integrating the source, the target occupies block 0 and the six
outer links occupy 1..6. The rectangle omits only that shared target. -/
def adjacentImage (w : Q') : RatPoly :=
  polyAdd (polySmul (qpow w 8) adjacentProduct)
    (polySmul ((1 + -(qpow w 8)) * schurFactor) (liftHead rectangle))

private theorem source_pair_pin :
    RatPolyCoeffEqv sourceAdjacentProduct
      (pathSource (liftQuaternion leftPath) (liftQuaternion rightPath)) := by
  have hl : liftQuaternion (liftQuaternion leftPath) =
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 7)) ⋄
          PolyQuaternion.coordinateVariable 2 := by
    simp only [leftPath, lift_mul, lift_conj]
    rfl
  have hr : liftQuaternion (liftQuaternion rightPath) =
      (PolyQuaternion.coordinateVariable 3 ⋄ PolyQuaternion.coordinateVariable 4) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5) := by
    simp only [rightPath, lift_mul, lift_conj]
    rfl
  unfold pathSource
  rw [hl, hr]
  exact ((first_cycle (PolyQuaternion.coordinateVariable 2) (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 7))).smul 2).mul
      ((polyQuaternion_mul_scalar_cyclic
        ((PolyQuaternion.coordinateVariable 3 ⋄ PolyQuaternion.coordinateVariable 4) ⋄
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5))
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))).smul 2)

private theorem target_pair_pin :
    RatPolyCoeffEqv (pathTarget (liftQuaternion leftPath) (liftQuaternion rightPath))
      adjacentProduct := by
  have hl : liftQuaternion leftPath =
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6)) ⋄
          PolyQuaternion.coordinateVariable 1 := by
    simp only [leftPath, lift_mul, lift_conj]
    rfl
  have hr : liftQuaternion rightPath =
      (PolyQuaternion.coordinateVariable 2 ⋄ PolyQuaternion.coordinateVariable 3) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4) := by
    simp only [rightPath, lift_mul, lift_conj]
    rfl
  unfold pathTarget
  rw [hl, hr]
  exact (((first_cycle (PolyQuaternion.coordinateVariable 1) (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6))).smul 2).mul
      ((polyQuaternion_mul_scalar_cyclic
        ((PolyQuaternion.coordinateVariable 2 ⋄ PolyQuaternion.coordinateVariable 3) ⋄
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4))
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))).smul 2)).symm

private theorem lift_smul (c : Q') (p : RatPoly) :
    liftHead (polySmul c p) = polySmul c (liftHead p) := by
  simp only [liftHead, polySmul, List.map_map]
  rfl

private theorem rectangle_pin :
    RatPolyCoeffEqv
      (characterPolynomial (liftQuaternion leftPath ⋄ liftQuaternion rightPath).scalar 1)
      (liftHead rectangle) := by
  have h := (outer_cycle (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.coordinateVariable 1) (PolyQuaternion.coordinateVariable 2)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 3))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5))).smul 2
  have hp : RatPolyCoeffEqv (characterPolynomial (leftPath ⋄ rightPath).scalar 1) rectangle := h
  have hl := SU2QuaternionAuxiliaryLiftAlgebra.lift_coeff 1 hp
  change RatPolyCoeffEqv (liftHead (characterPolynomial (leftPath ⋄ rightPath).scalar 1))
    (liftHead rectangle) at hl
  rw [show liftHead (characterPolynomial (leftPath ⋄ rightPath).scalar 1) =
      characterPolynomial (liftQuaternion (leftPath ⋄ rightPath)).scalar 1 from lift_smul 2 _,
    lift_mul] at hl
  exact hl

/-- Exact propagation of the literal adjacent pair, with its singlet rectangle
and its quadratic channel BOTH retained. This is not full-action integration. -/
theorem adjacent_heat_transmission (tailBlocks : Nat) (hb : 7 ≤ tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) sourceAdjacentProduct) (liftHead r)) ≈
      quaternionHaar tailBlocks (polyMul (adjacentImage w) r) := by
  have hi : RatPolyCoeffEqv
      (pathImage w (liftQuaternion leftPath) (liftQuaternion rightPath)) (adjacentImage w) :=
    (target_pair_pin.smul _).add (rectangle_pin.smul _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((source_pair_pin.mul_left _).mul_right _))
    (Q'.eqv_trans _ _ _
      (path_heat_transmission tailBlocks (by omega) w K hK _ _ r)
      (haar_of_coeff (hi.mul_right r)))

attribute [local irreducible] adjacentProduct rectangle sourceAdjacentProduct

/-- Signed shared-link defect after subtracting the two degree-one
multipliers, w^3*w^3=w^6. This is NOT the global connected correlation.
The first coefficient is (radial-transverse)/4; no absolute values erase
its negative sign for 0<w<1. Six other kinetic integrations are not asserted here. -/
def sharedDefectImage (w : Q') : RatPoly :=
  polyAdd
    (polySmul ((radialRate w + -(transverseRate w)) * SU2QuaternionHeadLinearHaar.quarter)
      adjacentProduct)
    (polySmul (transverseRate w * schurFactor) (liftHead rectangle))

theorem sharedDefectImage_channels (w : Q') :
    RatPolyCoeffEqv (polyAdd (adjacentImage w) (polySmul (-(qpow w 6)) adjacentProduct))
      (sharedDefectImage w) := by
  have hc : qpow w 8 + -(qpow w 6) ≈
      (radialRate w + -(transverseRate w)) * SU2QuaternionHeadLinearHaar.quarter := by
    have hd : radialRate w + -(transverseRate w) ≈ (4 : Q') * (qpow w 8 + -(qpow w 6)) :=
      poly_identity_of_normal_eq
        (.add (.add (.add (.const 1) (.mul (.const 3) (.var 0)))
          (.neg (.mul (.const 4) (.var 1)))) (.neg (.add (.const 1) (.neg (.var 0)))))
        (.mul (.const 4) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => qpow w 8 | _ => qpow w 6)
    have hs : ((4 : Q') * (qpow w 8 + -(qpow w 6))) * SU2QuaternionHeadLinearHaar.quarter ≈
        (qpow w 8 + -(qpow w 6)) * (4 * SU2QuaternionHeadLinearHaar.quarter) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.var 0) (.mul (.const 4) (.var 1)))
        (by decide) (fun | 0 => qpow w 8 + -(qpow w 6) | _ => SU2QuaternionHeadLinearHaar.quarter)
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hd)
      (Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : (4 : Q')*SU2QuaternionHeadLinearHaar.quarter ≈ 1))
        (Q'.mul_one_eqv _))))
  have hs (a b c : RatPoly) : RatPolyCoeffEqv (polyAdd (polyAdd a b) c) (polyAdd (polyAdd a c) b) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => a | 1 => b | _ => c)
  exact (hs _ _ _).trans
    (((RatPolyCoeffEqv.add_smul_same _ _ _).trans
      (RatPolyCoeffEqv.smul_coefficient hc _)).add (RatPolyCoeffEqv.refl _))

/-- Exact signed subtraction on the SAME retained pairing. The output is a
two-channel polynomial, not a nonnegativity claim for a signed test. -/
theorem adjacent_shared_defect (tailBlocks : Nat) (hb : 7 ≤ tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) sourceAdjacentProduct) (liftHead r)) +
        -(qpow w 6 * quaternionHaar tailBlocks (polyMul adjacentProduct r)) ≈
      quaternionHaar tailBlocks (polyMul (sharedDefectImage w) r) := by
  have hp : quaternionHaar tailBlocks
      (polyMul (polyAdd (adjacentImage w) (polySmul (-(qpow w 6)) adjacentProduct)) r) ≈
      quaternionHaar tailBlocks (polyMul (adjacentImage w) r) +
        -(qpow w 6 * quaternionHaar tailBlocks (polyMul adjacentProduct r)) := by
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
          (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) (Q'.neg_mul_eqv _ _))))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (adjacent_heat_transmission tailBlocks hb w K hK r) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hp)
      (haar_of_coeff ((sharedDefectImage_channels w).mul_right r)))

end YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat

#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.scalarSource
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.scalarTarget
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.scalarImage
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.scalar_heat_transmission
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.pathSource
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.pathTarget
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.pathImage
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.path_heat_transmission
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.sourceAdjacentProduct
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.adjacentImage
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.adjacent_heat_transmission
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.sharedDefectImage
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.sharedDefectImage_channels
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteHeat.adjacent_shared_defect
