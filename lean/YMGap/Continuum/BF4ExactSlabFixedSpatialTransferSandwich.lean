/-
# Certified rank-one bounds for the actual fixed-spatial transfer

On the original compact two-slice carrier, the complete kinetic product
lies between headFloor^numberOfTemporalFaces and prefixCap^thatSameCount.
Multiplication by the actual head potential V and supported certified input
f, followed by actual partial Haar integration, gives certificates for

  a * H[V*f] <= T f <= b * H[V*f].

The inequalities are in the polynomial Haar-certificate cone, not merely
bounds on the total integral. V stays inside the displayed weighted mass;
there is no independent layer normalization or deletion of spatial factors.
The constants depend on nome and width, not on the late heat cutoff. No
ratio contraction, stationary state, OS identification or gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (temporalFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight relative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- The original kinetic floor, independent of the cutoff. -/
def kineticFloor (w : Q') (width : Nat) : Q' :=
  (headFloor w)^(temporalFaces width).length

/-- The original kinetic cap; spatial factors are kept inside weightedMass. -/
def kineticCap (w : Q') (width : Nat) : Q' :=
  (prefixCap w)^(temporalFaces width).length

/-- The exact head integral, with the actual potential V occurring once. -/
def weightedMass (w : Q') (K width : Nat) (f : RatPoly) : Q' :=
  quaternionHaar (N width) (polyMul (spatialWeight w K width) f)

theorem kineticFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < kineticFloor w width :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

theorem kineticCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (width : Nat) :
    (0 : Q') ≤ kineticCap w width :=
  Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _

private def productCertificate {A : Type} {blocks : Nat} (f : A → RatPoly)
    (F : ∀ i, Certificate blocks (f i)) :
    (ids : List A) → Certificate blocks (polynomialProduct f ids)
  | [] => .one _
  | i::ids => (F i).mul (productCertificate f F ids)

private def productFloorCertificate {A : Type} {blocks : Nat} (f : A → RatPoly)
    (F : ∀ i, Certificate blocks (f i)) (c : Q') (hc : (0 : Q') ≤ c)
    (L : ∀ i, Certificate blocks (polyAdd (f i) (polyNeg (cap c)))) :
    (ids : List A) → Certificate blocks
      (polyAdd (polynomialProduct f ids) (polyNeg (cap (c^ids.length))))
  | [] => .ofCoeff
      (((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
          (by decide) (fun _ => cap 1))) (.constant _ 0 (Q'.le_refl' _))
  | i::ids => .ofCoeff
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul c (c^ids.length)).symm)).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
          (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
            (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
          (by decide) (fun
            | 0 => f i
            | 1 => polynomialProduct f ids
            | 2 => cap c
            | _ => cap (c^ids.length))).trans
          ((RatPolyCoeffEqv.refl _).add
            (cap_mul_left c (polyAdd (polynomialProduct f ids) (polyNeg (cap (c^ids.length))))))))
      (((L i).mul (productCertificate f F ids)).add
        (.smul c hc (productFloorCertificate f F c hc L ids)))

/-- A full polynomial certificate, stronger than the existing weighted scalar floor. -/
def kineticFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width)
      (polyAdd (kineticWeight w K width) (polyNeg (cap (kineticFloor w width)))) :=
  productFloorCertificate _ (fun face => faceCertificate hw0 hw1 K width face hK)
    (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))
    (fun face => faceFloorCertificate hw0 hw1 K width face hK) (temporalFaces width)

private theorem heads_add : ∀ (blocks : Nat) (p q : RatPoly),
    partialHaarHeads blocks (polyAdd p q) =
      polyAdd (partialHaarHeads blocks p) (partialHaarHeads blocks q)
  | 0, _, _ => rfl
  | blocks+1, p, q => by
      simp only [partialHaarHeads, partialHaarHead_add, heads_add blocks]

private theorem head_neg (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyNeg p)) (polyNeg (partialHaarHead p)) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (polyNeg p)) (polyNeg (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.neg_mul_eqv _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem heads_neg : ∀ (blocks : Nat) (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads blocks (polyNeg p)) (polyNeg (partialHaarHeads blocks p))
  | 0, _ => .refl _
  | blocks+1, p =>
      (partialHaarHeads_congr blocks (head_neg p)).trans (heads_neg blocks (partialHaarHead p))

private theorem heads_sub (blocks : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads blocks (polyAdd p (polyNeg q)))
      (polyAdd (partialHaarHeads blocks p) (polyNeg (partialHaarHeads blocks q))) := by
  rw [heads_add]
  exact (RatPolyCoeffEqv.refl _).add (heads_neg blocks q)

private theorem heads_smul : ∀ (blocks : Nat) (c : Q') (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads blocks (polySmul c p))
      (polySmul c (partialHaarHeads blocks p))
  | 0, _, _ => .refl _
  | blocks+1, c, p =>
      (partialHaarHeads_congr blocks (partialHaarHead_smul c p)).trans
        (heads_smul blocks c (partialHaarHead p))

private theorem zero_support_cap : ∀ (p : RatPoly), SupportedQuaternionBlocks 0 p →
    RatPolyCoeffEqv p (cap (quaternionHaar 0 p))
  | [], _ => (RatPolyCoeffEqv.zero_smul polyOne).symm
  | (m,c)::p, hp => by
      have hm : m = [] := List.eq_nil_of_length_eq_zero (by
        have h := hp (m,c) List.mem_cons_self
        change m.length ≤ 4*0 at h
        omega)
      subst m
      intro weight
      have ih := zero_support_cap p (fun t ht => hp t (List.mem_cons_of_mem _ ht)) weight
      change c*weight [] + ratWeightedSum weight p ≈
        ((c*1+quaternionHaar 0 p)*1)*weight [] + 0
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 2))
            (.add (.mul (.mul (.var 1) (.const 1)) (.var 2)) (.const 0)))
          (.add (.mul (.mul (.add (.mul (.var 0) (.const 1)) (.var 1)) (.const 1))
            (.var 2)) (.const 0)) (by decide)
          (fun | 0 => c | 1 => quaternionHaar 0 p | _ => weight []))

/-- Integrating a supported head-only polynomial leaves its exact Haar constant. -/
theorem partialHaarHeads_supported_constant (blocks : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    RatPolyCoeffEqv (partialHaarHeads blocks p) (cap (quaternionHaar blocks p)) := by
  have hs : SupportedQuaternionBlocks 0 (partialHaarHeads blocks p) :=
    partialHaarHeads_supported 0 blocks p (by simpa only [Nat.zero_add] using hp)
  have he : quaternionHaar 0 (partialHaarHeads blocks p) ≈ quaternionHaar blocks p := by
    simpa only [Nat.zero_add] using quaternionHaar_partialHaarHeads 0 blocks p
  exact (zero_support_cap _ hs).trans (RatPolyCoeffEqv.smul_coefficient he polyOne)

private theorem heads_cap_mul (blocks : Nat) (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    RatPolyCoeffEqv (partialHaarHeads blocks (polyMul (cap c) p))
      (cap (c*quaternionHaar blocks p)) :=
  (partialHaarHeads_congr blocks (cap_mul_left c p)).trans
    ((heads_smul blocks c p).trans
      (((partialHaarHeads_supported_constant blocks hp).smul c).trans
        (RatPolyCoeffEqv.smul_assoc c (quaternionHaar blocks p) polyOne)))

theorem weightedMass_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly} (F : Certificate (N width) f) :
    (0 : Q') ≤ weightedMass w K width f :=
  ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul F).haar_nonnegative

/-- Actual T dominates its displayed rank-one floor in the same polynomial cone. -/
def transferStepLowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (F : Certificate (N width) f) :
    Certificate (N width)
      (polyAdd (transferStep w K width f)
        (polyNeg (cap (kineticFloor w width * weightedMass w K width f)))) := by
  let p := polyMul (spatialWeight w K width) f
  have hp : SupportedQuaternionBlocks (N width) p :=
    supported_polyMul (spatialWeight_supported w K width) hf
  let P : Certificate (N width) p :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul F
  let C := partialHaarHeads_certificate (N width) (N width)
    ((kineticFloorCertificate hw0 hw1 K width hK).mul (certificate_extend (N width) hp P))
  have hd : RatPolyCoeffEqv
      (polyMul (polyAdd (kineticWeight w K width) (polyNeg (cap (kineticFloor w width)))) p)
      (polyAdd (polyMul (kineticWeight w K width) p)
        (polyNeg (polyMul (cap (kineticFloor w width)) p))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => kineticWeight w K width | 1 => cap (kineticFloor w width) | _ => p)
  exact Certificate.ofCoeff
    ((partialHaarHeads_congr (N width) hd).trans
      ((heads_sub (N width) _ _).trans ((RatPolyCoeffEqv.refl _).add
        (RatPolyCoeffEqv.neg (heads_cap_mul (N width) (kineticFloor w width) hp))))).symm C

/-- The corresponding cap keeps precisely the same V-weighted mass. -/
def transferStepUpperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (F : Certificate (N width) f) :
    Certificate (N width)
      (polyAdd (cap (kineticCap w width * weightedMass w K width f))
        (polyNeg (transferStep w K width f))) := by
  let p := polyMul (spatialWeight w K width) f
  have hp : SupportedQuaternionBlocks (N width) p :=
    supported_polyMul (spatialWeight_supported w K width) hf
  let P : Certificate (N width) p :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul F
  let C := partialHaarHeads_certificate (N width) (N width)
    ((kineticInterval hw0 hw1 K width).upper.mul (certificate_extend (N width) hp P))
  have hd : RatPolyCoeffEqv
      (polyMul (polyAdd (cap (kineticCap w width)) (polyNeg (kineticWeight w K width))) p)
      (polyAdd (polyMul (cap (kineticCap w width)) p)
        (polyNeg (polyMul (kineticWeight w K width) p))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => cap (kineticCap w width) | 1 => kineticWeight w K width | _ => p)
  exact Certificate.ofCoeff
    ((partialHaarHeads_congr (N width) hd).trans
      ((heads_sub (N width) _ _).trans
        ((heads_cap_mul (N width) (kineticCap w width) hp).add (RatPolyCoeffEqv.refl _)))).symm C

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.kineticFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.kineticCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.weightedMass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.kineticFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.kineticCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.kineticFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.partialHaarHeads_supported_constant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.weightedMass_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.transferStepLowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich.transferStepUpperCertificate
