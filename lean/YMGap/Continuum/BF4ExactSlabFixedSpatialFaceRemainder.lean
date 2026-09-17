/-
# A single separated face, with the full original terminal source retained

Delete exactly one selected factor from the original spatial heat product.
The remaining product and the actual terminal message are constructed positive
at the existing all-nome cutoff. Applying the unchanged kinetic map gives
two-sided comparison certificates for any bounded signed probe, and a lower
comparison with the ORIGINAL next terminal message. No independence, changed
partition, bulk contraction, or gap estimate is assumed or concluded.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported plaquette_unit faceCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (heatFace_supported heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHeads_certificate)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks terminalMessage

/-- The original ordered list with exactly one occurrence erased. -/
def remainingSpatialWeight (w : Q') (K width : Nat) (face : Z4Plaq) : RatPoly :=
  polynomialProduct (fun p => heatPrefix w K (plaquette width p).scalar)
    ((spatialFaces width).erase face)

private theorem erase_perm (face : Z4Plaq) :
    ∀ {faces : List Z4Plaq}, face ∈ faces → faces.Perm (face :: faces.erase face)
  | [], h => False.elim (List.not_mem_nil h)
  | p::ps, h => by
      by_cases he : p = face
      · subst p
        rw [List.erase_cons_head]
      · rw [List.erase_cons_tail (a := face) (b := p) (by simp [he])]
        have ht := (List.mem_cons.mp h).resolve_left (fun h => he h.symm)
        exact (List.Perm.cons p (erase_perm face ht)).trans (List.Perm.swap face p _)

/-- Coefficient-sensitive splitting of the literal original spatial action. -/
theorem spatialWeight_split (w : Q') (K width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv (spatialWeight w K width)
      (polyMul (heatPrefix w K (plaquette width face).scalar)
        (remainingSpatialWeight w K width face)) := by
  unfold spatialWeight remainingSpatialWeight
  exact polynomialProduct_perm _ (erase_perm face hf)

theorem remainingSpatialWeight_supported (w : Q') (K width : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (N width) (remainingSpatialWeight w K width face) :=
  heatProduct_supported w K width _

private def heatProduct_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (faces : List Z4Plaq) → Certificate (N width)
      (polynomialProduct (fun p => heatPrefix w K (plaquette width p).scalar) faces)
  | [] => .one _
  | p::ps => (faceCertificate hw0 hw1 K width (N width) (Nat.le_refl _) p hK).mul
      (heatProduct_certificate hw0 hw1 K width hK ps)

def remainingSpatialWeight_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (face : Z4Plaq) :
    Certificate (N width) (remainingSpatialWeight w K width face) :=
  heatProduct_certificate hw0 hw1 K width hK _

/-- The full retained action times the actual, cutoff-dependent terminal message. -/
def remainderSource (w : Q') (K width n : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul (remainingSpatialWeight w K width face) (terminalMessage w K width n)

theorem remainderSource_supported (w : Q') (K width n : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (N width) (remainderSource w K width n face) :=
  supported_polyMul (remainingSpatialWeight_supported w K width face)
    (terminalMessage_supported w K width n)

def remainderSource_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq) :
    Certificate (N width) (remainderSource w K width n face) :=
  (remainingSpatialWeight_certificate hw0 hw1 K width hK face).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)

def erasedMessage (w : Q') (K width n : Nat) (face : Z4Plaq) : RatPoly :=
  productMap (N width) w K (activeBlocks width) (remainderSource w K width n face)

def remainderMessage (w : Q') (K width n : Nat) (face : Z4Plaq) (probe : RatPoly) : RatPoly :=
  productMap (N width) w K (activeBlocks width)
    (polyMul (remainderSource w K width n face) probe)

theorem erasedMessage_supported (w : Q') (K width n : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (N width) (erasedMessage w K width n face) :=
  productMap_supported _ w K _ (activeBlocks_lt width) (remainderSource_supported w K width n face)

theorem remainderMessage_supported (w : Q') (K width n : Nat) (face : Z4Plaq)
    {probe : RatPoly} (hp : SupportedQuaternionBlocks (N width) probe) :
    SupportedQuaternionBlocks (N width) (remainderMessage w K width n face probe) :=
  productMap_supported _ w K _ (activeBlocks_lt width)
    (supported_polyMul (remainderSource_supported w K width n face) hp)

theorem remainderMessage_one (w : Q') (K width n : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (remainderMessage w K width n face polyOne) (erasedMessage w K width n face) :=
  productMap_congr _ w K _ (RatPolyCoeffEqv.mul_one _)

private def kinetic_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (P : Certificate (N width) p) :
    Certificate (N width) (productMap (N width) w K (activeBlocks width) p) := by
  change Certificate (N width) (kernelMap (N width)
    (polynomialProduct _ (activeBlocks width)) p)
  rw [← kineticWeight_eq_indexedProduct]
  exact partialHaarHeads_certificate (N width) (N width)
    ((kineticCertificate hw0 hw1 K width hK).mul (certificate_extend (N width) hp P))

def erasedMessage_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq) :
    Certificate (N width) (erasedMessage w K width n face) :=
  kinetic_certificate hw0 hw1 K width hK (remainderSource_supported w K width n face)
    (remainderSource_certificate hw0 hw1 K width hK n face)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem map_neg (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (productMap (N width) w K (activeBlocks width) (polyNeg p))
      (polyNeg (productMap (N width) w K (activeBlocks width) p)) :=
  (productMap_congr _ w K _ (smul_neg p).symm).trans
    ((kernelMap_smul _ _ (-1) p).trans (smul_neg _))

private theorem weighted_cap (s : RatPoly) (d : Q') :
    RatPolyCoeffEqv (polyMul s (cap d)) (polySmul d s) :=
  (RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left d s)

private theorem map_weighted_lower (w : Q') (K width : Nat) (s p : RatPoly) (d : Q') :
    RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width) (polyMul s (polyAdd (cap d) p)))
      (polyAdd (polySmul d (productMap (N width) w K (activeBlocks width) s))
        (productMap (N width) w K (activeBlocks width) (polyMul s p))) :=
  (productMap_congr _ w K _ (RatPolyCoeffEqv.mul_add_right _ _ _)).trans
    ((productMap_add _ w K _ _ _).trans
      (((productMap_congr _ w K _ (weighted_cap s d)).trans
        (kernelMap_smul _ _ d s)).add (.refl _)))

private theorem map_weighted_sub (w : Q') (K width : Nat) (s p q : RatPoly) :
    RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width) (polyMul s (polyAdd p (polyNeg q))))
      (polyAdd (productMap (N width) w K (activeBlocks width) (polyMul s p))
        (polyNeg (productMap (N width) w K (activeBlocks width) (polyMul s q)))) := by
  have hn : RatPolyCoeffEqv (polyMul s (polyNeg q)) (polyNeg (polyMul s q)) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun i => if i = 0 then s else q)
  exact (productMap_congr _ w K _ ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
    ((RatPolyCoeffEqv.refl _).add hn))).trans
    ((productMap_add _ w K _ _ _).trans ((RatPolyCoeffEqv.refl _).add (map_neg w K width _)))

/-- Positive-pair lower comparison for any bounded signed probe, not only characters. -/
def remainderMessage_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    {probe : RatPoly} {d : Q'} (I : Interval (N width) probe d) :
    Certificate (N width) (polyAdd (polySmul d (erasedMessage w K width n face))
      (remainderMessage w K width n face probe)) :=
  .ofCoeff (map_weighted_lower w K width _ probe d).symm
    (kinetic_certificate hw0 hw1 K width hK
      (supported_polyMul (remainderSource_supported w K width n face)
        (supported_add (supported_smul (supported_one _) d) I.support))
      ((remainderSource_certificate hw0 hw1 K width hK n face).mul I.lower))

/-- Upper comparison retains the complete original shared-variable source. -/
def remainderMessage_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    {probe : RatPoly} {d : Q'} (I : Interval (N width) probe d) :
    Certificate (N width) (polyAdd (polySmul d (erasedMessage w K width n face))
      (polyNeg (remainderMessage w K width n face probe))) := by
  have he := (map_weighted_sub w K width (remainderSource w K width n face) (cap d) probe).trans
    (((productMap_congr _ w K _ (weighted_cap _ d)).trans
      (kernelMap_smul _ _ d _)).add (.refl _))
  exact .ofCoeff he.symm
    (kinetic_certificate hw0 hw1 K width hK
      (supported_polyMul (remainderSource_supported w K width n face)
        (supported_add (supported_smul (supported_one _) d) (support_neg I.support)))
      ((remainderSource_certificate hw0 hw1 K width hK n face).mul I.upper))

/-- Reinserting the separated face recovers the literal original first message. -/
theorem originalMessage_pin (w : Q') (K width n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv (transferStep w K width (terminalMessage w K width n))
      (remainderMessage w K width n face (heatPrefix w K (plaquette width face).scalar)) := by
  have hprod : transferStep w K width (terminalMessage w K width n) =
      productMap (N width) w K (activeBlocks width)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n)) := by
    unfold transferStep step productMap kernelMap
    rw [kineticWeight_eq_indexedProduct]
    rfl
  rw [hprod]
  exact productMap_congr _ w K _ (((spatialWeight_split w K width face hf).mul_right _).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
      (fun | 0 => heatPrefix w K (plaquette width face).scalar
           | 1 => remainingSpatialWeight w K width face
           | _ => terminalMessage w K width n)))

/-- The single original heat floor compares the erased source to Tg_n, with
no width, terminal-depth, or cutoff count in the coefficient. -/
def originalMessage_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    Certificate (N width)
      (polyAdd (transferStep w K width (terminalMessage w K width n))
        (polyNeg (polySmul (headFloor w) (erasedMessage w K width n face)))) := by
  let p := heatPrefix w K (plaquette width face).scalar
  let s := remainderSource w K width n face
  have H := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (plaquette_supported width (N width) (Nat.le_refl _) face)
    (plaquette_unit width (N width) (Nat.le_refl _) face) K hK
  have he := (map_weighted_sub w K width s p (cap (headFloor w))).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
      ((productMap_congr _ w K _ (weighted_cap s (headFloor w))).trans
        (kernelMap_smul _ _ (headFloor w) s))))
  exact .ofCoeff
    (((originalMessage_pin w K width n face hf).add (.refl _)).trans he.symm)
    (kinetic_certificate hw0 hw1 K width hK
      (supported_polyMul (remainderSource_supported w K width n face)
        (supported_add (heatFace_supported w K width face)
          (support_neg (supported_smul (supported_one _) (headFloor w)))))
      ((remainderSource_certificate hw0 hw1 K width hK n face).mul H))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainingSpatialWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.spatialWeight_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainingSpatialWeight_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainingSpatialWeight_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderSource
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderSource_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderSource_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.erasedMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.erasedMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderMessage_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.erasedMessage_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderMessage_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.remainderMessage_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.originalMessage_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder.originalMessage_floor
