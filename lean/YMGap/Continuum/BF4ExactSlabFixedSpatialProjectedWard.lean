/-
# Integrated projected-source Ward pairing on the ORIGINAL odd marginal

The original weight is V*g_n*g_(n+1), not q*P(q) as a polynomial.  For a
padded signed spatial family, inactive projection transports precisely the
Haar tests needed by the full Casimir Ward identity.  Consequently its
INTEGRATED residual equals the auxiliary q*P(q) gradient pairing with the
original mean.  No coefficientwise weight or derivative transport, sign,
smallness, or continuum scaling is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
  (angular_moment_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (wardResidual normalizedWardResidual marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage marginalWeight projectedEndpointSource

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term hterm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hterm
  exact hp s hs

/-- The auxiliary two-endpoint polynomial; it is not the original marginal. -/
def projectedPairWeight (w : Q') (K width n : Nat) : RatPoly :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  polyMul q (productMap (N width) w K (List.range (N width)) q)

/-- Its moment is the original moment only against the specified independent
test. This is a Haar identity, not polynomial equality of weights. -/
private theorem projected_pair_moment (w : Q') (K width n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p) :
    H (N width) (polyMul (marginalWeight w K width n) p) ≈
      H (N width) (polyMul (projectedPairWeight w K width n) p) := by
  have h := oddMoment_projected_source w K width n p hp hind
  exact Q'.eqv_trans _ _ _ h (by
    unfold sourceMoment projectedPairWeight
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => projectedEndpointSource w K width (terminalMessage w K width n)
        | 1 => p
        | _ => productMap (N width) w K (List.range (N width))
            (projectedEndpointSource w K width (terminalMessage w K width n)))))

private theorem angular_pair_moment (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    totalEnergy (N width) (marginalWeight w K width n) f ≈
      totalEnergy (N width) (projectedPairWeight w K width n) f := by
  have hp (i : Nat) (hi : i < N width) :
      blockEnergy (N width) i (marginalWeight w K width n) f ≈
        blockEnergy (N width) i (projectedPairWeight w K width n) f := by
    unfold blockEnergy
    exact Q'.eqv_trans _ _ _ (angular_moment_pin w K width n f hf hind i hi)
      (by
        unfold sourceMoment projectedPairWeight
        exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 2)) (.var 1))
          (by decide) (fun
            | 0 => projectedEndpointSource w K width (terminalMessage w K width n)
            | 1 => blockAngularSquare i f
            | _ => productMap (N width) w K (List.range (N width))
                (projectedEndpointSource w K width (terminalMessage w K width n)))))
  exact Q'.eqv_trans _ _ _ (totalEnergy_finSum _ _ _)
    (Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ (N width) hp)
      (Q'.eqv_symm (totalEnergy_finSum _ _ _)))

private theorem residual_cancel {A B C D E F : Q'}
    (h₁ : A+B ≈ C) (h₂ : D+E ≈ F) (hA : A ≈ D) (hC : C ≈ F) : B ≈ E := by
  have hb : B ≈ C-A :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.var 1)
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (by decide) (fun | 0 => A | _ => B))
      (Q'.add_eqv_congr' h₁ (Q'.eqv_refl _))
  have he : E ≈ F-D :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.var 1)
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (by decide) (fun | 0 => D | _ => E))
      (Q'.add_eqv_congr' h₂ (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ hb
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hC (Q'.neg_eqv_congr _ _ hA))
      (Q'.eqv_symm he))

/-- The ORIGINAL complete-weight Ward scalar equals the auxiliary projected
source's full angular-gradient pairing. The center comes from the original
odd marginal. Arbitrary signed coefficients and repeated faces are retained. -/
theorem wardResidual_projected_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width coeff qs
    let center := normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n)
    wardResidual hw0 hw1 K width hK n f ≈
      totalResidual (N width) (projectedPairWeight w K width n) f center := by
  dsimp only
  let f := spatialSpan width coeff qs
  let W := marginalWeight w K width n
  let U := projectedPairWeight w K width n
  let center := normalizedMoment (N width) W f
    (marginalMass_positive hw0 hw1 K width hK n)
  let psi := polyAdd f (polySmul (-center) polyOne)
  have hf : SupportedQuaternionBlocks (N width) f := spatialSpan_supported width coeff qs
  have hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f :=
    spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs
  have hpsi : SupportedQuaternionBlocks (N width) psi :=
    supported_add hf (support_smul (supported_one _) (-center))
  have hpsii : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i psi := by
    intro i hi
    exact quaternionBlockIndependent_polyAdd (hind i hi)
      (quaternionBlockIndependent_polySmul (-center)
        (quaternionBlockIndependent_polyOne i))
  have htest : H (N width) (polyMul W (polyMul psi f)) ≈
      H (N width) (polyMul U (polyMul psi f)) :=
    projected_pair_moment w K width n (polyMul psi f)
      (supported_polyMul hpsi hf)
      (fun i hi => quaternionBlockIndependent_polyMul (hpsii i hi) (hind i hi))
  have hcas := spatialSpan_casimir width coeff qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have htarget (V : RatPoly) :
      H (N width) (polyMul (polyMul V psi)
        (activeCasimirPolynomial (List.range (N width)) f)) ≈
        12 * H (N width) (polyMul V (polyMul psi f)) :=
    Q'.eqv_trans _ _ _ (hcas (polyMul V psi))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 12 (polyMul V psi) f))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) 12 _)
          (Q'.mul_eqv_congr_left 12 _ _
            (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V psi f)))))
  have hW : totalEnergy (N width) W f +
      wardResidual hw0 hw1 K width hK n f ≈
        H (N width) (polyMul (polyMul W psi)
          (activeCasimirPolynomial (List.range (N width)) f)) := by
    simpa only [wardResidual, W, f, center, psi] using
      complete_ward_raw (N width) W f center
  have hU := complete_ward_raw (N width) U f center
  have hA := angular_pair_moment w K width n f hf hind
  have hT : H (N width) (polyMul (polyMul W psi)
      (activeCasimirPolynomial (List.range (N width)) f)) ≈
      H (N width) (polyMul (polyMul U psi)
        (activeCasimirPolynomial (List.range (N width)) f)) :=
    Q'.eqv_trans _ _ _ (htarget W)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 12 _ _ htest)
        (Q'.eqv_symm (htarget U)))
  exact residual_cancel hW hU hA hT

/-- Direct adapter for the signed term in `completeCenteredError`, still
normalized by the ORIGINAL odd partition and centered by its own mean. -/
theorem normalizedWardResidual_projected_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width coeff qs
    let center := normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n)
    normalizedWardResidual hw0 hw1 K width hK n f ≈
      totalResidual (N width) (projectedPairWeight w K width n) f center *
        Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n) := by
  dsimp only
  unfold normalizedWardResidual
  exact Q'.mul_eqv_congr_right _ _ _
    (wardResidual_projected_pair hw0 hw1 K hwidth hK n qs coeff hqs)

/-- The actual complete centered error consumes the transported residual
with its ORIGINAL signed coefficient. No favorable sign or smallness is used. -/
theorem completeCenteredError_projected_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width coeff qs
    let center := normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n)
    BF4ExactSlabFixedSpatialCenteredRemainderSquare.completeCenteredError
      hw0 hw1 K width hK n f ≈
      BF4ExactSlabFixedSpatialCenteredRemainderSquare.normalizedCenteredError
        hw0 hw1 K width hK n f -
      ((1 : Q')-w) *
        (totalResidual (N width) (projectedPairWeight w K width n) f center *
          Q'.recipPos (oddMass w K width n)
            (oddMass_positive hw0 hw1 K width hK n)) := by
  dsimp only
  unfold BF4ExactSlabFixedSpatialCenteredRemainderSquare.completeCenteredError
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
      (normalizedWardResidual_projected_pair hw0 hw1 K hwidth hK n qs coeff hqs)))

#print axioms projectedPairWeight
#print axioms wardResidual_projected_pair
#print axioms normalizedWardResidual_projected_pair
#print axioms completeCenteredError_projected_pair

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedWard
