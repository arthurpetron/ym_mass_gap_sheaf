/-
# Signed quartic insertion with the ORIGINAL positive terminal source

The OWN odd-marginal center is retained at both endpoints. Symmetric Young
and its explicit square certificates cost sixteen times the original selected
quartic mass, not the raw Haar source norm. The computed original-prefix
cutoff then gives a two-sided budget against the SAME odd partition.
This only bounds this quartic remainder: it is not the complete filtered
response slope, an OWN-variance comparison, or a survival/scaling theorem.
-/

import YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff
import YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedQuarticInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatPositive (insertion)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison (selectedInsertion)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin (quarticProfileCoefficient)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound (quarticChordInsertion)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage sourceCharacter oddMass

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem smul_supported {n : Nat} {p : RatPoly}
    (c : Q') (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem gap_supported {n : Nat} {p : RatPoly} (c : Q')
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (gap c p) :=
  supported_add (smul_supported c (supported_one n))
    (neg_supported (supported_polyMul hp hp))

private def lowerBound {n : Nat} {p : RatPoly} {c : Q'}
    (P : SquareBound n p c) : SquareBound (n+n) p c where
  support := fun t ht => Nat.le_trans (P.support t ht) (by omega)
  nonnegative := P.nonnegative
  certificate := certificate_extend n (gap_supported c P.support) P.certificate

private def upperBound {n : Nat} {p : RatPoly} {c : Q'}
    (P : SquareBound n p c) : SquareBound (n+n) (liftBoundary n p) c := by
  have hp := lift_supported P.support n
  have hs := gap_supported c P.support
  have hl := lift_supported hs n
  have hg := gap_supported c hp
  have he : PaddedPolynomialCoeffEqv (n+n)
      (liftBoundary n (gap c p)) (gap c (liftBoundary n p)) := by
    unfold gap cap
    rw [lift_add, lift_smul]
    have hn : RatPolyCoeffEqv (liftBoundary n (polyNeg (polyMul p p)))
        (polyNeg (polyMul (liftBoundary n p) (liftBoundary n p))) := by
      have h := lift_coeff n (QuaternionHaarAngularCarrier.neg_smul (polyMul p p))
      rw [lift_smul, lift_product] at h
      exact h.trans (QuaternionHaarAngularCarrier.neg_smul _).symm
    exact ((lift_one (n+n) n).smul c).add (PaddedPolynomialCoeffEqv.of_coeff hn)
  have hc := carrier_of_supported hg hl (fun r hr => he.symm.haar_insert hg hl r hr)
  exact ⟨hp,P.nonnegative,.transport hc (lift_certificate n P.certificate)⟩

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H n p)))

private theorem cap_integral (n : Nat) (W p : RatPoly) (c : Q') :
    H n (polyMul W (polyAdd (cap c) (polyNeg p))) ≈ c*H n W-H n (polyMul W p) := by
  have he := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
    (by decide) (fun
      | 0 => W
      | 1 => cap c
      | _ => p)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c W))
          (quaternionHaar_polySmul n c W)) (haar_neg n _)))

private theorem cross_upper {n : Nat} {W p q : RatPoly} {c : Q'}
    (B : Certificate n W) (P : SquareBound n p c) (Q : SquareBound n q c) :
    H n (polyMul W (polyMul p q)) ≤ c*H n W := by
  have h := (B.mul (P.cross Q)).haar_nonnegative
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (cap_integral n W _ c)))

private theorem cross_lower {n : Nat} {W p q : RatPoly} {c : Q'}
    (B : Certificate n W) (P : SquareBound n p c) (Q : SquareBound n q c) :
    -(c*H n W) ≤ H n (polyMul W (polyMul p q)) := by
  have h := cross_upper B P.neg Q
  have he : H n (polyMul W (polyMul (polyNeg p) q)) ≈ -(H n (polyMul W (polyMul p q))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.neg (.var 1)) (.var 2)))
      (.neg (.mul (.var 0) (.mul (.var 1) (.var 2)))) (by decide) (fun
        | 0 => W
        | 1 => p
        | _ => q))) (haar_neg n _)
  exact Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h))
    (Q'.le_of_eqv (Q'.neg_neg_eqv _))

private theorem young_upper {n : Nat} {W p q : RatPoly}
    (B : Certificate n W) (hp : SupportedQuaternionBlocks n p)
    (hq : SupportedQuaternionBlocks n q) :
    2*H n (polyMul W (polyMul p q)) ≤
      H n (polyMul W (polyMul p p))+H n (polyMul W (polyMul q q)) := by
  let S := H n (polyMul W (polyMul p q))
  have he := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
    (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (.neg (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2)))))) (by decide) (fun
          | 0 => W
          | 1 => p
          | _ => q)
  have hd : H n (polyMul W (polyMul (polyAdd p (polyNeg q)) (polyAdd p (polyNeg q)))) ≈
      H n (polyMul W (polyMul p p))+H n (polyMul W (polyMul q q))-(2*S) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (quaternionHaar_append n _ _)
          (Q'.eqv_trans _ _ _ (haar_neg n _)
            (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
              (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
                (.mul (.const 2) (.var 0)) (by decide) (fun _ => S)))))))
  have h := (B.mul (Certificate.square (polyAdd p (polyNeg q))
    (supported_add hp (neg_supported hq)))).haar_nonnegative
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hd))

/-- Literal signed bilateral quartic insertion, with the OWN original odd
mean and the entire original endpoint/terminal source at both endpoints. -/
def squareSignedQuarticInsertion {w : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (depth scale : Nat)
    (hwidth : side scale<width) (i : Nat) : Q' :=
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  selectedInsertion w K width depth i
    (polyMul (quarticChordInsertion w K (scalarAt (N width+i) i))
      (polyMul psi (liftBoundary (N width) psi)))

private def selected_weight_certificate {w : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (depth i : Nat)
    (hi : i∈activeBlocks width) :
    Certificate (N width+N width)
      (polyMul
        (polyMul (productHeat (N width) w K (eraseIndex i (activeBlocks width)))
          (polyMul (endpointSource w K width (terminalMessage w K width depth))
            (liftBoundary (N width) (endpointSource w K width (terminalMessage w K width depth)))))
        (quarticChordInsertion w K (scalarAt (N width+i) i))) := by
  let a := endpointSource w K width (terminalMessage w K width depth)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width depth)
  let A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK depth)
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable (N width+i))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable i))
  have hil := activeBlocks_lt width i hi
  have hp : Supported (N width+N width) word :=
    (Supported.coordinate (by omega)).mul (Supported.coordinate (by omega)).conj
  have hu : HaarCarrierEqv (N width+N width) (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate (by omega : N width+i<N width+N width))
    ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans
      (haarNorm_coordinate (by omega : i<N width+N width)))
  have HX : SupportedQuaternionBlocks (N width+N width) (scalarAt (N width+i) i) := hp.scalar
  have HC := QuaternionHaarAllNomeHeatCertificate.prefixCertificate hw0 hw1 hp hu K hK
  have hd := smul_supported (2 : Q') (supported_add (supported_one _ ) (neg_supported HX))
  have HQ : Certificate (N width+N width)
      (quarticChordInsertion w K (scalarAt (N width+i) i)) :=
    Certificate.multiplySquare _ hd HC
  exact ((productHeatCertificate (N width) hw0 hw1 K hK _
      (fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj))).mul
    ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A))).mul HQ

/-- The signed Young bound BEFORE imposing cap sixteen. BOTH actual
endpoint-diagonal quartic insertions remain available for sharper estimates. -/
theorem squareSignedQuarticInsertion_young_upper {w : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (depth scale : Nat)
    (hwidth : side scale<width) (i : Nat) (hi : i∈activeBlocks width) :
    let psi := oddCentered hw0 hw1 K width hK depth
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    let Q := quarticChordInsertion w K (scalarAt (N width+i) i)
    2*squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ≤
      selectedInsertion w K width depth i (polyMul Q (polyMul psi psi))+
        selectedInsertion w K width depth i
          (polyMul Q (polyMul (liftBoundary (N width) psi) (liftBoundary (N width) psi))) := by
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let Q := quarticChordInsertion w K (scalarAt (N width+i) i)
  let B := polyMul
    (polyMul (productHeat (N width) w K (eraseIndex i (activeBlocks width)))
      (polyMul (endpointSource w K width (terminalMessage w K width depth))
        (liftBoundary (N width) (endpointSource w K width (terminalMessage w K width depth))))) Q
  have C : Certificate (N width+N width) B :=
    selected_weight_certificate hw0 hw1 K width hK depth i hi
  let P : SquareBound (N width) psi 16 :=
    paddedSquare_centered_squareBound hw0 hw1 K width hK depth scale hwidth
  have hpair (p r : RatPoly) : selectedInsertion w K width depth i (polyMul Q (polyMul p r)) ≈
      H (N width+N width) (polyMul B (polyMul p r)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (2 : Q') _ _ (hpair psi (liftBoundary (N width) psi))))
    (Q'.le_trans' _ _ _ (young_upper C (lowerBound P).support (upperBound P).support)
      (Q'.ge_of_eqv (Q'.add_eqv_congr' (hpair psi psi)
        (hpair (liftBoundary (N width) psi) (liftBoundary (N width) psi)))))

/-- Two-sided Young bound against the actual selected quartic mass. No
positive-definiteness of the quartic operator is assumed or asserted. -/
theorem squareSignedQuarticInsertion_bounds {w : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (depth scale : Nat)
    (hwidth : side scale<width) (i : Nat) (hi : i∈activeBlocks width) :
    let M := selectedInsertion w K width depth i
      (quarticChordInsertion w K (scalarAt (N width+i) i));
    -(16*M) ≤ squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ∧
      squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ≤ 16*M := by
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let B := polyMul
    (polyMul (productHeat (N width) w K (eraseIndex i (activeBlocks width)))
      (polyMul (endpointSource w K width (terminalMessage w K width depth))
        (liftBoundary (N width) (endpointSource w K width (terminalMessage w K width depth)))))
    (quarticChordInsertion w K (scalarAt (N width+i) i))
  have C : Certificate (N width+N width) B :=
    selected_weight_certificate hw0 hw1 K width hK depth i hi
  let P : SquareBound (N width) psi 16 :=
    paddedSquare_centered_squareBound hw0 hw1 K width hK depth scale hwidth
  have he : squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ≈
      H (N width+N width) (polyMul B (polyMul psi (liftBoundary (N width) psi))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  have hu := cross_upper C (lowerBound P) (upperBound P)
  have hl := cross_lower C (lowerBound P) (upperBound P)
  exact ⟨Q'.le_trans' _ _ _ hl (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hu⟩

/-- Computed all-later ORIGINAL cutoff at q and q*q; the actual signed
insertion is bounded by the SAME odd partition, with no raw source cost.
The near-one guard belongs to the proven heat-profile producer. -/
theorem squareSignedQuarticInsertion_tolerance_bounds {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (depth scale : Nat)
    (hwidth : side scale<width) (i : Nat) (hi : i∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K) :
    let budget := 16*((quarticProfileCoefficient w+epsilon)*oddMass w K width depth);
    -budget ≤ squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ∧
      squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i ≤ budget := by
  have hb := squareSignedQuarticInsertion_bounds hw0 hw1 K width hK depth scale hwidth i hi
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (16 : Q')
    (selectedChordInsertion_le_tolerance hw0 hw1 hw he K width depth i hcut hi) (by decide)
  exact ⟨Q'.le_trans' _ _ _ (Q'.neg_le_neg hm) hb.1, Q'.le_trans' _ _ _ hb.2 hm⟩

/-- Absolute value form of the actual signed quartic budget. This is not
a bound on the full filtered increment or on its ratio to OWN variance. -/
theorem squareSignedQuarticInsertion_abs_le {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (depth scale : Nat)
    (hwidth : side scale<width) (i : Nat) (hi : i∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K) :
    Q'.abs (squareSignedQuarticInsertion hw0 hw1 K width hK depth scale hwidth i) ≤
      16*((quarticProfileCoefficient w+epsilon)*oddMass w K width depth) := by
  have h := squareSignedQuarticInsertion_tolerance_bounds hw0 hw1 hw he
    K width hK depth scale hwidth i hi hcut
  exact Q'.abs_le h.1 h.2

#print axioms squareSignedQuarticInsertion
#print axioms squareSignedQuarticInsertion_young_upper
#print axioms squareSignedQuarticInsertion_bounds
#print axioms squareSignedQuarticInsertion_tolerance_bounds
#print axioms squareSignedQuarticInsertion_abs_le

end YMGap.Continuum.BF4DyadicWilsonSquareSignedQuarticInsertion
