/-
# Original connected fusion with signed observations on BOTH sides

The left source is the actual observed window f, dominated by a*g with
g = g_(m+Lleft); it need not be positive or independent of the fused face.
Every connected determinant uses U = T g and its ORIGINAL right-window
partition. Fusion retains c_1*D(T f,U), as well as the full signed bulk.

The remaining two cutoff-boundary terms have an explicit relative error
cutoff depending only on nome, the two certified observable caps and the
requested tolerance. Width, both boundary depths and both window lengths
do not occur in that cutoff. No decay estimate for the coupled baseline
and bulk, repeated-fusion bound, or continuum statement is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
open YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource
open YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary
  (boundaryTolerance relativeBoundaryCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeatFusionResidual (bulkResidual boundaryResidual)
open YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks inputNumerator inputPartition
  transferStep terminalMessage observedMessage retainedMessage

/-- The original connected residual AFTER keeping the baseline and bulk
coupled. The baseline message is T f, not the unobserved T g. -/
def observedFusionError (w : Q') (K width m Lleft Lright n : Nat)
    (face : Z4Plaq) (p psi : RatPoly) : Q' :=
  let f := observedMessage w K width m Lleft p
  let U := transferStep w K width (terminalMessage w K width (m+Lleft))
  let A := transferStep w K width f
  let F := transferStep w K width (polyMul f (characterPolynomial (plaquette width face).scalar 1))
  let B := retainedMessage w K width face f (bulkResidual w K (plaquette width face).scalar)
  let J := fun h => inputNumerator w K width Lright n h psi
  let Z := inputPartition w K width Lright n
  let D := fun h => J h*Z U + -(Z h*J U)
  D F + -(coeffW w 1 * D A + D B)

private theorem subtract_sum {a b c : Q'} (h : a ≈ b+c) : a + -b ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h (Q'.eqv_refl _))
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => b | _ => c))

private theorem determinant_error (jf zf ja za jb zb je ze ju zu c : Q')
    (hj : jf + (-c)*ja ≈ jb+je) (hz : zf + (-c)*za ≈ zb+ze) :
    (jf*zu + -(zf*ju)) + -(c*(ja*zu + -(za*ju)) + (jb*zu + -(zb*ju))) ≈
      je*zu + -(ze*ju) := by
  have he :
      (jf*zu + -(zf*ju)) + -(c*(ja*zu + -(za*ju)) + (jb*zu + -(zb*ju))) ≈
        ((jf+(-c)*ja)+ -jb)*zu + -(((zf+(-c)*za)+ -zb)*ju) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 7)) (.neg (.mul (.var 1) (.var 6))))
        (.neg (.add (.mul (.var 8)
          (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 3) (.var 6)))))
          (.add (.mul (.var 4) (.var 7)) (.neg (.mul (.var 5) (.var 6)))))))
      (.add (.mul (.add (.add (.var 0) (.mul (.neg (.var 8)) (.var 2)))
          (.neg (.var 4))) (.var 7))
        (.neg (.mul (.add (.add (.var 1) (.mul (.neg (.var 8)) (.var 3)))
          (.neg (.var 5))) (.var 6))))
      (by decide)
      (fun | 0 => jf | 1 => zf | 2 => ja | 3 => za | 4 => jb
           | 5 => zb | 6 => ju | 7 => zu | _ => c)
  exact Q'.eqv_trans _ _ _ he
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (subtract_sum hj))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (subtract_sum hz))))

/-- Exact original common-partition identity, valid also at cutoff zero.
The signed left source is the actual earlier observed window. -/
theorem observedFusion_error_pin (w : Q') (K width m Lleft Lright n : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (p psi : RatPoly) :
    let U := transferStep w K width (terminalMessage w K width (m+Lleft))
    let E := retainedMessage w K width face (observedMessage w K width m Lleft p)
      (boundaryResidual w K (plaquette width face).scalar)
    let J := fun h => inputNumerator w K width Lright n h psi
    let Z := inputPartition w K width Lright n
    observedFusionError w K width m Lleft Lright n face p psi ≈ J E*Z U + -(Z E*J U) := by
  let f := observedMessage w K width m Lleft p
  let U := transferStep w K width (terminalMessage w K width (m+Lleft))
  let A := transferStep w K width f
  let F := transferStep w K width (polyMul f (characterPolynomial (plaquette width face).scalar 1))
  let B := retainedMessage w K width face f (bulkResidual w K (plaquette width face).scalar)
  let E := retainedMessage w K width face f (boundaryResidual w K (plaquette width face).scalar)
  let J := fun h => inputNumerator w K width Lright n h psi
  let Z := inputPartition w K width Lright n
  let c := coeffW w 1
  have hp : RatPolyCoeffEqv (polyAdd F (polySmul (-c) A)) (polyAdd B E) :=
    signedSource_fusion w K width face hf f
  have hJ : J F + (-c)*J A ≈ J B+J E :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (inputNumerator_add w K width Lright n F (polySmul (-c) A) psi)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (inputNumerator_smul w K width Lright n (-c) A psi))))
      (Q'.eqv_trans _ _ _ (inputNumerator_congr w K width Lright n hp psi)
        (inputNumerator_add w K width Lright n B E psi))
  have hZ : Z F + (-c)*Z A ≈ Z B+Z E :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (inputPartition_add w K width Lright n F (polySmul (-c) A))
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (inputPartition_smul w K width Lright n (-c) A))))
      (Q'.eqv_trans _ _ _ (inputPartition_congr w K width Lright n hp)
        (inputPartition_add w K width Lright n B E))
  exact determinant_error (J F) (Z F) (J A) (Z A) (J B) (Z B)
    (J E) (Z E) (J U) (Z U) c hJ hZ

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem negative_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polySmul c p)) :=
  ((RatPolyCoeffEqv.smul_coefficient
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c)))) p).trans
    (RatPolyCoeffEqv.smul_assoc (-1) c p).symm).trans (smul_neg _)

/-- Quantitative connected bound with both observed windows retained.
Only nome, cutoff and certified caps occur in the displayed coefficient. -/
theorem observedFusion_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m Lleft Lright n : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    {p psi : RatPoly} {a c : Q'}
    (Ileft : Interval ((Lleft+1)*(N width)) p a)
    (Iright : Interval ((Lright+1)*(N width)) psi c) :
    let U := transferStep w K width (terminalMessage w K width (m+Lleft))
    let Z := inputPartition w K width Lright n U
    headFloor w * Q'.abs (observedFusionError w K width m Lleft Lright n face p psi) ≤
      (2*(a*c)*boundaryCap w K)*(Z*Z) := by
  let g := terminalMessage w K width (m+Lleft)
  let u := transferStep w K width g
  let v := erasedMessage w K width (m+Lleft) face
  let f := observedMessage w K width m Lleft p
  let e := retainedMessage w K width face f (boundaryResidual w K (plaquette width face).scalar)
  let Z := inputPartition w K width Lright n u
  have hg := terminalMessage_supported w K width (m+Lleft)
  have hsource := observedMessage_supported w K width m Lleft Ileft.support
  let Iedge := boundaryInterval (Q'.le_of_lt hw0)
    (.scalar (plaquette_supported width (N width) (Nat.le_refl _) face)
      (plaquette_unit width (N width) (Nat.le_refl _) face)) K
  let C := observedMessage_comparison hw0 hw1 K width hK m Lleft Ileft
  let D := retainedMessage_comparison hw0 hw1 K width hK (m+Lleft) face
    hsource C.1 C.2 Iedge
  have Q : Certificate (N width)
      (polyAdd (polySmul (a*boundaryCap w K) v) (polySmul (-1) e)) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (smul_neg _)) D.2
  have H : Certificate (N width) (polyAdd u (polySmul (-(headFloor w)) v)) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (negative_smul _ _))
      (originalMessage_floor hw0 hw1 K width hK (m+Lleft) face hf)
  have hb := inputCovariance_relative_bound hw0 hw1 K width hK Lright n
    (transferStep_supported w K width hg)
    (erasedMessage_supported w K width (m+Lleft) face)
    (retainedMessage_supported w K width face hsource Iedge.support)
    (transferStep_certificate hw0 hw1 K width hK hg
      (terminalMessage_certificate hw0 hw1 K width hK (m+Lleft)))
    (erasedMessage_certificate hw0 hw1 K width hK (m+Lleft) face)
    D.1 Q H Iright (Q'.mul_nonneg _ _ Ileft.nonnegative Iedge.nonnegative)
    (Q'.le_of_lt (headFloor_positive hw0 hw1))
  have he := observedFusion_error_pin w K width m Lleft Lright n face hf p psi
  have hc : (2*c*(a*boundaryCap w K))*(Z*Z) ≈
      (2*(a*c)*boundaryCap w K)*(Z*Z) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2))) (.var 3))
      (.mul (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 2)) (.var 3))
      (by decide) (fun | 0 => a | 1 => c | 2 => boundaryCap w K | _ => Z*Z)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (headFloor w) _ _ (Q'.abs_eqv_congr he)))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hc))

private theorem scale_positive (b : Q') (hb : (0 : Q') ≤ b) : (0 : Q') < 2*b+1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 (2*b)
      (Q'.mul_nonneg _ _ (by decide) hb)) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

-- The existing cutoff uses 2*b+1, so zero observable caps cause no division.
private theorem tolerance_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (b : Q') (hb : (0 : Q') ≤ b) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (2*b)*boundaryTolerance w b hb epsilon ≤ epsilon*headFloor w := by
  let r := Q'.recipPos (2*b+1) (scale_positive b hb)
  have hr : (2*b)*r ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ r
      (Q'.add_le_self_of_nonneg (2*b) 1 Q'.zero_le_one)
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _))
  have heq : (2*b)*boundaryTolerance w b hb epsilon ≈
      (epsilon*headFloor w)*((2*b)*r) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => 2*b | 1 => epsilon*headFloor w | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hr
        (Q'.le_of_lt (Q'.mul_pos he (headFloor_positive hw0 hw1))))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-- An explicit late cutoff for the ACTUAL connected error, with the same
original partition squared. No width or time parameter enters the cutoff. -/
theorem observedFusion_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (K width m Lleft Lright n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    {p psi : RatPoly} {a c : Q'}
    (Ileft : Interval ((Lleft+1)*(N width)) p a)
    (Iright : Interval ((Lright+1)*(N width)) psi c)
    (hK : relativeBoundaryCutoff w (a*c)
      (Q'.mul_nonneg _ _ Ileft.nonnegative Iright.nonnegative) epsilon ≤ K) :
    let U := transferStep w K width (terminalMessage w K width (m+Lleft))
    let Z := inputPartition w K width Lright n U
    Q'.abs (observedFusionError w K width m Lleft Lright n face p psi) ≤ epsilon*(Z*Z) := by
  let b := a*c
  have hb : (0 : Q') ≤ b := Q'.mul_nonneg _ _ Ileft.nonnegative Iright.nonnegative
  have hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have htail : boundaryCutoff w (boundaryTolerance w b hb epsilon) ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) hK
  let U := transferStep w K width (terminalMessage w K width (m+Lleft))
  let Z := inputPartition w K width Lright n U
  have htpos : (0 : Q') < boundaryTolerance w b hb epsilon :=
    Q'.mul_pos (Q'.mul_pos he (headFloor_positive hw0 hw1)) (Q'.recipPos_pos _ _)
  have hcap := boundaryCap_small hw0 hw1 (boundaryTolerance w b hb epsilon) htpos K htail
  have hrate : 2*b*boundaryCap w K ≤ epsilon*headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (2*b) hcap (Q'.mul_nonneg _ _ (by decide) hb))
      (tolerance_budget hw0 hw1 b hb epsilon he)
  have hbound := observedFusion_bound hw0 hw1 K width hhead m Lleft Lright n face hf Ileft Iright
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ (Z*Z) hrate (SumOfSquares.q_mul_self_nonneg Z)
  have hp : (epsilon*headFloor w)*(Z*Z) ≈ headFloor w*(epsilon*(Z*Z)) :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => epsilon | 1 => headFloor w | _ => Z*Z)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hbound (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hp)))
    (headFloor_positive hw0 hw1)

#print axioms observedFusionError
#print axioms observedFusion_error_pin
#print axioms observedFusion_bound
#print axioms observedFusion_small

end YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionBoundary
