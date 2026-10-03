/-
# Sharp coordinate covariance for the literal conditional relative heat

The source is arbitrary and signed. Only the input quaternion is integrated;
the output quaternion and all other spectators stay shared. The actual
two-copy wedge certificate, normalization and degree-one/two transmission
construct the polynomial certificate
  ((1-w^8)/4) [P(q^2)-(Pq)^2] - [P(q x_i)-(Pq)w^3 y_i]^2.
No source independence, pointwise positivity rule or covariance bound is
assumed. Output-link independence is needed only by the final raw Haar loss
pin. That loss is not interacting OWN variance or an OS norm/scaling budget.
-/

import YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate
import YMGap.Continuum.SU2QuaternionQuadraticHeatProduct
import YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar (partialHaarHead_mul_lift coordinateMoment liftHead_mul)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion (lifted_independent)
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum (heat_vacuum)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction
open YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission (coordinatePair quarter)
open YMGap.Continuum.SU2QuaternionQuadraticHeatProduct (coordinatePair_transmission)
open YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation "A" => partialHaarHead

/-- The computed conditional source loss, not an interacting variance. -/
def sourceLoss (w : Q') (K : Nat) (q : RatPoly) : RatPoly :=
  polyAdd (conditionalHeat w K (polyMul q q))
    (polyNeg (polyMul (conditionalHeat w K q) (conditionalHeat w K q)))

def coordinateCovariance (w : Q') (K : Nat) (q : RatPoly) (i : Fin 4) : RatPoly :=
  polyAdd (conditionalHeat w K (polyMul q (polyVar i.val)))
    (polyNeg (polyMul (conditionalHeat w K q) (polySmul (qpow w 3) (polyVar i.val))))

def coordinateRate (w : Q') : Q' := (1 - qpow w 8) * quarter

private def centered (W p : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (liftHead (A (polyMul W p))))

private theorem supported_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem supported_var (n : Nat) (hn : 0 < n) (i : Fin 4) :
    SupportedQuaternionBlocks n (polyVar i.val) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_singleton]
  have hi := i.isLt
  omega

private theorem partial_neg (p : RatPoly) :
    RatPolyCoeffEqv (A (polyNeg p)) (polyNeg (A p)) := by
  have ht : RatPolyTermwiseEqv (A (polyNeg p)) (polyNeg (A p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.neg_mul_eqv _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem boundary_carrier (n : Nat) (p P : RatPoly)
    (h : ∀ r : RatPoly, quaternionHaar (n+1) (polyMul p (liftHead r)) ≈
      quaternionHaar n (polyMul P r)) : HaarCarrierEqv n (A p) P := by
  intro r
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing n 1 p r))
      (Q'.eqv_trans _ _ _ (h r) (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- Actual conditional normalization under every retained insertion. -/
theorem conditional_normalization (n : Nat) (hn : 0 < n) (w : Q') (K : Nat) :
    HaarCarrierEqv n (A (relativeHeat w K)) polyOne := by
  apply boundary_carrier
  intro r
  exact Q'.eqv_trans _ _ _ (heat_vacuum n hn w K (liftHead r) (lifted_independent r))
    (Q'.eqv_trans _ _ _ (haar_liftBoundary 1 n r)
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul r))))

/-- The original full packet transmits a coordinate, with shared spectators. -/
theorem coordinate_mean (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (hK : 1 ≤ K) (i : Fin 4) :
    HaarCarrierEqv n (conditionalHeat w K (polyVar i.val))
      (polySmul (qpow w 3) (polyVar i.val)) := by
  apply boundary_carrier
  intro r
  exact Q'.eqv_trans _ _ _ (coordinate_transmission n hn w K hK i r)
    (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (quaternionHaar_polySmul _ _ _)))

/-- Exact singlet plus spin-two coordinate square transmission. -/
theorem coordinate_secondMoment (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (hK : 2 ≤ K) (i : Fin 4) :
    HaarCarrierEqv n (conditionalHeat w K (polyMul (polyVar i.val) (polyVar i.val)))
      (polyAdd (polySmul (qpow w 8) (polyMul (polyVar i.val) (polyVar i.val)))
        (polySmul (coordinateRate w) polyOne)) := by
  apply boundary_carrier
  intro r
  have h := coordinatePair_transmission n hn w K hK i i r
  simp only [coordinateMoment] at h
  change _ ≈ qpow w 8 * quaternionHaar n (polyMul (polyMul (polyVar i.val) (polyVar i.val)) r) +
    (1 - qpow w 8) * (quarter * quaternionHaar n r) at h
  have hout : quaternionHaar n (polyMul
      (polyAdd (polySmul (qpow w 8) (polyMul (polyVar i.val) (polyVar i.val)))
        (polySmul (coordinateRate w) polyOne)) r) ≈
      qpow w 8 * quaternionHaar n (polyMul (polyMul (polyVar i.val) (polyVar i.val)) r) +
        (1 - qpow w 8) * (quarter * quaternionHaar n r) := by
    rw [polyMul_add_left_exact]
    refine Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _) (Q'.add_eqv_congr' ?_ ?_)
    · exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
        (quaternionHaar_polySmul _ _ _)
    · exact Q'.eqv_trans _ _ _ (haar_of_coeff
        ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans ((RatPolyCoeffEqv.one_mul r).smul _)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) (Q'.mul_assoc_eqv _ _ _))
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm hout)

private theorem centered_product (n : Nat) (W p q : RatPoly)
    (hW : HaarCarrierEqv n (A W) polyOne) :
    HaarCarrierEqv n (A (polyMul W (polyMul (centered W p) (centered W q))))
      (polyAdd (A (polyMul W (polyMul p q)))
        (polyNeg (polyMul (A (polyMul W p)) (A (polyMul W q))))) := by
  let mp := A (polyMul W p)
  let mq := A (polyMul W q)
  have he : RatPolyCoeffEqv (polyMul W (polyMul (centered W p) (centered W q)))
      (polyAdd
        (polyAdd (polyMul W (polyMul p q)) (polyNeg (polyMul (polyMul W p) (liftHead mq))))
        (polyAdd (polyNeg (polyMul (polyMul W q) (liftHead mp)))
          (polyMul W (liftHead (polyMul mp mq))))) := by
    rw [liftHead_mul]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 3))) (.add (.var 2) (.neg (.var 4)))))
      (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.var 4))))
        (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3)))
          (.mul (.var 0) (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => W | 1 => p | 2 => q | 3 => liftHead mp | _ => liftHead mq)
  have ha := partialHaarHead_congr he
  simp only [partialHaarHead_add] at ha
  have hb : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (A (polyMul W (polyMul p q)))
          (A (polyNeg (polyMul (polyMul W p) (liftHead mq)))))
        (polyAdd (A (polyNeg (polyMul (polyMul W q) (liftHead mp))))
          (A (polyMul W (liftHead (polyMul mp mq))))))
      (polyAdd
        (polyAdd (A (polyMul W (polyMul p q))) (polyNeg (polyMul mp mq)))
        (polyAdd (polyNeg (polyMul mq mp)) (polyMul (A W) (polyMul mp mq)))) :=
    RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      ((partial_neg _).trans (RatPolyCoeffEqv.neg (partialHaarHead_mul_lift _ _))))
    (RatPolyCoeffEqv.add
      ((partial_neg _).trans (RatPolyCoeffEqv.neg (partialHaarHead_mul_lift _ _)))
      (partialHaarHead_mul_lift _ _))
  refine (RatPolyCoeffEqv.haarCarrier (ha.trans hb)).trans ?_
  refine (HaarCarrierEqv.add
    (HaarCarrierEqv.refl _ _)
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      ((HaarCarrierEqv.mul hW (HaarCarrierEqv.refl _ _)).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _))))).trans ?_
  exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (.add (.neg (.mul (.var 2) (.var 1))) (.mul (.var 1) (.var 2))))
    (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
    (by decide) (fun | 0 => A (polyMul W (polyMul p q)) | 1 => mp | _ => mq))

private def heatCertificate (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate (n+1) (relativeHeat w K) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => relativeHeat w K | _ => cap (headFloor w)))
    ((residualCertificate hn hw0 hw1 K hK).add
      (.constant _ (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))

private theorem heat_supported (n : Nat) (hn : 0 < n) (w : Q') (K : Nat) :
    SupportedQuaternionBlocks (n+1) (relativeHeat w K) :=
  SU2QuaternionRelativeHeatPairGeometry.heat_supported (by omega) (by omega) w K

private theorem centered_supported (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (n+1) p) :
    SupportedQuaternionBlocks (n+1) (centered (relativeHeat w K) p) :=
  supported_add hp (supported_neg (lift_supported (conditionalHeat_supported hn w K hp) 1))

/-- The local source loss itself has a constructed original certificate. -/
def sourceLoss_certificate (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (n+1) q) :
    Certificate n (sourceLoss w K q) :=
  .transport (centered_product n (relativeHeat w K) q q (conditional_normalization n hn w K)).symm
    (partialHaarHead_certificate n ((heatCertificate n hn hw0 hw1 K hK).mul
      (.square _ (centered_supported n hn w K hq))))

private theorem qpow_rg (w : Q') : ∀ r, qpow w r = RGTransport.qpow w r
  | 0 => rfl
  | r+1 => congrArg (fun z : Q' => z*w) (qpow_rg w r)

private theorem rate_difference_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : (0 : Q') ≤ qpow w 3*qpow w 3 - qpow w 8 := by
  have hp0 : (0 : Q') ≤ qpow w 6 := by
    rw [qpow_rg]; exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) 6
  have hp2 : qpow w 2 ≤ (1 : Q') := by
    rw [qpow_rg]; exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 2
  have hnon := Q'.mul_nonneg _ _ hp0 (Q'.sub_nonneg_of_le hp2)
  have hpin : qpow w 6*(1-qpow w 2) ≈ qpow w 3*qpow w 3-qpow w 8 :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (qpow_add w 3 3))
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ _)
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (qpow_add w 6 2))))) (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ hnon (Q'.le_of_eqv hpin)

private theorem negative_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p)) (polySmul (-c) p) :=
  (neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c))) p))

private theorem square_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul c p) (polySmul c p))
      (polySmul (c*c) (polyMul p p)) :=
  (RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
    (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans
      (RatPolyCoeffEqv.smul_assoc _ _ _))

/-- The coordinate variance is bounded by (1-w^8)/4 as a certificate,
not by pointwise substitution on the unit sphere. -/
def coordinateVariance_gap_certificate (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : 2 ≤ K) (i : Fin 4) :
    Certificate n (polyAdd (polySmul (coordinateRate w) polyOne)
      (polyNeg (sourceLoss w K (polyVar i.val)))) := by
  let y := polyVar i.val
  let yy := polyMul y y
  let a := qpow w 3
  let b := qpow w 8
  let t := polySmul (coordinateRate w) polyOne
  have hv : HaarCarrierEqv n (sourceLoss w K y)
      (polyAdd (polyAdd (polySmul b yy) t)
        (polyNeg (polyMul (polySmul a y) (polySmul a y)))) :=
    HaarCarrierEqv.add (coordinate_secondMoment n hn w K hK i)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul (coordinate_mean n hn w K (by omega) i)
        (coordinate_mean n hn w K (by omega) i)))
  have he : RatPolyCoeffEqv
      (polyAdd t (polyNeg (polyAdd (polyAdd (polySmul b yy) t)
        (polyNeg (polyMul (polySmul a y) (polySmul a y))))))
      (polyAdd (polyMul (polySmul a y) (polySmul a y)) (polyNeg (polySmul b yy))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.add (.add (.var 1) (.var 0)) (.neg (.var 2)))))
      (.add (.var 2) (.neg (.var 1))) (by decide)
      (fun | 0 => t | 1 => polySmul b yy | _ => polyMul (polySmul a y) (polySmul a y))
  have hc := ((square_smul a y).add (negative_smul b yy)).trans
    (RatPolyCoeffEqv.add_smul_same _ _ _)
  exact .transport ((HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (HaarCarrierEqv.neg hv)).trans
    (RatPolyCoeffEqv.haarCarrier (he.trans hc)))
    (.smul (a*a-b) (rate_difference_nonnegative hw0 hw1)
      (.square y (supported_var n hn i)))

/-- Sharp actual relative-heat coordinate covariance, retaining the full
source and every shared spectator. No unused-output independence is needed. -/
def coordinateCovariance_certificate (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : max (headCutoff w) 2 ≤ K) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (n+1) q) (i : Fin 4) :
    Certificate n (polyAdd (polySmul (coordinateRate w) (sourceLoss w K q))
      (polyNeg (polyMul (coordinateCovariance w K q i) (coordinateCovariance w K q i)))) := by
  have hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have htwo : 2 ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  let W := relativeHeat w K
  let x := polyVar i.val
  let q0 := centered W q
  let x0 := centered W x
  let L := sourceLoss w K q
  let V := sourceLoss w K x
  let C := coordinateCovariance w K q i
  let t := polySmul (coordinateRate w) polyOne
  have hnorm := conditional_normalization n hn w K
  have hL := centered_product n W q q hnorm
  have hV := centered_product n W x x hnorm
  have hC : HaarCarrierEqv n (A (polyMul W (polyMul q0 x0))) C :=
    (centered_product n W q x hnorm).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
        (HaarCarrierEqv.neg (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
          (coordinate_mean n hn w K (by omega) i))))
  have hGram : HaarCarrierEqv n (conditionalGram W q0 x0)
      (polyAdd (polyMul L V) (polyNeg (polyMul C C))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.mul hL hV)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hC hC))
  let PG : Certificate n (polyAdd (polyMul L V) (polyNeg (polyMul C C))) :=
    .transport hGram.symm (conditionalGram_certificate n W q0 x0 (heat_supported n hn w K)
      (centered_supported n hn w K hq)
      (centered_supported n hn w K (supported_var (n+1) (by omega) i))
      (heatCertificate n hn hw0 hw1 K hhead))
  let PL : Certificate n L := sourceLoss_certificate n hn hw0 hw1 K hhead q hq
  let PD : Certificate n (polyAdd t (polyNeg V)) :=
    coordinateVariance_gap_certificate n hn hw0 hw1 K htwo i
  have he : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul L V) (polyNeg (polyMul C C)))
        (polyMul L (polyAdd t (polyNeg V))))
      (polyAdd (polyMul t L) (polyNeg (polyMul C C))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
        (.mul (.var 0) (.add (.var 3) (.neg (.var 1)))))
      (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => L | 1 => V | 2 => C | _ => t)
  exact .ofCoeff (he.trans ((cap_mul_left (coordinateRate w) L).add
      (RatPolyCoeffEqv.refl _))).symm (PG.add (PL.mul PD))

/-- The sharp bound survives any certified action on the retained links. -/
theorem spectator_covariance_bound (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : max (headCutoff w) 2 ≤ K) (q R : RatPoly)
    (hq : SupportedQuaternionBlocks (n+1) q) (PR : Certificate n R) (i : Fin 4) :
    (0 : Q') ≤ quaternionHaar n (polyMul R
      (polyAdd (polySmul (coordinateRate w) (sourceLoss w K q))
        (polyNeg (polyMul (coordinateCovariance w K q i) (coordinateCovariance w K q i))))) :=
  (PR.mul (coordinateCovariance_certificate n hn hw0 hw1 K hK q hq i)).haar_nonnegative

private theorem haar_neg (n : Nat) (p : RatPoly) :
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- Only this raw norm-loss join requires the source to omit the unused
output link. The remaining spectator links are still arbitrary. -/
theorem sourceLoss_raw_pin (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (n+1) q)
    (hd : HasQuaternionBlockDegree 1 0 q) :
    quaternionHaar n (sourceLoss w K q) ≈ quaternionHaar (n+1) (polyMul q q) -
      quaternionHaar n (polyMul (conditionalHeat w K q) (conditionalHeat w K q)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr'
      (conditionalHeat_mean hn w K (supported_polyMul hq hq) (hd.mul hd))
      (haar_neg n _))

end YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.sourceLoss
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinateCovariance
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinateRate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.conditional_normalization
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinate_mean
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinate_secondMoment
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.sourceLoss_certificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinateVariance_gap_certificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.coordinateCovariance_certificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.spectator_covariance_bound
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatCoordinateCovariance.sourceLoss_raw_pin
