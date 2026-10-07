/-
# Cap-free finite comparison on the original block window

Only support of the original source psi is required. With the existing
finite reciprocal phi=G_k*b and m=1-a*G_k, use the ACTUAL joined source
  eta*lift(phi) + psi*lift(m).
Its determinant, the old signed innovation tower, and the multiplier
square interval construct
  (1+nu)*Nfull + nu*B^2 - (1-eta)*Nlast >= 0,
where nu=mixRate^(2*k)/eta and eta is an explicit positive rational.
The only inverse is that of eta, never of a conditional density. The
source second moment Nfull+B^2 replaces a global observable cap.

Historical variance is retained by the old tower certificate; it is not
called reconstruction error or assumed small. These are finite original
K*V certificates, not completed norms, physical RG, survival or Clay.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationCovariance
import YMGap.Continuum.SU2QuaternionHaarKernelBound
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationRelativeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHeads_certificate)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds (halfOpenAction_certificate)
open YMGap.Continuum.SU2QuaternionConditionalVarianceTower (mean towerWeight tower_mean_pin)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.SU2QuaternionHaarKernelBound
  (kernelMap_congr kernelMap_add kernelMap_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul cap_add)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal multiplierErrorInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeight stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (iterateStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate terminalMessage_mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica (blockWindowWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
  (blockConditionalRatio blockConditionalRatio_supported blockReciprocal
   blockWindowLower blockWindowUpper blockWindowUpper_positive
   blockWindowCertificates blockWindow_radius_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationTower
  (originalInnovationCovariance original_block_ratio_innovation_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem block_terminal (w : Q') (K width n t : Nat) :
    originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n t polyOne).symm

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      originalBlockTransfer w K width 1 (originalBlockTransfer w K width t p) := by
  unfold originalBlockTransfer
  exact iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem mean_congr (heads : Nat) (W : RatPoly) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (mean heads W p) (mean heads W q) :=
  kernelMap_congr heads W h

private theorem mean_cap (heads : Nat) (W : RatPoly) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (mean heads W (polyMul (cap c) p))
      (polyMul (cap c) (mean heads W p)) :=
  (mean_congr heads W (cap_mul_left c p)).trans
    ((kernelMap_smul heads W c p).trans (cap_mul_left c _).symm)

private theorem mean_sub (heads : Nat) (W p q : RatPoly) :
    RatPolyCoeffEqv (mean heads W (polyAdd p (polyNeg q)))
      (polyAdd (mean heads W p) (polyNeg (mean heads W q))) := by
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
    (by decide) (fun | 0 => W | 1 => p | _ => q)
  refine (partialHaarHeads_congr heads hr).trans ?_
  dsimp only [coeffEvalExpr]
  rw [partialHaarHeads_add]
  exact (RatPolyCoeffEqv.refl _).add (partialHaarHeads_neg heads _)

private theorem inner_moment (w : Q') (K width n t : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (mean (t*(N width)) (blockWindowWeight w K width n t) p)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) p)) := by
  unfold mean blockWindowWeight
  exact (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => terminalMessage w K width n
           | 1 => halfOpenAction (N width) (kineticWeight w K width)
               (spatialWeight w K width) t | _ => p))).trans
    (windowMessage_iterate (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n) p)

private theorem inner_mass (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (terminalMessage w K width (n+t)) := by
  rw [← block_terminal w K width n t]
  unfold blockWindowWeight
  exact (partialHaarHeads_congr (t*(N width))
    ((RatPolyCoeffEqv.mul_one (terminalMessage w K width n)).symm.mul_right
      (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t))).trans
    (windowMessage_one (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n))

private theorem outer_moment (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (mean (N width) (stepWeight w K width) p)
      (originalBlockTransfer w K width 1 p) :=
  partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_assoc (kineticWeight w K width) (spatialWeight w K width) p)

private theorem outer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (mean (N width) (stepWeight w K width) p)
      (originalBlockTransfer w K width 1 q) :=
  (mean_congr (N width) (stepWeight w K width) h).trans (outer_moment w K width q)

private theorem joined_moment (w : Q') (K width n t : Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (mean (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width)) p)
      (originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) p)) := by
  rw [block_succ]
  exact (tower_mean_pin (t*(N width)) (N width)
    (blockWindowWeight w K width n t) (stepWeight w K width) p).trans
    (outer_congr w K width (inner_moment w K width n t p))

private theorem joined_mass (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width)))
      (originalBlockTransfer w K width 1 (terminalMessage w K width (n+t))) := by
  unfold towerWeight
  rw [SU2QuaternionConditionalVarianceTower.heads_compose]
  exact (partialHaarHeads_congr (N width)
    ((partialHaarHeads_mul_lift (t*(N width))
      (blockWindowWeight w K width n t) (stepWeight w K width)).trans
      (((inner_mass w K width n t).mul_right (stepWeight w K width)).trans
        (RatPolyCoeffEqv.mul_comm _ _)))).trans (outer_moment w K width _)

private theorem joined_lift (w : Q') (K width n t : Nat) (f : RatPoly) :
    RatPolyCoeffEqv
      (mean (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width))
        (liftBoundary (t*(N width)) f))
      (originalBlockTransfer w K width 1 (polyMul (terminalMessage w K width (n+t)) f)) :=
  (tower_mean_pin (t*(N width)) (N width)
    (blockWindowWeight w K width n t) (stepWeight w K width) _).trans
    (outer_congr w K width
      ((partialHaarHeads_mul_lift (t*(N width)) (blockWindowWeight w K width n t) f).trans
        ((inner_mass w K width n t).mul_right f)))

private theorem joined_probe (w : Q') (K width n t : Nat) (p f : RatPoly) :
    RatPolyCoeffEqv
      (mean (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width))
        (polyMul p (liftBoundary (t*(N width)) f)))
      (originalBlockTransfer w K width 1
        (polyMul (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) p)) f)) :=
  (tower_mean_pin (t*(N width)) (N width)
    (blockWindowWeight w K width n t) (stepWeight w K width) _).trans
    (outer_congr w K width
      ((partialHaarHeads_congr (t*(N width))
        (RatPolyCoeffEqv.mul_assoc (blockWindowWeight w K width n t) p _).symm).trans
        ((partialHaarHeads_mul_lift (t*(N width))
          (polyMul (blockWindowWeight w K width n t) p) f).trans
          ((inner_moment w K width n t p).mul_right f))))

private def centered (heads : Nat) (W p q : RatPoly) : RatPoly :=
  polyAdd (polyMul (partialHaarHeads heads W) (mean heads W (polyMul p q)))
    (polyNeg (polyMul (mean heads W p) (mean heads W q)))

private theorem determinant_add_pin (heads : Nat) (W q r : RatPoly) (eta : Q') :
    RatPolyCoeffEqv (determinant heads W (polyAdd (polySmul eta q) r))
      (polyAdd
        (polyAdd (polyMul (cap eta) (polyMul (cap eta) (determinant heads W q)))
          (polyMul (cap eta) (polyAdd (centered heads W q r) (centered heads W q r))))
        (determinant heads W r)) := by
  let u := cap eta
  let A := partialHaarHeads heads W
  let Q := mean heads W q
  let Z := mean heads W r
  let H := mean heads W (polyMul q q)
  let X := mean heads W (polyMul q r)
  let E := mean heads W (polyMul r r)
  have hsource : RatPolyCoeffEqv (polyAdd (polySmul eta q) r)
      (polyAdd (polyMul u q) r) :=
    (cap_mul_left eta q).symm.add (RatPolyCoeffEqv.refl r)
  have hm := (mean_congr heads W hsource).trans
    ((kernelMap_add heads W _ r).trans
      ((mean_cap heads W eta q).add (RatPolyCoeffEqv.refl Z)))
  have hs : RatPolyCoeffEqv
      (mean heads W (polyMul (polyAdd (polySmul eta q) r) (polyAdd (polySmul eta q) r)))
      (polyAdd (polyAdd (polyMul u (polyMul u H)) (polyMul u (polyAdd X X))) E) := by
    have hr := (hsource.mul hsource).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 1)) (.var 2))
          (.add (.mul (.var 0) (.var 1)) (.var 2)))
        (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
          (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))
          (.mul (.var 2) (.var 2)))
        (by decide) (fun | 0 => u | 1 => q | _ => r))
    refine (mean_congr heads W hr).trans ?_
    exact (kernelMap_add heads W _ _).trans
      (((kernelMap_add heads W _ _).trans
        (((mean_cap heads W eta _).trans
          ((mean_cap heads W eta _).mul_left u)).add
          ((mean_cap heads W eta _).trans
            ((kernelMap_add heads W _ _).mul_left u)))).add
        (RatPolyCoeffEqv.refl E))
  exact (((RatPolyCoeffEqv.refl A).mul hs).add (RatPolyCoeffEqv.neg (hm.mul hm))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 1) (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 4)))
        (.mul (.var 0) (.add (.var 5) (.var 5)))) (.var 6)))
        (.neg (.mul (.add (.mul (.var 0) (.var 2)) (.var 3))
          (.add (.mul (.var 0) (.var 2)) (.var 3)))))
      (.add (.add
        (.mul (.var 0) (.mul (.var 0)
          (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 2) (.var 2))))))
        (.mul (.var 0) (.add
          (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 3))))
          (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 3)))))))
        (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 3) (.var 3)))))
      (by decide) (fun | 0 => u | 1 => A | 2 => Q | 3 => Z | 4 => H | 5 => X | _ => E))

private theorem power_square (rho : Q') (k : Nat) : Q'.eqv (rho^k*rho^k) (rho^(2*k)) := by
  have split (i : Nat) : Q'.eqv (rho^(i+k)) (rho^i*rho^k) := by
    induction i with
    | zero =>
      simpa only [Nat.zero_add, Q'.pow_zero] using Q'.eqv_symm (Q'.one_mul_eqv (rho^k))
    | succ i ih =>
      simp only [Nat.succ_add, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left rho _ _ ih)
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  have h : 2*k = k+k := by omega
  rw [h]
  exact Q'.eqv_symm (split k)

/-- Explicit source-relative loss, with inverse only of the chosen eta. -/
def innovationRelativeLoss {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width k : Nat) (eta : Q') (heta : (0 : Q') < eta) : Q' :=
  (mixRate hw0 hw1 width)^(2*k) * Q'.recipPos eta heta

/-- Actual cap-free comparison: original support is the only source input.
The positive determinant uses psi*lift(1-a*G), not a claimed-small history.
The residual historical certificate from the original tower is preserved. -/
def original_innovation_relativeComparison_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (k : Nat) (eta : Q') (heta : (0 : Q') < eta) :
    let a := terminalMessage w K width (n+t)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    let F := blockNoise w K width (t+1) (terminalMessage w K width n) psi
    let D := blockNoise w K width 1 a phi
    let B := originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) psi)
    let nu := innovationRelativeLoss hw0 hw1 width k eta heta
    Certificate (N width)
      (polyAdd (polyAdd (polySmul (1+nu) F) (polySmul nu (polyMul B B)))
        (polyNeg (polySmul (1-eta) D))) := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let s := originalBlockTransfer w K width t
    (polyMul (terminalMessage w K width n) (polyMul psi psi))
  let G := blockReciprocal hw0 hw1 K width hK n t k
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let m := polyNeg (polyAdd (polyMul a G) (polyNeg polyOne))
  let e := polyAdd b (polyNeg (polyMul a phi))
  let A := originalBlockTransfer w K width 1 a
  let z := originalBlockTransfer w K width 1 e
  let H := originalBlockTransfer w K width 1 (polyMul s (polyMul m m))
  let E := polyAdd (polyMul A H) (polyNeg (polyMul z z))
  let C := originalInnovationCovariance w K width n t psi phi
  let F := blockNoise w K width (t+1) (terminalMessage w K width n) psi
  let D := blockNoise w K width 1 a phi
  let B := originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) psi)
  let rho := mixRate hw0 hw1 width
  let eps := rho^(2*k)
  let inv := Q'.recipPos eta heta
  let u := cap eta
  let v := cap inv
  let d := cap eps
  let W := blockWindowWeight w K width n t
  let R := stepWeight w K width
  let heads := t*(N width)+N width
  let J := towerWeight (t*(N width)) W R
  let q := liftBoundary (t*(N width)) phi
  let r := polyMul psi (liftBoundary (t*(N width)) m)
  have ha := terminalMessage_supported w K width (n+t)
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hs := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
    (supported_polyMul (terminalMessage_supported w K width n) (supported_polyMul hpsi hpsi))
  have hphi := blockConditionalRatio_supported hw0 hw1 K width hK n t hpsi k
  have hG : SupportedQuaternionBlocks (N width) G :=
    QuaternionHaarPositiveWindowInverse.reciprocal_supported ha
      (blockWindowUpper w K width n t)
      (blockWindowUpper_positive hw0 hw1 K width hK n t) k
  have hm : SupportedQuaternionBlocks (N width) m :=
    support_neg (supported_add (supported_polyMul ha hG)
      (support_neg (supported_one (N width))))
  have he := supported_add hb (support_neg (supported_polyMul ha hphi))
  have hz := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) 1 he
  have hem : RatPolyCoeffEqv (polyMul b m) e :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1) (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.const 1)))))
      (.add (.var 1) (.neg (.mul (.var 0) (.mul (.var 2) (.var 1)))))
      (by decide) (fun | 0 => a | 1 => b | _ => G)
  have hsize : (t+1)*(N width) = N width+t*(N width) := by rw [Nat.succ_mul]; omega
  have hbase : SupportedQuaternionBlocks (N width+t*(N width)) W := hsize ▸
    supported_polyMul (support_mono (terminalMessage_supported w K width n)
      (by rw [Nat.succ_mul]; omega))
      (halfOpenAction_supported (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) t)
  have Pbase : Certificate (N width+t*(N width)) W :=
    (certificate_extend (t*(N width)) (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)).mul
      (hsize ▸ halfOpenAction_certificate (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) t)
  have htotal : N width+t*(N width)+N width = N width+heads := by dsimp [heads]; omega
  have PW : Certificate (N width+heads) W :=
    htotal ▸ certificate_extend (N width) hbase Pbase
  have hR : SupportedQuaternionBlocks (N width+N width) R :=
    supported_polyMul (kineticWeight_supported w K width)
      (support_mono (spatialWeight_supported w K width) (by omega))
  have hlift : N width+N width+t*(N width) = N width+heads := by dsimp [heads]; omega
  have PJ : Certificate (N width+heads) J :=
    PW.mul (hlift ▸ lift_certificate (t*(N width)) (stepWeightCertificate hw0 hw1 K width hK))
  have hJ : SupportedQuaternionBlocks (N width+heads) J :=
    supported_polyMul (support_mono hbase (by dsimp [heads]; omega))
      (hlift ▸ lift_supported hR (t*(N width)))
  have hq : SupportedQuaternionBlocks (N width+heads) q :=
    support_mono (lift_supported hphi (t*(N width))) (by dsimp [heads]; omega)
  have hr : SupportedQuaternionBlocks (N width+heads) r :=
    supported_polyMul (support_mono hpsi (by dsimp [heads]; omega))
      (support_mono (lift_supported hm (t*(N width))) (by dsimp [heads]; omega))
  have hA := joined_mass w K width n t
  have hq1 := joined_lift w K width n t phi
  have hq2 : RatPolyCoeffEqv (mean heads J (polyMul q q))
      (originalBlockTransfer w K width 1 (polyMul a (polyMul phi phi))) := by
    dsimp [q]
    rw [← lift_product]
    exact joined_lift w K width n t _
  have hr1 : RatPolyCoeffEqv (mean heads J r) z :=
    (joined_probe w K width n t psi m).trans
      ((outer_moment w K width _).symm.trans (outer_congr w K width hem))
  have hrr : RatPolyCoeffEqv (polyMul r r)
      (polyMul (polyMul psi psi) (liftBoundary (t*(N width)) (polyMul m m))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => psi | _ => liftBoundary (t*(N width)) m)
  have hr2 : RatPolyCoeffEqv (mean heads J (polyMul r r)) H :=
    (mean_congr heads J hrr).trans (joined_probe w K width n t (polyMul psi psi) (polyMul m m))
  have hqr : RatPolyCoeffEqv (polyMul q r)
      (polyMul psi (liftBoundary (t*(N width)) (polyMul phi m))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => psi | 1 => q | _ => liftBoundary (t*(N width)) m)
  have hqr1 : RatPolyCoeffEqv (mean heads J (polyMul q r))
      (originalBlockTransfer w K width 1 (polyMul phi e)) := by
    have hbe : RatPolyCoeffEqv (polyMul b (polyMul phi m)) (polyMul phi e) :=
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => b | 1 => phi | _ => m)).trans (hem.mul_left phi)
    exact (mean_congr heads J hqr).trans
      ((joined_probe w K width n t psi (polyMul phi m)).trans
        ((outer_moment w K width _).symm.trans (outer_congr w K width hbe)))
  have hD : RatPolyCoeffEqv (determinant heads J q) D :=
    (hA.mul hq2).add (RatPolyCoeffEqv.neg (hq1.mul hq1))
  have hE : RatPolyCoeffEqv (determinant heads J r) E :=
    (hA.mul hr2).add (RatPolyCoeffEqv.neg (hr1.mul hr1))
  have hC : RatPolyCoeffEqv (centered heads J q r) C := by
    dsimp [C, originalInnovationCovariance]
    rw [block_terminal]
    exact (hA.mul hqr1).add (RatPolyCoeffEqv.neg (hq1.mul hr1))
  have Pdet := determinant_certificate (N width) heads J
    (polyAdd (polySmul eta q) r) hJ (supported_add (support_smul hq eta) hr) PJ
  have Pyoung : Certificate (N width)
      (polyAdd (polyAdd (polyMul u (polyMul u D)) (polyMul u (polyAdd C C))) E) :=
    Certificate.ofCoeff
      ((determinant_add_pin heads J q r eta).trans
        ((((hD.mul_left u).mul_left u).add ((hC.add hC).mul_left u)).add hE)).symm Pdet
  have hwindow : blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1)))
  have M := QuaternionHaarSignedInterval.Interval.neg
    (multiplierErrorInterval ha (blockWindowUpper_positive hw0 hw1 K width hK n t)
      hwindow (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
      (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k)
  have M' := M.changeCap
    (Q'.pow_eqv_congr (blockWindow_radius_pin hw0 hw1 K width hK n t) k)
  have S := (QuaternionHaarIntervalSecondMoment.Interval.squareBound M').changeCap
    (power_square rho k)
  have Ps : Certificate (N width) s :=
    iterateStep_certificate hw0 hw1 K width hK t _
      (supported_polyMul (terminalMessage_supported w K width n) (supported_polyMul hpsi hpsi))
      ((terminalMessage_certificate hw0 hw1 K width hK n).mul (Certificate.square psi hpsi))
  have hgap : SupportedQuaternionBlocks (N width)
      (polyAdd d (polyNeg (polyMul m m))) :=
    supported_add (support_smul (supported_one (N width)) eps)
      (support_neg (supported_polyMul hm hm))
  have Pgap := partialHaarHeads_certificate (N width) (N width)
    ((stepWeightCertificate hw0 hw1 K width hK).mul
      (certificate_extend (N width) (supported_polyMul hs hgap) (Ps.mul S.certificate)))
  have hp : RatPolyCoeffEqv (mean (N width) R
      (polyMul s (polyAdd d (polyNeg (polyMul m m)))))
      (polyAdd (polyMul d (originalBlockTransfer w K width 1 s)) (polyNeg H)) :=
    (mean_congr (N width) R
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => s | 1 => d | _ => polyMul m m))).trans
      ((mean_sub (N width) R _ _).trans
        (((mean_cap (N width) R eps s).trans
          ((outer_moment w K width s).mul_left d)).add
          (RatPolyCoeffEqv.neg (outer_moment w K width _))))
  have PA : Certificate (N width) A := by
    dsimp [A, a]
    rw [block_terminal]
    exact terminalMessage_certificate hw0 hw1 K width hK _
  have Perror := (PA.mul (Certificate.ofCoeff hp.symm Pgap)).add (Certificate.square z hz)
  have hsecond : RatPolyCoeffEqv (polyMul A (originalBlockTransfer w K width 1 s))
      (polyAdd F (polyMul B B)) := by
    dsimp [F, blockNoise, A, a, s, B]
    simp only [block_succ w K width t, block_terminal w K width n t]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.var 1))
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
        (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => originalBlockTransfer w K width 1 (terminalMessage w K width (n+t))
                       | 1 => originalBlockTransfer w K width 1 s
                       | _ => originalBlockTransfer w K width 1 b)
  have herror : RatPolyCoeffEqv
      (polyAdd (polyMul A (polyAdd (polyMul d (originalBlockTransfer w K width 1 s))
        (polyNeg H))) (polyMul z z))
      (polyAdd (polyMul d (polyAdd F (polyMul B B))) (polyNeg E)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
        (.mul (.var 4) (.var 4)))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 4) (.var 4))))))
      (by decide) (fun | 0 => A | 1 => d | 2 => originalBlockTransfer w K width 1 s
                       | 3 => H | _ => z)).trans
      ((hsecond.mul_left d).add (RatPolyCoeffEqv.refl (polyNeg E)))
  have Perr : Certificate (N width)
      (polyAdd (polyMul d (polyAdd F (polyMul B B))) (polyNeg E)) :=
    Certificate.ofCoeff herror.symm Perror
  have Pold := original_block_ratio_innovation_certificate hw0 hw1 K width hK n t k hpsi
  dsimp only at Pold
  rw [block_terminal] at Pold
  have Pv := Certificate.constant (N width) inv (Q'.le_of_lt (Q'.recipPos_pos eta heta))
  have Ptotal := (Pold.add (Pv.mul Pyoung)).add (Pv.mul Perr)
  have hinv : RatPolyCoeffEqv (polyMul v u) polyOne :=
    (cap_mul inv eta).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv eta heta)) polyOne).trans
        (RatPolyCoeffEqv.one_smul polyOne))
  have hn : RatPolyCoeffEqv (polyMul v d)
      (cap (innovationRelativeLoss hw0 hw1 width k eta heta)) :=
    (cap_mul inv eps).trans (RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv _ _) polyOne)
  let nu := innovationRelativeLoss hw0 hw1 width k eta heta
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyAdd F (polyNeg (polyAdd D (polyAdd C C))))
        (polyMul v (polyAdd (polyAdd (polyMul u (polyMul u D))
          (polyMul u (polyAdd C C))) E)))
        (polyMul v (polyAdd (polyMul d (polyAdd F (polyMul B B))) (polyNeg E))))
      (polyAdd
        (polyAdd
          (polyAdd F (polyMul (polyMul v d) F))
          (polyMul (polyMul v d) (polyMul B B)))
        (polyAdd (polyNeg D)
          (polyAdd (polyMul (polyMul v u) (polyMul u D))
            (polyAdd (polyMul (polyMul v u) (polyAdd C C)) (polyNeg (polyAdd C C)))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.add (.var 0) (.neg (.add (.var 1) (.add (.var 2) (.var 2)))))
        (.mul (.var 3) (.add (.add (.mul (.var 4) (.mul (.var 4) (.var 1)))
          (.mul (.var 4) (.add (.var 2) (.var 2)))) (.var 5))))
        (.mul (.var 3) (.add (.mul (.var 6) (.add (.var 0) (.mul (.var 7) (.var 7))))
          (.neg (.var 5)))))
      (.add (.add (.add (.var 0) (.mul (.mul (.var 3) (.var 6)) (.var 0)))
        (.mul (.mul (.var 3) (.var 6)) (.mul (.var 7) (.var 7))))
        (.add (.neg (.var 1))
          (.add (.mul (.mul (.var 3) (.var 4)) (.mul (.var 4) (.var 1)))
            (.add (.mul (.mul (.var 3) (.var 4)) (.add (.var 2) (.var 2)))
              (.neg (.add (.var 2) (.var 2)))))))
      (by decide) (fun | 0 => F | 1 => D | 2 => C | 3 => v | 4 => u | 5 => E | 6 => d | _ => B)
  have hcancel := hring.trans
    ((((RatPolyCoeffEqv.refl F).add (hn.mul_right F)).add (hn.mul_right (polyMul B B))).add
      ((RatPolyCoeffEqv.refl (polyNeg D)).add
        (((hinv.mul_right (polyMul u D)).trans (RatPolyCoeffEqv.one_mul _)).add
          (((hinv.mul_right (polyAdd C C)).trans (RatPolyCoeffEqv.one_mul _)).add
            (RatPolyCoeffEqv.refl (polyNeg (polyAdd C C)))))))
  have hfinal : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyAdd F (polyMul (cap nu) F)) (polyMul (cap nu) (polyMul B B)))
        (polyAdd (polyNeg D) (polyAdd (polyMul u D)
          (polyAdd (polyAdd C C) (polyNeg (polyAdd C C))))))
      (polyAdd (polyAdd (polySmul (1+nu) F) (polySmul nu (polyMul B B)))
        (polyNeg (polySmul (1-eta) D))) := by
    have hr := coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (.add (.neg (.var 3)) (.add (.mul (.var 4) (.var 3))
          (.add (.var 5) (.neg (.var 5))))))
      (.add (.add (.mul (.add (.const 1) (.var 1)) (.var 0))
        (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (.neg (.mul (.add (.const 1) (.neg (.var 4))) (.var 3))))
      (by decide) (fun | 0 => F | 1 => cap nu | 2 => B | 3 => D | 4 => u | _ => polyAdd C C)
    have hone : RatPolyCoeffEqv polyOne (cap (1 : Q')) := (RatPolyCoeffEqv.one_smul polyOne).symm
    have hneg : RatPolyCoeffEqv (polyNeg u) (cap (-eta)) :=
      (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0))
        (.mul (.const (-1)) (.var 0)) (by decide) (fun _ => u)).trans
        ((cap_mul_left (-1) u).trans
          ((RatPolyCoeffEqv.smul_assoc (-1) eta polyOne).trans
            (RatPolyCoeffEqv.smul_coefficient
              (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 eta)
                (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv eta))) polyOne)))
    have hc1 := (hone.add (RatPolyCoeffEqv.refl (cap nu))).trans (cap_add 1 nu)
    have hc2 := (hone.add hneg).trans (cap_add 1 (-eta))
    exact hr.trans
      ((((hc1.mul_right F).trans (cap_mul_left (1+nu) F)).add (cap_mul_left nu (polyMul B B))).add
        (RatPolyCoeffEqv.neg ((hc2.mul_right D).trans (cap_mul_left (1-eta) D))))
  exact Certificate.ofCoeff (hcancel.trans hfinal).symm Ptotal

/-- The literal output multiplier is Vbar squared times Gout squared.
Its reciprocal degree is independent of the inner prediction degree k;
the output terminal time is n+t+1. No surviving-form estimate is supplied. -/
theorem original_innovation_relativeComparison_weighted_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (k kout : Nat) (eta : Q') (heta : (0 : Q') < eta) :
    let a := terminalMessage w K width (n+t)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    let F := blockNoise w K width (t+1) (terminalMessage w K width n) psi
    let D := blockNoise w K width 1 a phi
    let B := originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) psi)
    let nu := innovationRelativeLoss hw0 hw1 width k eta heta
    let Vbar := spatialFringeMass w K width
    let Gout := blockReciprocal hw0 hw1 K width hK n (t+1) kout
    let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
    (1-eta)*quaternionHaar (N width) (polyMul Lambda D) ≤
      (1+nu)*quaternionHaar (N width) (polyMul Lambda F) +
        nu*quaternionHaar (N width) (polyMul Lambda (polyMul B B)) := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let F := blockNoise w K width (t+1) (terminalMessage w K width n) psi
  let D := blockNoise w K width 1 a phi
  let B := originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) psi)
  let nu := innovationRelativeLoss hw0 hw1 width k eta heta
  let Vbar := spatialFringeMass w K width
  let Gout := blockReciprocal hw0 hw1 K width hK n (t+1) kout
  let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
  let X := polyAdd (polySmul (1+nu) F) (polySmul nu (polyMul B B))
  let Y := polySmul (1-eta) D
  let gap := polyMul Lambda (polyAdd X (polyNeg Y))
  have P := original_innovation_relativeComparison_certificate
    hw0 hw1 K width hK n t hdepth hpsi k eta heta
  have PG : Certificate (N width) (polyMul Gout Gout) :=
    Certificate.square Gout
      (QuaternionHaarPositiveWindowInverse.reciprocal_supported
        (terminalMessage_supported w K width (n+(t+1)))
        (blockWindowUpper w K width n (t+1))
        (blockWindowUpper_positive hw0 hw1 K width hK n (t+1)) kout)
  have hn : (0 : Q') ≤ quaternionHaar (N width) gap :=
    (((Certificate.square Vbar (spatialFringeMass_supported w K width)).mul PG).mul P).haar_nonnegative
  have hid : RatPolyCoeffEqv (polyAdd (polyMul Lambda Y) gap) (polyMul Lambda X) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.add (.var 2) (.neg (.var 1)))))
      (.mul (.var 0) (.var 2)) (by decide) (fun | 0 => Lambda | 1 => Y | _ => X)
  have hraw : quaternionHaar (N width) (polyMul Lambda Y) ≤
      quaternionHaar (N width) (polyMul Lambda X) :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (quaternionHaar_append (N width) _ _)) (haar_of_coeff hid)))
  have hscalar (c : Q') (p : RatPoly) :
      Q'.eqv (quaternionHaar (N width) (polyMul Lambda (polySmul c p)))
        (c*quaternionHaar (N width) (polyMul Lambda p)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c Lambda p))
      (quaternionHaar_polySmul (N width) c _)
  have hleft := hscalar (1-eta) D
  have hright : Q'.eqv (quaternionHaar (N width) (polyMul Lambda X))
      ((1+nu)*quaternionHaar (N width) (polyMul Lambda F) +
        nu*quaternionHaar (N width) (polyMul Lambda (polyMul B B))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right Lambda _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
        (Q'.add_eqv_congr' (hscalar (1+nu) F) (hscalar nu (polyMul B B))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright))

#print axioms innovationRelativeLoss
#print axioms original_innovation_relativeComparison_certificate
#print axioms original_innovation_relativeComparison_weighted_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationRelativeComparison
