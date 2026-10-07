/-
# Vacuum-preserving finite prediction on the ORIGINAL block marginal

With a=T^t g, b=T^t(g psi), G the existing finite reciprocal, and
r=1-aG, define P psi=G b+r psi on the output slice. This is an auxiliary
polynomial map, not a substituted action or an OS/coarse transfer operator.
The residual restores constants exactly rather than leaking the vacuum.

The actual symmetric block marginal is H[V*g*a*(-)]. Jensen and ORIGINAL
weighted transfer symmetry give ||P psi||^2 <= (1+mixRate^k)||psi||^2
in this SAME marginal, for every supported source, without a source cap or
assumed stationarity. No OS-norm, intertwining or changing-action comparison
is asserted. The continuum/scaling and Clay inputs remain open.
-/

import YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockUnitalPrediction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds (halfOpenAction_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
  (reciprocal_supported multiplierErrorInterval)
open YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (stepWeightCertificate transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative kineticFloor kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr weightedMass_add weightedMass_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (iterateStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica (blockWindowWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight terminalMessage weightedMass

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      transferStep w K width (originalBlockTransfer w K width t p) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem block_congr (w : Q') (K width : Nat) :
    (t : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
    RatPolyCoeffEqv (originalBlockTransfer w K width t p) (originalBlockTransfer w K width t q)
  | 0, _, _, h => h
  | t+1, _, _, h => by
      rw [block_succ, block_succ]
      exact transfer_congr w K width (block_congr w K width t h)

private theorem block_add (w : Q') (K width : Nat) : (t : Nat) → (p q : RatPoly) →
    RatPolyCoeffEqv (originalBlockTransfer w K width t (polyAdd p q))
      (polyAdd (originalBlockTransfer w K width t p) (originalBlockTransfer w K width t q))
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | t+1, p, q => by
      rw [block_succ, block_succ, block_succ]
      exact (transfer_congr w K width (block_add w K width t p q)).trans
        (transferStep_add w K width _ _)

private theorem block_terminal (w : Q') (K width n t : Nat) :
    originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n t polyOne).symm

private theorem source_support (w : Q') (K width t : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    SupportedQuaternionBlocks (N width) (originalBlockTransfer w K width t p) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) t hp

private theorem inner_moment (w : Q') (K width n t : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (polyMul (blockWindowWeight w K width n t) p))
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) p)) := by
  unfold blockWindowWeight
  exact (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => terminalMessage w K width n
           | 1 => halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t
           | _ => p))).trans
    (windowMessage_iterate (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n) p)

private theorem inner_mass (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (terminalMessage w K width (n+t)) := by
  have h := (partialHaarHeads_congr (t*(N width))
    (RatPolyCoeffEqv.mul_one (blockWindowWeight w K width n t)).symm).trans
    ((inner_moment w K width n t polyOne).trans
      (block_congr w K width t (RatPolyCoeffEqv.mul_one _)))
  rw [block_terminal] at h
  exact h

/-- Positive residual on the actual original middle slice. -/
def blockPredictionResidual {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) : RatPoly :=
  polyAdd polyOne (polyNeg (polyMul (terminalMessage w K width (n+t))
    (blockReciprocal hw0 hw1 K width hK n t k)))

private theorem residual_support {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) :
    SupportedQuaternionBlocks (N width) (blockPredictionResidual hw0 hw1 K width hK n t k) :=
  supported_add (supported_one _) (support_neg (supported_polyMul
    (terminalMessage_supported w K width (n+t))
    (reciprocal_supported (terminalMessage_supported w K width (n+t)) _ _ k)))

private def residual_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t) (k : Nat) :
    Certificate (N width) (blockPredictionResidual hw0 hw1 K width hK n t k) :=
  reciprocalResidual_certificate (blockWindowUpper_positive hw0 hw1 K width hK n t)
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k

private def residual_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t) (k : Nat) :
    Certificate (N width) (polyAdd (cap ((mixRate hw0 hw1 width)^k))
      (polyNeg (blockPredictionResidual hw0 hw1 K width hK n t k))) := by
  have horder : blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1)))
  have M := (multiplierErrorInterval (terminalMessage_supported w K width (n+t))
    (blockWindowUpper_positive hw0 hw1 K width hK n t) horder
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k).changeCap
      (Q'.pow_eqv_congr (blockWindow_radius_pin hw0 hw1 K width hK n t) k)
  exact Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      (coeffEvalExpr_eqv_of_normalize_eq
        (.neg (.add (.const 1) (.neg (.var 0))))
        (.add (.var 0) (.neg (.const 1))) (by decide)
        (fun _ => polyMul (terminalMessage w K width (n+t))
          (blockReciprocal hw0 hw1 K width hK n t k)))) M.lower

/-- An auxiliary finite prediction, completed by its literal residual.
The same source polynomial is evaluated on the output slice in the second term. -/
def blockUnitalPrediction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  polyAdd (blockConditionalRatio hw0 hw1 K width hK n t psi k)
    (polyMul (blockPredictionResidual hw0 hw1 K width hK n t k) psi)

def blockUnitalSecondMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  polyAdd (polyMul (blockReciprocal hw0 hw1 K width hK n t k)
    (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) (polyMul psi psi))))
    (polyMul (blockPredictionResidual hw0 hw1 K width hK n t k) (polyMul psi psi))

/-- The SAME original symmetric block marginal, not the completed OS norm. -/
def blockMarginalSquare (w : Q') (K width n t : Nat) (psi : RatPoly) : Q' :=
  weightedMass w K width (polyMul
    (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+t))) (polyMul psi psi))

theorem blockUnitalPrediction_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) :
    RatPolyCoeffEqv (blockUnitalPrediction hw0 hw1 K width hK n t polyOne k) polyOne := by
  let a := terminalMessage w K width (n+t)
  let G := blockReciprocal hw0 hw1 K width hK n t k
  have hb := block_congr w K width t (RatPolyCoeffEqv.mul_one (terminalMessage w K width n))
  rw [block_terminal] at hb
  exact (((hb.mul_left G).trans (RatPolyCoeffEqv.mul_comm G a)).add
    (RatPolyCoeffEqv.mul_one _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.add (.const 1) (.neg (.var 0))))
      (.const 1) (by decide) (fun _ => polyMul a G))

/-- The finite Jensen certificate is constructed on the ORIGINAL window.
No normalized conditional measure or stationarity law is assumed. -/
def blockUnitalPrediction_jensen_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    Certificate (N width) (polyAdd (blockUnitalSecondMoment hw0 hw1 K width hK n t psi k)
      (polyNeg (polyMul (blockUnitalPrediction hw0 hw1 K width hK n t psi k)
        (blockUnitalPrediction hw0 hw1 K width hK n t psi k)))) := by
  let W := blockWindowWeight w K width n t
  let G := blockReciprocal hw0 hw1 K width hK n t k
  let r := blockPredictionResidual hw0 hw1 K width hK n t k
  have hs : (t+1)*(N width) = N width+t*(N width) := by rw [Nat.succ_mul]; omega
  have hsmall : N width ≤ (t+1)*(N width) := by rw [Nat.succ_mul]; omega
  have hW : SupportedQuaternionBlocks (N width+t*(N width)) W := hs ▸
    supported_polyMul (support_mono (terminalMessage_supported w K width n) hsmall)
      (halfOpenAction_supported (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) t)
  have PW : Certificate (N width+t*(N width)) W :=
    (certificate_extend (t*(N width)) (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)).mul
      (hs ▸ halfOpenAction_certificate (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) t)
  have hG := reciprocal_supported (terminalMessage_supported w K width (n+t))
    (blockWindowUpper w K width n t) (blockWindowUpper_positive hw0 hw1 K width hK n t) k
  have PG := reciprocal_certificate (terminalMessage_supported w K width (n+t))
    (blockWindowUpper_positive hw0 hw1 K width hK n t)
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k
  have hr := residual_support hw0 hw1 K width hK n t k
  have PR := residual_positive hw0 hw1 K width hK n t hdepth k
  have hunit : RatPolyCoeffEqv
      (polyAdd (polyMul (partialHaarHeads (t*(N width)) W) G) r) polyOne :=
    (((inner_mass w K width n t).mul_right G).add (RatPolyCoeffEqv.refl r)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.add (.const 1) (.neg (.var 0))))
        (.const 1) (by decide) (fun _ => polyMul (terminalMessage w K width (n+t)) G))
  have P := jensen_certificate (N width) (t*(N width)) W psi psi G r hW
    (support_mono hpsi (by omega)) hpsi hG hr PW PG PR hunit
  have hb := inner_moment w K width n t psi
  have hH := inner_moment w K width n t (polyMul psi psi)
  have hpred := (hb.mul_left G).add (RatPolyCoeffEqv.refl (polyMul r psi))
  have hmoment := (hH.mul_left G).add (RatPolyCoeffEqv.refl (polyMul r (polyMul psi psi)))
  exact Certificate.ofCoeff
    (hmoment.add (RatPolyCoeffEqv.neg (hpred.mul hpred))).symm P

private theorem mass_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (P : Certificate (N width) (polyAdd q (polyNeg p))) :
    weightedMass w K width p ≤ weightedMass w K width q := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK P
  have he := Q'.eqv_trans _ _ _ (weightedMass_add w K width q (polyNeg p))
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => weightedMass w K width p)))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- Actual same-marginal second-moment control, using the signed adjoint
density defect rather than assuming the auxiliary prediction is stationary. -/
theorem blockUnitalSecondMoment_upper {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    weightedMass w K width (polyMul
      (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+t)))
      (blockUnitalSecondMoment hw0 hw1 K width hK n t psi k)) ≤
      (1+(mixRate hw0 hw1 width)^k)*blockMarginalSquare w K width n t psi := by
  let g := terminalMessage w K width n
  let a := terminalMessage w K width (n+t)
  let G := blockReciprocal hw0 hw1 K width hK n t k
  let r := blockPredictionResidual hw0 hw1 K width hK n t k
  let psi2 := polyMul psi psi
  let H := originalBlockTransfer w K width t (polyMul g psi2)
  let v := polyMul g (polyMul a G)
  let z := polyMul g r
  let M := blockMarginalSquare w K width n t psi
  let rho := (mixRate hw0 hw1 width)^k
  have hg := terminalMessage_supported w K width n
  have ha := terminalMessage_supported w K width (n+t)
  have hG := reciprocal_supported ha (blockWindowUpper w K width n t)
    (blockWindowUpper_positive hw0 hw1 K width hK n t) k
  have hr := residual_support hw0 hw1 K width hK n t k
  have Pg := terminalMessage_certificate hw0 hw1 K width hK n
  have Pa := terminalMessage_certificate hw0 hw1 K width hK (n+t)
  have Pr := residual_positive hw0 hw1 K width hK n t hdepth k
  have hz := supported_polyMul hg hr
  have Pz := iterateStep_certificate hw0 hw1 K width hK t z hz (Pg.mul Pr)
  have hsum : RatPolyCoeffEqv
      (polyAdd (originalBlockTransfer w K width t v) (originalBlockTransfer w K width t z)) a := by
    have hvz : RatPolyCoeffEqv (polyAdd v z) g :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
        (.var 0) (by decide) (fun | 0 => g | _ => polyMul a G)
    have h := (block_add w K width t v z).symm.trans (block_congr w K width t hvz)
    rw [block_terminal] at h
    exact h
  have hdiff : RatPolyCoeffEqv (polyAdd a (polyNeg (originalBlockTransfer w K width t v)))
      (originalBlockTransfer w K width t z) :=
    ((hsum.symm).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (.var 1) (by decide)
        (fun | 0 => originalBlockTransfer w K width t v
             | _ => originalBlockTransfer w K width t z))
  have Pdiff := Certificate.ofCoeff hdiff Pz
  have Ptest := Pg.mul (Certificate.square psi hpsi)
  have hfirst := mass_order hw0 hw1 K width hK
    (Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun | 0 => polyMul g psi2 | 1 => a
                         | _ => originalBlockTransfer w K width t v))
      (Ptest.mul Pdiff))
  have hs := iterateStep_weighted_symmetric w K width t (supported_polyMul hg (supported_polyMul hpsi hpsi))
    (supported_polyMul hg (supported_polyMul ha hG))
  have hM : weightedMass w K width (polyMul (polyMul g psi2) a) ≈ M :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => g | 1 => psi2 | _ => a))
  have h1 : weightedMass w K width (polyMul v H) ≤ M :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hs) (Q'.le_trans' _ _ _ hfirst (Q'.le_of_eqv hM))
  have Pupper := residual_upper hw0 hw1 K width hK n t hdepth k
  have hsecond := mass_order hw0 hw1 K width hK
    (Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
          (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 4) (.var 3)))))
        (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.add (.var 0) (.neg (.var 4))))
        (by decide) (fun | 0 => cap rho | 1 => g | 2 => a | 3 => psi2 | _ => r))
      (((Pg.mul Pa).mul (Certificate.square psi hpsi)).mul Pupper))
  have hcap : weightedMass w K width (polyMul (cap rho) (polyMul (polyMul g a) psi2)) ≈ rho*M :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left rho _))
      (weightedMass_smul w K width rho _)
  have h2 := Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hcap)
  have hsplit : weightedMass w K width (polyMul (polyMul g a)
      (blockUnitalSecondMoment hw0 hw1 K width hK n t psi k)) ≈
      weightedMass w K width (polyMul v H) +
        weightedMass w K width (polyMul (polyMul g a) (polyMul r psi2)) :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
        (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 5))))
        (by decide) (fun | 0 => g | 1 => a | 2 => G | 3 => H | 4 => r | _ => psi2)))
      (weightedMass_add w K width _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ (Q'.add_le_add h1 h2)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.const 1) (.var 1)) (.var 0))
        (by decide) (fun | 0 => M | _ => rho))))

/-- A source-cap-free upper square comparison on the SAME original block
marginal. This is NOT an OS/completed norm or a changing-action intertwiner. -/
theorem blockUnitalPrediction_square_upper {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    blockMarginalSquare w K width n t (blockUnitalPrediction hw0 hw1 K width hK n t psi k) ≤
      (1+(mixRate hw0 hw1 width)^k)*blockMarginalSquare w K width n t psi := by
  have P := blockUnitalPrediction_jensen_certificate hw0 hw1 K width hK n t hdepth hpsi k
  have Q := (terminalMessage_certificate hw0 hw1 K width hK n).mul
    (terminalMessage_certificate hw0 hw1 K width hK (n+t))
  have h := mass_order hw0 hw1 K width hK
    (Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => polyMul (terminalMessage w K width n) (terminalMessage w K width (n+t))
          | 1 => blockUnitalSecondMoment hw0 hw1 K width hK n t psi k
          | _ => polyMul (blockUnitalPrediction hw0 hw1 K width hK n t psi k)
              (blockUnitalPrediction hw0 hw1 K width hK n t psi k))) (Q.mul P))
  exact Q'.le_trans' _ _ _ h
    (blockUnitalSecondMoment_upper hw0 hw1 K width hK n t hdepth hpsi k)

#print axioms blockPredictionResidual
#print axioms blockUnitalPrediction
#print axioms blockUnitalSecondMoment
#print axioms blockMarginalSquare
#print axioms blockUnitalPrediction_one
#print axioms blockUnitalPrediction_jensen_certificate
#print axioms blockUnitalSecondMoment_upper
#print axioms blockUnitalPrediction_square_upper

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockUnitalPrediction
