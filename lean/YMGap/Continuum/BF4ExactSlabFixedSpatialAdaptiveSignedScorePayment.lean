/-
# Construct the approximation overhead, leaving genuine original energy

The literal score has a computed finite cap independent of reciprocal degree.
Choose sigma from that cap and the positive ACTUAL surviving target first,
then choose the correction onset. Weighted Young and the original partition
comparison pay the signed reciprocal debt to arbitrary relative tolerance.

This removes only approximation overhead at fixed original parameters. The
cap is source/cutoff/depth/width dependent; no uniform AF diagonal modulus,
small original energy, changing-action comparison or Clay closure is proved.
-/

import YMGap.Continuum.QuaternionHaarFiniteReciprocalScoreCap
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy
import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAdaptiveSignedScorePayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum const_mul_finSum finSum_eqv_congr_lt)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_supported_at)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
  (sixValue sixValue_congr sixValue_mono sixValue_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarFiniteReciprocalScoreCap
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity (reciprocalSlope_supported)
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
  (costTolerance costTolerance_pos costTolerance_pays)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget
  (correctionPlaneTolerance correctionPlaneTolerance_positive six_error sum_error plane_payment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost
  (lastStepPartitionPaymentCap original_block_partition_relative_le
    correctionBulkTolerance correctionBulkTolerance_positive correctionBulkTolerance_payment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost (exactScoreSignedBulk)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass originalBlockTransfer
  spatialFringeMass exactScoreSignedBulk energy blockConditionalRatio relativeCutoff

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem fin_nonneg (f : Nat → Q') : ∀ m : Nat,
    (∀ s, s < m → (0 : Q') ≤ f s) → (0 : Q') ≤ finSum f m
  | 0, _ => Q'.le_refl' 0
  | m+1, h => Q'.zero_le_add _ _
      (fin_nonneg f m (fun s hs => h s (by omega))) (h m (by omega))

private theorem six_nonneg (f : Nat → Nat → Q')
    (h : ∀ i j, i < 4 → j < 4 → (0 : Q') ≤ f i j) : (0 : Q') ≤ sixValue f :=
  Q'.zero_le_add _ _ (h 0 1 (by decide) (by decide))
    (Q'.zero_le_add _ _ (h 0 2 (by decide) (by decide))
      (Q'.zero_le_add _ _ (h 0 3 (by decide) (by decide))
        (Q'.zero_le_add _ _ (h 1 2 (by decide) (by decide))
          (Q'.zero_le_add _ _ (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

/-- Actual finite score cap; crucially there is NO reciprocal-degree argument. -/
def originalScoreCap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let ell := blockWindowLower w K width n (r+1)
  let hell := blockWindowLower_positive hw0 hw1 K width hhead n (r+1)
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then sixValue (fun i j =>
    let c := computedScoreCap ell hell (conditionalScore (4*s+i) (4*s+j) A b)
    (c*c)*quaternionHaar (N width) (polyMul Vbar Vbar)) else 0) (N width)

theorem originalScoreCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) :
    (0 : Q') ≤ originalScoreCap hw0 hw1 K width hK n r psi := by
  unfold originalScoreCap
  apply fin_nonneg
  intro s _
  split
  · apply six_nonneg
    intro i j _ _
    exact Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _)
      (Certificate.square _ (spatialFringeMass_supported w K width)).haar_nonnegative
  · exact Q'.le_refl' 0

/-- A genuine estimate of the signed debt, not a noise enlargement. The
degree-independent cap is constructed; only the correction tolerance is used. -/
theorem original_signed_debt_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (sigma : Q') (hsigma : (0 : Q') < sigma)
    (eta : Q') (heta : (0 : Q') < eta) (k : Nat)
    (hk : lastStepRelativeCorrectionCutoff hw0 hw1 width
      (correctionPlaneTolerance width eta) ≤ k) :
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi (k+1) ≤
      (2*sigma)*originalScoreCap hw0 hw1 K width hK n r psi +
        Q'.recipPos sigma hsigma*(eta*weightedMass w K width (polyMul b b)) := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let ell := blockWindowLower w K width n (r+1)
  let hell := blockWindowLower_positive hw0 hw1 K width hhead n (r+1)
  let u := blockWindowUpper w K width n (r+1)
  let hu := blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)
  let Vbar := spatialFringeMass w K width
  let W := polyMul Vbar Vbar
  let B := weightedMass w K width (polyMul b b)
  let nu := Q'.recipPos sigma hsigma
  let tol := correctionPlaneTolerance width eta
  let capPlane := fun s i j =>
    let c := computedScoreCap ell hell (conditionalScore (4*s+i) (4*s+j) A b)
    (c*c)*quaternionHaar (N width) W
  let g := fun s => if s ∈ activeBlocks width then
    (2*sigma)*sixValue (capPlane s) else 0
  have hA := terminalMessage_supported w K width (n+(r+1))
  have hb : SupportedQuaternionBlocks (N width) b := by
    simpa only [b, originalBlockTransfer] using
      iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) (r+1)
      (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square b hb)
  have hn : (0 : Q') ≤ nu := Q'.le_of_lt (Q'.recipPos_pos sigma hsigma)
  have ht := correctionPlaneTolerance_positive width heta
  have hsum : exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi (k+1) ≤
      finSum g (N width)+Q'.ofNat (N width)*(6*(2*(nu*(tol*B)))) := by
    unfold exactScoreReciprocalDebt
    apply sum_error
    intro s hs
    dsimp only [g]
    split
    · rename_i ha
      have hsn := activeBlocks_lt width s ha
      refine Q'.le_trans' _ _ _ (six_error _ _ _ ?_)
        (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sixValue_mul_left _ _))))
      intro i j hi hj
      let S := conditionalScore (4*s+i) (4*s+j) A b
      let G := blockReciprocal hw0 hw1 K width hhead n (r+1) (k+1)
      let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu (k+1)
      have hdA := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
        (show 4*s+j < 4*N width by omega) hA
      have hdb := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
        (show 4*s+j < 4*N width by omega) hb
      have hS := supported_add (supported_polyMul hA hdb) (support_neg (supported_polyMul hb hdA))
      have hG := reciprocal_supported hA u hu (k+1)
      have he := supported_polyMul hb (supported_polyMul
        (supported_add hG (support_neg (supported_polyMul hA (reciprocalSlope_supported hA u hu (k+1))))) hdA)
      have MW := Certificate.square Vbar (spatialFringeMass_supported w K width)
      have win := blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)
      have ho : ell ≤ u := Q'.mul_le_mul_of_nonneg_right _ _ _
        (BF4ExactSlabFixedSpatialTransferMixingRate.kineticFloor_le_cap hw0 hw1 width)
        (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hhead (n+(r+1)-1)))
      have hc := reciprocal_score_finite_cap_le hA hS hell hu ho win.1 win.2 MW (k+1)
      have hd := signed_debt_le MW (supported_polyMul hG hS) he sigma sigma hsigma
      have hrow : quaternionHaar (N width) (polyMul W (polyMul (polyMul G S) (polyMul G S))) ≈
          quaternionHaar (N width) (polyMul (polyMul W (polyMul G G)) (polyMul S S)) :=
        haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
          (by decide) (fun | 0 => W | 1 => G | _ => S))
      have hE := original_block_lastStep_correction_relative_tolerance
        hw0 hw1 K width hK n r s ha hi hj psi hp ht k hk
      have hlead := Q'.mul_le_mul_of_nonneg_left _ _ (sigma+sigma) hc
        (Q'.zero_le_add _ _ (Q'.le_of_lt hsigma) (Q'.le_of_lt hsigma))
      have hcorr := Q'.mul_le_mul_of_nonneg_left _ _ nu hE hn
      have hpay := Q'.add_le_add hlead hcorr
      have hex : (sigma+sigma)*capPlane s i j+nu*(tol*B) ≈
          (2*sigma)*capPlane s i j+nu*(tol*B) :=
        poly_identity_of_normal_eq
          (.add (.mul (.add (.var 0) (.var 0)) (.var 1)) (.var 2))
          (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
          (by decide) (fun | 0 => sigma | 1 => capPlane s i j | _ => nu*(tol*B))
      have hmore := Q'.add_le_self_of_nonneg (nu*(tol*B)) (nu*(tol*B))
        (Q'.mul_nonneg _ _ hn (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) hB))
      have htwice : nu*(tol*B)+nu*(tol*B) ≈ 2*(nu*(tol*B)) :=
        poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
          (by decide) (fun _ => nu*(tol*B))
      have hdebt :
          (sigma*quaternionHaar (N width) (polyMul (polyMul W (polyMul G G)) (polyMul S S)) +
            -(2*quaternionHaar (N width) (polyMul W (polyMul (polyMul G S) e)))) +
            -(quaternionHaar (N width) (polyMul W (polyMul e e))) ≤
          (sigma+sigma)*quaternionHaar (N width) (polyMul W (polyMul (polyMul G S) (polyMul G S)))+
            nu*quaternionHaar (N width) (polyMul W (polyMul e e)) := Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left sigma _ _ (Q'.eqv_symm hrow)) (Q'.eqv_refl _))
          (Q'.eqv_refl _))) hd
      exact Q'.le_trans' _ _ _ hdebt (Q'.le_trans' _ _ _ hpay
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hex)
          (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hmore (Q'.le_of_eqv htwice)))))
    · have hz : (0 : Q') ≤ 6*(2*(nu*(tol*B))) :=
        Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ hn (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) hB)))
      exact Q'.le_trans' _ _ _ hz (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _))
  have hfactor : (2*sigma)*originalScoreCap hw0 hw1 K width hK n r psi ≈ finSum g (N width) := by
    unfold originalScoreCap
    refine Q'.eqv_trans _ _ _ (const_mul_finSum _ _ _) (finSum_eqv_congr_lt _ _ _ ?_)
    intro s _
    dsimp only [g]
    split
    · exact Q'.eqv_refl _
    · exact Q'.mul_zero_eqv _
  have herror : Q'.ofNat (N width)*(6*(2*(nu*(tol*B)))) ≈
      nu*(Q'.ofNat (N width)*(6*(2*(tol*B)))) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 6) (.mul (.const 2) (.mul (.var 1) (.var 2)))))
      (.mul (.var 1) (.mul (.var 0) (.mul (.const 6) (.mul (.const 2) (.var 2)))))
      (by decide) (fun | 0 => Q'.ofNat (N width) | 1 => nu | _ => tol*B)
  exact Q'.le_trans' _ _ _ hsum (Q'.add_le_add
    (Q'.ge_of_eqv hfactor) (Q'.le_trans' _ _ _ (Q'.le_of_eqv herror)
      (Q'.mul_le_mul_of_nonneg_left _ _ nu (plane_payment width (Q'.le_of_lt heta) hB) hn)))

private def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The literal all-later finite bound, named only to keep witness recursors
from expanding the original polynomial action during elaboration. -/
def signedScorePaymentBound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    (psi : RatPoly) (epsilon sigma : Q') (onset : Nat) : Prop :=
  ∀ k, onset ≤ k →
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    exactScoreSignedBulk sigma hw0 hw1 K width hK n r psi (k+1) ≤
      weightedMass w K width (polyMul A A)*energy w K width A phi +
        epsilon*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b))

attribute [local irreducible] signedScorePaymentBound

/-- Witnesses are data. This is a finite approximation certificate, not a
new analytic frontier assumption or an energy-smallness certificate. -/
structure SignedScorePayment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    (psi : RatPoly) (epsilon : Q') : Type where
  sigma : Q'
  positive : (0 : Q') < sigma
  onset : Nat
  bound : signedScorePaymentBound hw0 hw1 K width hK n r psi epsilon sigma onset

/-- Construct sigma BEFORE the all-later degree onset. Only the positive
actual finite surviving target is guarded; it is not inverted or estimated.
Sigma is an auxiliary Young coefficient, not string tension or coupling. -/
def adaptiveSignedScorePayment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hQ : (0 : Q') <
      weightedMass w K width (polyMul (terminalMessage w K width (n+(r+1)))
        (transferStep w K width (terminalMessage w K width (n+(r+1))))) *
      weightedMass w K width (polyMul
        (originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi))
        (originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)))) :
    SignedScorePayment hw0 hw1 K width hK n r psi epsilon := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let Q := Z1*B
  let h := 1-w
  let M := originalScoreCap hw0 hw1 K width hK n r psi
  let P := lastStepPartitionPaymentCap hw0 hw1 width
  have hA := terminalMessage_supported w K width (n+(r+1))
  have hZ0 : (0 : Q') ≤ Z0 := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
  have hb : SupportedQuaternionBlocks (N width) b := by
    simpa only [b, originalBlockTransfer] using
      iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) (r+1)
      (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square b hb)
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hM := originalScoreCap_nonnegative hw0 hw1 K width hK n r psi
  have hZh : (0 : Q') ≤ Z0*h := Q'.mul_nonneg _ _ hZ0 hh
  let cost := (2*(Z0*h))*M
  have hc : (0 : Q') ≤ cost := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) hZh) hM
  let epsilonHalf := half*epsilon
  have he : (0 : Q') < epsilonHalf := Q'.mul_pos (by decide) hepsilon
  let sigma := costTolerance cost hc (epsilonHalf*Q)
  have hsigma : (0 : Q') < sigma := costTolerance_pos cost hc _ (Q'.mul_pos he hQ)
  let nu := Q'.recipPos sigma hsigma
  have hnu : (0 : Q') ≤ nu := Q'.le_of_lt (Q'.recipPos_pos sigma hsigma)
  let eta := correctionBulkTolerance hw0 hw1 width (epsilonHalf*sigma)
  have heta : (0 : Q') < eta := correctionBulkTolerance_positive hw0 hw1 width (Q'.mul_pos he hsigma)
  let onset := lastStepRelativeCorrectionCutoff hw0 hw1 width (correctionPlaneTolerance width eta)
  refine ⟨sigma, hsigma, onset, ?_⟩
  unfold signedScorePaymentBound
  intro k hk
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
  let debt := exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi (k+1)
  have hd := original_signed_debt_le hw0 hw1 K width hK n r hp sigma hsigma eta heta k hk
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Z0*h) hd hZh
  have hfirst : (Z0*h)*((2*sigma)*M) ≤ epsilonHalf*Q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
      (.mul (.var 1) (.mul (.mul (.const 2) (.var 0)) (.var 2)))
      (by decide) (fun | 0 => Z0*h | 1 => sigma | _ => M)))
      (costTolerance_pays cost hc _ (Q'.le_of_lt (Q'.mul_pos he hQ)))
  have hpart := original_block_partition_relative_le hw0 hw1 K width hhead n (r+1) (by omega)
  have hsecond : (Z0*h)*(nu*(eta*B)) ≤ epsilonHalf*Q := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ (h*(nu*(eta*B))) hpart
      (Q'.mul_nonneg _ _ hh (Q'.mul_nonneg _ _ hnu (Q'.mul_nonneg _ _ (Q'.le_of_lt heta) hB)))
    have hleft : (Z0*h)*(nu*(eta*B)) ≈ Z0*(h*(nu*(eta*B))) := Q'.mul_assoc_eqv _ _ _
    have hright : (P*Z1)*(h*(nu*(eta*B))) ≈ ((h*P)*eta)*(nu*Q) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.var 5)))))
        (.mul (.mul (.mul (.var 2) (.var 0)) (.var 4))
          (.mul (.var 3) (.mul (.var 1) (.var 5))))
        (by decide) (fun | 0 => P | 1 => Z1 | 2 => h | 3 => nu | 4 => eta | _ => B)
    have hpay := Q'.mul_le_mul_of_nonneg_right _ _ (nu*Q)
      (correctionBulkTolerance_payment hw0 hw1 width (Q'.mul_pos he hsigma))
      (Q'.mul_nonneg _ _ hnu (Q'.le_of_lt hQ))
    have hcancel : (epsilonHalf*sigma)*(nu*Q) ≈ epsilonHalf*Q :=
      Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => epsilonHalf | 1 => sigma | 2 => nu | _ => Q))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ Q (Q'.mul_recipPos_eqv sigma hsigma)))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv Q)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) (Q'.le_trans' _ _ _ hm
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) (Q'.le_trans' _ _ _ hpay (Q'.le_of_eqv hcancel))))
  have hdebt : (Z0*h)*debt ≤ epsilon*Q :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv (Z0*h) ((2*sigma)*M) (nu*(eta*B))))
      (Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
            (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (.mul (.add (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
          (by decide) (fun | 0 => half | 1 => epsilon | _ => Q))
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : half+half ≈ 1))
            (Q'.one_mul_eqv (epsilon*Q)))))))
  have hsplit := exactScoreSignedBulk_energy_split sigma hw0 hw1 K width hK n r hN hp (k+1)
  have hex : Z0*(energy w K width A phi+h*debt) ≈
      Z0*energy w K width A phi+(Z0*h)*debt :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) (Q'.le_trans' _ _ _
    (Q'.le_of_eqv hex) (Q'.add_le_add_left _ _ _ hdebt))

#print axioms originalScoreCap_nonnegative
#print axioms original_signed_debt_le
#print axioms adaptiveSignedScorePayment

end YMGap.Continuum.BF4ExactSlabFixedSpatialAdaptiveSignedScorePayment
