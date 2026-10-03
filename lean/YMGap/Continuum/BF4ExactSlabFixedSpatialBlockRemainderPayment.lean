/-
Pay only the raw reconstructed square in the COMPLETE original remainder.
The actual projected source is Vbar*A, not a replacement of V by Vbar^2.
Fringe independence and the finite reciprocal multiplier give
H[(q*phi)^2]<=spatialCeiling*ell[b^2]. The checked partition comparison
then pays its eighth heat-loss coefficient in SAME Z1*ell[b^2] currency.
The negative completed square, signed cubic/cutoff terms, angular pair
remainder and angular-weight change all remain in the signed bulk.
Fixed-parameter caps may deteriorate with nome/width. A useful combined
relative estimate on a justified changing family remains OPEN.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
import YMGap.Continuum.SU2QuaternionCompleteRemainderSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRemainderPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor (spatialCeiling_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceCubic sourceOmitted)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
  (quarter observableSquare squareCompletionMass completedRemainder completeRemainder_square_completion)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

/-- The literal finite reconstructed source square is paid by the SAME
surviving original square. No center transport or norm inverse is used. -/
theorem blockConditionalRatio_sourceSquare_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n (r+1) psi k
    let q := projectedEndpointSource w K width A
    quaternionHaar (N width) (polyMul (polyMul q phi) (polyMul q phi)) ≤
      spatialCeiling w width * weightedMass w K width (polyMul b b) := by
  dsimp only
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hK n (r+1) psi k
  let q := projectedEndpointSource w K width A
  let Vbar := spatialFringeMass w K width
  have hA := terminalMessage_supported w K width (n+(r+1))
  have hf := blockConditionalRatio_supported hw0 hw1 K width hK n (r+1) hp k
  have hq := projected_terminal_source_pin w K width (n+(r+1))
  have hid : RatPolyCoeffEqv (polyMul (polyMul q phi) (polyMul q phi))
      (polyMul (polyMul Vbar Vbar) (polyMul (polyMul A phi) (polyMul A phi))) :=
    ((hq.mul_right phi).mul (hq.mul_right phi)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.mul (.mul (.var 0) (.var 0))
          (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (by decide) (fun
          | 0 => Vbar
          | 1 => A
          | _ => phi))
  have hw := spatialFringeMass_square_weight_le hw0 hw1 K width hK
    (supported_polyMul hA hf)
    (fun i hi => quaternionBlockIndependent_polyMul
      (terminal_fringe_independent w K width (n+(r+1)) i hi)
      (blockConditionalRatio_fringe_independent hw0 hw1 K width hK n (r+1)
        (by omega) hp k i hi))
  have hs := blockConditionalRatio_surviving_square_le
    hw0 hw1 K width hK n (r+1) (by omega) hp k
  have hsq : RatPolyCoeffEqv (polyMul (polyMul A phi) (polyMul A phi))
      (polyMul (polyMul A A) (polyMul phi phi)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun
        | 0 => A
        | _ => phi)
  have hsur := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (BF4ExactSlabFixedSpatialWeightedMass.weightedMass_congr w K width hsq)) hs
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (blocks := N width) hid))
    (Q'.le_trans' _ _ _ hw (Q'.mul_le_mul_of_nonneg_left _ _ _ hsur
      (Q'.le_of_lt (spatialCeiling_positive hw0 hw1 width))))

/-- Exactly h²/8, written in the original square-completion coefficients. -/
def blockRemainderRate (w : Q') : Q' :=
  (HalfPow.half*((1-w)*(1-w)))*quarter

private theorem rate_nonnegative (w : Q') : (0 : Q') ≤ blockRemainderRate w :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (SumOfSquares.q_mul_self_nonneg _)) (by decide)

/-- The payment constant has fixed nome/width dependence only. Its explicit
partition/spatial factors are NOT claimed uniform on a changing family. -/
def blockRemainderPaymentCap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) : Q' :=
  (blockRemainderRate w*lastStepPartitionPaymentCap hw0 hw1 width)*spatialCeiling w width

/-- Pay the raw square coefficient, keeping both original partitions and
the surviving norm. The case B=0 requires no division or separate premise. -/
theorem original_block_rawSquare_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n (r+1) psi k
    let q := projectedEndpointSource w K width A
    weightedMass w K width (polyMul A A)*
      (blockRemainderRate w*observableSquare (N width-1) q phi) ≤
      blockRemainderPaymentCap hw0 hw1 width *
        (weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hK n (r+1) psi k
  let q := projectedEndpointSource w K width A
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let C := spatialCeiling w width
  let P := lastStepPartitionPaymentCap hw0 hw1 width
  let rate := blockRemainderRate w
  have hZ0 : (0 : Q') ≤ Z0 := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square A (terminalMessage_supported w K width (n+(r+1))))
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square b hb)
  have hC : (0 : Q') ≤ C := Q'.le_of_lt (spatialCeiling_positive hw0 hw1 width)
  have hrate := rate_nonnegative w
  have hraw : observableSquare (N width-1) q phi ≤ C*B := by
    unfold observableSquare
    rw [Nat.sub_add_cancel hN]
    exact blockConditionalRatio_sourceSquare_le hw0 hw1 K width hK n r hp k
  have hpart := original_block_partition_relative_le hw0 hw1 K width hK n (r+1) (by omega)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hraw hrate) hZ0
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _ _ hpart
    (Q'.mul_nonneg _ _ hrate (Q'.mul_nonneg _ _ hC hB))
  have he : (P*Z1)*(rate*(C*B)) ≈ ((rate*P)*C)*(Z1*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
      (.mul (.mul (.mul (.var 2) (.var 0)) (.var 3)) (.mul (.var 1) (.var 4)))
      (by decide) (fun
        | 0 => P
        | 1 => Z1
        | 2 => rate
        | 3 => C
        | _ => B)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv he))

/-- SIGNED residue after paying only the raw square. In particular the
completed negative square and every cubic/cutoff/angular remainder survive. -/
def signedRemainderResidue (tail : Nat) (w : Q') (K : Nat) (q phi : RatPoly) : Q' :=
  let h : Q' := 1-w;
  -((HalfPow.half*(h*h))*squareCompletionMass tail q phi) +
    sourceCubic tail w q phi - sourceOmitted tail w K q phi -
      h*pairRemainder tail w K q (polyMul q (angularSquare tail phi))

private theorem signed_remainder_split (tail : Nat) (w : Q') (K : Nat)
    (q phi : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hp : SupportedQuaternionBlocks (tail+1) phi) :
    pairRemainder tail w K q (polyMul q (polyMul phi phi)) -
      pairRemainder tail w K (polyMul q phi) (polyMul q phi) ≈
      blockRemainderRate w*observableSquare tail q phi +
        ((1-w)*angularWeightChange tail w K q phi + signedRemainderResidue tail w K q phi) := by
  let R := pairRemainder tail w K q (polyMul q (polyMul phi phi)) -
    pairRemainder tail w K (polyMul q phi) (polyMul q phi)
  let C := (1-w)*angularWeightChange tail w K q phi
  have h1 : R ≈ completeRemainder tail w K q phi+C :=
    poly_identity_of_normal_eq (.var 0) (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (by decide) (fun
        | 0 => R
        | _ => C)
  have h2 := Q'.add_eqv_congr' (completeRemainder_square_completion tail w K q phi hq hp)
    (Q'.eqv_refl C)
  have h3 : completedRemainder tail w K q phi+C ≈
      blockRemainderRate w*observableSquare tail q phi +
        (C+signedRemainderResidue tail w K q phi) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.add (.mul (.var 0)
        (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))) (.var 4))
        (.neg (.var 5))) (.neg (.var 6))) (.var 7))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.add (.var 7) (.add (.add (.add (.neg (.mul (.var 0) (.var 3)))
          (.var 4)) (.neg (.var 5))) (.neg (.var 6)))))
      (by decide) (fun
        | 0 => HalfPow.half*((1-w)*(1-w))
        | 1 => quarter
        | 2 => observableSquare tail q phi
        | 3 => squareCompletionMass tail q phi
        | 4 => sourceCubic tail w q phi
        | 5 => sourceOmitted tail w K q phi
        | 6 => (1-w)*pairRemainder tail w K q (polyMul q (angularSquare tail phi))
        | _ => C)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- The whole source angular term and SIGNED angular-weight change remain
together; no DV*X cancellation or favorable residue sign is asserted. -/
def blockRemainderSignedBulk {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A)*
    ((1-w)*(sourceDerivativeAngularBudget hw0 hw1 K width hK n r psi k +
      angularWeightChange (N width-1) w K q phi) +
        signedRemainderResidue (N width-1) w K q phi)

/-- Genuine reduction of the previous original signed bulk: only its
raw reconstructed square is replaced by a paid SAME-norm scalar. -/
theorem sourceDerivativeSignedBulk_remainder_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    sourceDerivativeSignedBulk hw0 hw1 K width hK n r psi k ≤
      blockRemainderSignedBulk hw0 hw1 K width hK n r psi k +
        blockRemainderPaymentCap hw0 hw1 width *
          (weightedMass w K width (polyMul A (transferStep w K width A))*
            weightedMass w K width (polyMul b b)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  let Z0 := weightedMass w K width (polyMul A A)
  let L := sourceDerivativeAngularBudget hw0 hw1 K width hK n r psi k
  let C := angularWeightChange (N width-1) w K q phi
  let R := signedRemainderResidue (N width-1) w K q phi
  let Q := observableSquare (N width-1) q phi
  let h := 1-w
  have hqn : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+(r+1))))
  have hpn := blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp k
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  have hqt : SupportedQuaternionBlocks (N width-1+1) q := by
    rw [hn]
    exact hqn
  have hpt : SupportedQuaternionBlocks (N width-1+1) phi := by
    rw [hn]
    exact hpn
  have hs := signed_remainder_split (N width-1) w K q phi hqt hpt
  have h1 : sourceDerivativeSignedBulk hw0 hw1 K width hK n r psi k ≈
      Z0*(h*L+(blockRemainderRate w*Q+(h*C+R))) :=
    Q'.mul_eqv_congr_left Z0 _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hs)
  have h2 : Z0*(h*L+(blockRemainderRate w*Q+(h*C+R))) ≈
      blockRemainderSignedBulk hw0 hw1 K width hK n r psi k + Z0*(blockRemainderRate w*Q) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
        (.add (.mul (.var 3) (.var 4)) (.add (.mul (.var 1) (.var 5)) (.var 6)))))
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.add (.var 2) (.var 5))) (.var 6)))
        (.mul (.var 0) (.mul (.var 3) (.var 4))))
      (by decide) (fun
        | 0 => Z0
        | 1 => h
        | 2 => L
        | 3 => blockRemainderRate w
        | 4 => Q
        | 5 => C
        | _ => R)
  have hpay := original_block_rawSquare_payment hw0 hw1 K width hhead n r hN hp k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ h1 h2))
    (Q'.add_le_add_left _ _ _ hpay)

/-- COMPLETE original cost, with all approximation errors already paid.
The remaining bulk retains its signs. No changing-family estimate is supplied. -/
theorem original_block_remainderPaid_cost_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon zeta : Q') (hd : (0 : Q') < delta)
    (he : (0 : Q') < epsilon) (hz : (0 : Q') < zeta)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k+1)
    (hc : lastStepCorrectionPaidCostCutoff hw0 hw1 width zeta ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      blockRemainderSignedBulk hw0 hw1 K width hK n r psi (k+1) +
        (blockRemainderPaymentCap hw0 hw1 width+((zeta+delta)+epsilon))*
          (weightedMass w K width (polyMul A (transferStep w K width A))*
            weightedMass w K width (polyMul b b)) := by
  dsimp only
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let M := weightedMass w K width (polyMul A (transferStep w K width A))*
    weightedMass w K width (polyMul b b)
  have hcost := original_block_sourceDerivative_cost_relative_tolerance
    hw0 hw1 K width hK n r hN hp delta epsilon zeta hd he hz hdepth k hk hc
  have hpay := sourceDerivativeSignedBulk_remainder_payment
    hw0 hw1 K width hK n r hN hp (k+1)
  have hsum := Q'.add_le_add_right _ _ (((zeta+delta)+epsilon)*M) hpay
  exact Q'.le_trans' _ _ _ hcost (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 3)))
      (.add (.var 0) (.mul (.add (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun
        | 0 => blockRemainderSignedBulk hw0 hw1 K width hK n r psi (k+1)
        | 1 => blockRemainderPaymentCap hw0 hw1 width
        | 2 => (zeta+delta)+epsilon
        | _ => M))))

#print axioms blockConditionalRatio_sourceSquare_le
#print axioms blockRemainderRate
#print axioms blockRemainderPaymentCap
#print axioms original_block_rawSquare_payment
#print axioms signedRemainderResidue
#print axioms blockRemainderSignedBulk
#print axioms sourceDerivativeSignedBulk_remainder_payment
#print axioms original_block_remainderPaid_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRemainderPayment
