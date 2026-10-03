/-
# Fringe-first derivative estimate in the ORIGINAL signed cost

Project the complete incoming source derivative over the unheated lower
fringe BEFORE squaring. The original score is preserved and the removed
weighted residual square is nonnegative. This retains the integrated
original spatial action, every output weight and both signed Taylor terms.

The same near-unit coefficient and existing correction/depth/reconstruction
onsets feed the complete original cost. The remaining active conditional
variance and the useful changing-family signed-window estimate are OPEN.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy
import YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr const_mul_finSum)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost boundaryDrift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor (energy_taylor_angular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy
  (asymmetricCorrectionTolerance asymmetricCorrectionTolerance_positive
    asymmetricCorrectionTolerance_payment asymmetricCorrectionCutoff
    asymmetricCorrectionCostCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionAngularSquareLocality (blockAngularSquare_zero)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity (reciprocalSlope_supported)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
  (sixValue haar_six sixValue_congr sixValue_mul_left sixValue_mono)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

private theorem finite_sum_mono (f g : Nat → Q') : ∀ m : Nat,
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_refl' _
  | m+1, h => Q'.add_le_add
      (finite_sum_mono f g m (fun s hs => h s (by omega))) (h m (by omega))

private theorem terminal_output (w : Q') (K width n r : Nat) :
    transferStep w K width (terminalMessage w K width (n+r)) =
      terminalMessage w K width (n+(r+1)) :=
  (terminalMessage_next w K width (n+r)).trans
    (congrArg (terminalMessage w K width) (by omega))

private theorem source_output (w : Q') (K width r : Nat) (p : RatPoly) :
    transferStep w K width (originalBlockTransfer w K width r p) =
      originalBlockTransfer w K width (r+1) p := by
  exact (show originalBlockTransfer w K width (r+1) p =
      transferStep w K width (originalBlockTransfer w K width r p) from
    by simpa only [originalBlockTransfer, iterateStep, transferStep] using
      iterateStep_add (N width) (kineticWeight w K width)
        (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width) r 1 p).symm


private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

private theorem reciprocal_gradient_square_le (sigma : Q') (hsigma : (0 : Q') < sigma)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let G := reciprocal A u hu k
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu k
    quaternionHaar (N width) (polyMul W (polyMul d d)) ≤
      (1+sigma)*(quaternionHaar (N width) (polyMul (polyMul W (polyMul G G))
        (lastStepProjectedDerivativeBudget w K width s i j a c))) +
      (1+Q'.recipPos sigma hsigma)*(quaternionHaar (N width) (polyMul W (polyMul e e))) := by
  dsimp only
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width hc
  have hdA := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hA
  have hdb := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hb
  have hG := reciprocal_supported hA u hu k
  have hS := supported_add (supported_polyMul hA hdb) (support_neg (supported_polyMul hb hdA))
  have he := supported_polyMul hb (supported_polyMul
    (supported_add hG (support_neg (supported_polyMul hA (reciprocalSlope_supported hA u hu k)))) hdA)
  have hlead := lastStep_projectedDerivative_weighted_multiplier_square_le
    hw0 hw1 K width hK s i j hs hi hj ha hc MW hG
  have hid := reciprocal_score_cleared_derivative (4*s+i) (4*s+j)
    (transferStep w K width a) (transferStep w K width c) u hu k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hid.mul hid).mul_left W)))
    (QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_bound sigma hsigma
      MW (supported_polyMul hG hS) he hlead (Q'.le_of_eqv (Q'.eqv_refl _)))

/-- Literal projected leading square over every active link and six planes.
The COMPLETE source derivatives are fringe-integrated before squaring. -/
def projectedDerivativeAngularBudget (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => (1+sigma)*
      (quaternionHaar (N width) (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (lastStepProjectedDerivativeBudget w K width s i j a c))))
    else 0) (N width)

/-- Exact near-unit coefficient on the very same unsplit incoming source
square. Sigma zero denotes its algebraic undoubled value, not a supplied
zero-tolerance approximation estimate. -/
theorem projectedDerivativeAngularBudget_scale (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) :
    projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi k ≈
      (1+sigma)*projectedDerivativeAngularBudget 0 hw0 hw1 K width hK n r psi k := by
  unfold projectedDerivativeAngularBudget
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun s => ?_) (N width))
    (Q'.eqv_symm (const_mul_finSum _ (1+sigma) (N width)))
  split
  · rename_i hs
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (sixValue_mul_left (1+sigma) _)) ?_
    refine Q'.mul_eqv_congr_left _ _ _ (sixValue_congr _ _ (fun i j _ _ => ?_))
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (1 : Q')+0 ≈ 1))
      (Q'.one_mul_eqv _))
  · exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- The fringe-first budget is genuinely no larger, under the SAME output
weight, multiplier and near-unit coefficient. No action factor is omitted. -/
theorem projectedDerivativeAngularBudget_le_source (sigma : Q')
    (hsigma : (0 : Q') ≤ sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi k ≤
      BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.sourceDerivativeAngularBudget
        sigma hw0 hw1 K width hK n r psi k := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  have ha : SupportedQuaternionBlocks (N width) a := terminalMessage_supported w K width (n+r)
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) r
      (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hG : SupportedQuaternionBlocks (N width) G :=
    reciprocal_supported (terminalMessage_supported w K width (n+(r+1))) _ _ k
  have hcoef : (0 : Q') ≤ 1+sigma := Q'.zero_le_add _ _ Q'.zero_le_one hsigma
  unfold projectedDerivativeAngularBudget
    BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.sourceDerivativeAngularBudget
  apply finite_sum_mono
  intro s hs
  split
  · rename_i hactive
    apply sixValue_mono
    intro i j hi hj
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (lastStep_projectedDerivative_weighted_budget_le hw0 hw1 K width hhead
        s i j (activeBlocks_lt width s hactive) hi hj ha hc
        ((Certificate.square Vbar (spatialFringeMass_supported w K width)).mul
          (Certificate.square G hG))) hcoef
  · exact Q'.le_refl' _

private theorem projected_plane_le (sigma : Q') (hsigma : (0 : Q') < sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    let q := projectedEndpointSource w K width A
    let Vbar := spatialFringeMass w K width
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
    quaternionHaar (N width) (polyMul (polyMul q q)
      (polyMul (angularDerivative (4*s+i) (4*s+j) phi)
        (angularDerivative (4*s+i) (4*s+j) phi))) ≤
      (1+sigma)*(quaternionHaar (N width)
        (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
          (lastStepProjectedDerivativeBudget w K width s i j a c))) +
        (1+Q'.recipPos sigma hsigma)*
          (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hc : SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)) :=
    iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) r
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hg := reciprocal_gradient_square_le sigma hsigma
    hw0 hw1 K width hhead s i j (activeBlocks_lt width s hs) hi hj
    (terminalMessage_supported w K width (n+r)) hc
    (Certificate.square _ (spatialFringeMass_supported w K width))
    (blockWindowUpper w K width n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
  dsimp only at hg
  rw [terminal_output w K width n r, source_output] at hg
  have hq := projected_terminal_source_pin w K width (n+(r+1))
  have hid (d : RatPoly) : RatPolyCoeffEqv
      (polyMul (polyMul (projectedEndpointSource w K width (terminalMessage w K width (n+(r+1))))
        (projectedEndpointSource w K width (terminalMessage w K width (n+(r+1))))) (polyMul d d))
      (polyMul (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
        (polyMul (polyMul (terminalMessage w K width (n+(r+1))) d)
          (polyMul (terminalMessage w K width (n+(r+1))) d))) :=
    ((hq.mul hq).mul_right _).trans (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun
        | 0 => spatialFringeMass w K width
        | 1 => terminalMessage w K width (n+(r+1))
        | _ => d))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hid _))) hg

/-- Full ORIGINAL angular energy: actual inactive links vanish, and the
successor-degree correction is paid in the SAME surviving norm. -/
theorem original_block_projectedDerivative_angular_le (sigma : Q') (hsigma : (0 : Q') < sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : asymmetricCorrectionCutoff sigma hsigma hw0 hw1 width epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi (k+1) +
        epsilon*weightedMass w K width (polyMul b b) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
  let q := projectedEndpointSource w K width A
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) (k+1)
  let Vbar := spatialFringeMass w K width
  let B := weightedMass w K width (polyMul b b)
  let eta := correctionPlaneTolerance width epsilon
  let g := fun s => if s ∈ activeBlocks width then sixValue (fun i j =>
    (1+sigma)*(quaternionHaar (N width) (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
      (lastStepProjectedDerivativeBudget w K width s i j a c)))) else 0
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square _ hb)
  have heta : (0 : Q') < eta := correctionPlaneTolerance_positive width he
  have herr : (0 : Q') ≤ 6*(2*(eta*B)) := Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (Q'.le_of_lt heta) hB))
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  unfold weightedAngularEnergy
  simp only [hn]
  refine Q'.le_trans' _ _ _ (sum_error _ g (6*(2*(eta*B))) (N width) ?_)
    (Q'.add_le_add_left _ _ _ (plane_payment width (Q'.le_of_lt he) hB))
  intro s hs
  dsimp only [g]
  split
  · rename_i ha
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six (N width) _ _)) (six_error _ _ _ ?_)
    intro i j hi hj
    have hg := projected_plane_le sigma hsigma hw0 hw1 K width hK n r s ha hi hj psi hp (k+1)
    let tol := correctionPlaneTolerance width (asymmetricCorrectionTolerance sigma hsigma epsilon)
    have htol : (0 : Q') < tol := correctionPlaneTolerance_positive width
      (asymmetricCorrectionTolerance_positive sigma hsigma he)
    have hplane := original_block_lastStep_correction_relative_tolerance
      hw0 hw1 K width hK n r s ha hi hj psi hp htol k hk
    let C := quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (lastStepProjectedDerivativeBudget w K width s i j a c))
    have hcoef : (0 : Q') ≤ 1+Q'.recipPos sigma hsigma :=
      Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (Q'.recipPos_pos sigma hsigma))
    have hpair := Q'.add_le_add_left ((1+sigma)*C) _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hplane hcoef)
    have hpay : (1+Q'.recipPos sigma hsigma)*(tol*B) ≈ 2*(eta*B) :=
      Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (by decide) (fun
          | 0 => 1+Q'.recipPos sigma hsigma
          | 1 => asymmetricCorrectionTolerance sigma hsigma epsilon
          | 2 => Q'.invSucc (12*N width) | _ => B))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (asymmetricCorrectionTolerance_payment sigma hsigma epsilon))
          (poly_identity_of_normal_eq
            (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
            (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
            (by decide) (fun | 0 => epsilon | 1 => Q'.invSucc (12*N width) | _ => B)))
    exact Q'.le_trans' _ _ _ hg (Q'.le_trans' _ _ _ hpair
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hpay)))
  · rename_i ha
    have hz := blockAngularSquare_zero (blockConditionalRatio_fringe_independent
      hw0 hw1 K width hhead n (r+1) (by omega) hp (k+1) s
        ((fringeBlocks_mem_iff width s).mpr ⟨hs, ha⟩))
    have heq := haar_of_coeff (blocks := N width)
      ((hz.mul_left (polyMul q q)).trans (RatPolyCoeffEqv.mul_zero_right _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _ herr
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))))

/-- Literal fringe-first signed bulk; Rmixed and the negative Rdiagonal
retain their exact order. The original action is integrated, not replaced. -/
def projectedDerivativeSignedBulk (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A)*
    ((1-w)*projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

/-- Complete signed-bulk refinement: only the proved nonnegative fringe
debt is removed; BOTH Taylor remainders stay identical. -/
theorem projectedDerivativeSignedBulk_le_source (sigma : Q')
    (hsigma : (0 : Q') ≤ sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    projectedDerivativeSignedBulk sigma hw0 hw1 K width hK n r psi k ≤
      BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.sourceDerivativeSignedBulk
        sigma hw0 hw1 K width hK n r psi k := by
  have hA := terminalMessage_supported w K width (n+(r+1))
  have hZ0 := weightedMass_nonnegative hw0 hw1 K width
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) (Certificate.square _ hA)
  have hangular := projectedDerivativeAngularBudget_le_source sigma hsigma
    hw0 hw1 K width hK n r psi hp k
  unfold projectedDerivativeSignedBulk
    BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.sourceDerivativeSignedBulk
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hangular
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))) hZ0

/-- Original energy with only reciprocal correction paid relatively.
The projected source and both signed Taylor remainders are unchanged. -/
theorem original_block_projectedDerivative_energy_le (sigma : Q') (hsigma : (0 : Q') < sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi)
    {zeta : Q'} (hz : (0 : Q') < zeta) (k : Nat)
    (hk : asymmetricCorrectionCostCutoff sigma hsigma hw0 hw1 width zeta ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    weightedMass w K width (polyMul A A)*energy w K width A phi ≤
      projectedDerivativeSignedBulk sigma hw0 hw1 K width hK n r psi (k+1) +
        zeta*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let eta := correctionBulkTolerance hw0 hw1 width zeta
  let P := lastStepPartitionPaymentCap hw0 hw1 width
  let s := 1-w
  let L := projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi (k+1)
  let q := projectedEndpointSource w K width A
  let R := pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
    -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))
  have hA := terminalMessage_supported w K width (n+(r+1))
  have PA := terminalMessage_certificate hw0 hw1 K width hhead (n+(r+1))
  have hZ0 := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
  have hZ1 : (0 : Q') ≤ Z1 := weightedMass_nonnegative hw0 hw1 K width hhead
    (PA.mul (BF4ExactSlabFixedSpatialTransferOrder.transferStep_certificate hw0 hw1 K width hhead hA PA))
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square _ hb)
  have hs : (0 : Q') ≤ s := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have heta := correctionBulkTolerance_positive hw0 hw1 width hz
  have hang := original_block_projectedDerivative_angular_le sigma hsigma
    hw0 hw1 K width hK n r hN psi hp heta k hk
  have ht := energy_taylor_angular w K width A phi hA
    (blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp (k+1)) hN
    (fun i hi => blockConditionalRatio_fringe_independent
      hw0 hw1 K width hhead n (r+1) (by omega) hp (k+1) i hi)
  have he : Z0*energy w K width A phi ≤ Z0*(s*(L+eta*B)+R) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ht)
        (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hang hs))) hZ0
  have hexpand : Z0*(s*(L+eta*B)+R) ≈ (Z0*(s*L+R))+(s*Z0)*(eta*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.add (.var 2) (.mul (.var 3) (.var 4)))) (.var 5)))
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 5)))
        (.mul (.mul (.var 1) (.var 0)) (.mul (.var 3) (.var 4))))
      (by decide) (fun
        | 0 => Z0 | 1 => s | 2 => L | 3 => eta | 4 => B | _ => R)
  have hpart := original_block_partition_relative_le hw0 hw1 K width hhead n (r+1) (by omega)
  have herr := Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpart hs) (Q'.mul_nonneg _ _ (Q'.le_of_lt heta) hB)
  have horder : (s*(P*Z1))*(eta*B) ≈ ((s*P)*eta)*(Z1*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 4)))
      (by decide) (fun
        | 0 => s | 1 => P | 2 => Z1 | 3 => eta | _ => B)
  have hpay := Q'.mul_le_mul_of_nonneg_right _ _ _
    (correctionBulkTolerance_payment hw0 hw1 width hz) (Q'.mul_nonneg _ _ hZ1 hB)
  exact Q'.le_trans' _ _ _ he (Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ herr
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder) hpay))))

/-- COMPLETE original cleared cost, with three computed fixed-parameter
onsets. The new source-derivative signed bulk still needs a useful relative
estimate on a justified changing family. -/
theorem original_block_projectedDerivative_cost_relative_tolerance (sigma : Q') (hsigma : (0 : Q') < sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon zeta : Q') (hd : (0 : Q') < delta)
    (he : (0 : Q') < epsilon) (hz : (0 : Q') < zeta)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k+1)
    (hc : asymmetricCorrectionCostCutoff sigma hsigma hw0 hw1 width zeta ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      projectedDerivativeSignedBulk sigma hw0 hw1 K width hK n r psi (k+1) +
        ((zeta+delta)+epsilon)*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  have hr := ExpNeg.le_add_of_abs_sub_le
    (blockConditionalRatio_energy_error_relative_tolerance hw0 hw1 K width hhead
      n (r+1) (by omega) hp epsilon he (k+1) hk)
  have hen := original_block_projectedDerivative_energy_le sigma hsigma hw0 hw1 K width hK n r hN psi hp hz k hc
  have hdri := blockConditionalRatio_boundaryDrift_tolerance
    hw0 hw1 K width hhead n (r+1) (by omega) hp delta hd (k+1) hdepth
  have hdu := Q'.le_trans' _ _ _ (Q'.le_abs_self _) hdri
  have h := Q'.add_le_add_right _ _ (epsilon*(Z1*B)) (Q'.add_le_add hen hdu)
  exact Q'.le_trans' _ _ _ hr (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 4) (.var 5))))
        (.mul (.mul (.var 2) (.var 4)) (.var 5))) (.mul (.var 3) (.mul (.var 4) (.var 5))))
      (.add (.var 0) (.mul (.add (.add (.var 1) (.var 2)) (.var 3)) (.mul (.var 4) (.var 5))))
      (by decide) (fun
        | 0 => projectedDerivativeSignedBulk sigma hw0 hw1 K width hK n r psi (k+1)
        | 1 => zeta | 2 => delta | 3 => epsilon
        | 4 => Z1 | _ => B))))

#print axioms projectedDerivativeAngularBudget
#print axioms projectedDerivativeAngularBudget_scale
#print axioms projectedDerivativeAngularBudget_le_source
#print axioms original_block_projectedDerivative_angular_le
#print axioms projectedDerivativeSignedBulk
#print axioms projectedDerivativeSignedBulk_le_source
#print axioms original_block_projectedDerivative_energy_le
#print axioms original_block_projectedDerivative_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy
