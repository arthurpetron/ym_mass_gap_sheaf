/-
The ORIGINAL last-step source-derivative square feeds the complete angular
energy and cleared signed Rayleigh cost. Both incoming messages, Vbar^2,
the finite reciprocal square, and BOTH signed Taylor remainders remain.
Only correction, boundary drift and reconstruction are paid by the SAME
surviving norm, at their computed fixed-parameter onsets. No useful relative
bound for the remaining signed bulk or changing-family uniformity is asserted.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
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
open YMGap.Continuum.SU2QuaternionAngularSquareLocality (blockAngularSquare_zero)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue haar_six)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

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

/-- Literal leading square over every active link and all six planes.
The COMPLETE source derivatives inside the budget are not separated. -/
def sourceDerivativeAngularBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => sumBound
      (quaternionHaar (N width) (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (lastStepSourceDerivativeBudget w K width s i j a c))) 0)
    else 0) (N width)

private theorem projected_plane_le {w : Q'}
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
      sumBound (quaternionHaar (N width)
        (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
          (lastStepSourceDerivativeBudget w K width s i j a c)))
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hc : SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)) :=
    iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) r
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hg := lastStep_sourceDerivative_reciprocal_gradient_square_le
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
theorem original_block_sourceDerivative_angular_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : lastStepCorrectionPaidCutoff hw0 hw1 width epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      sourceDerivativeAngularBudget hw0 hw1 K width hK n r psi (k+1) +
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
    sumBound (quaternionHaar (N width) (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
      (lastStepSourceDerivativeBudget w K width s i j a c))) 0) else 0
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
    have hg := projected_plane_le hw0 hw1 K width hK n r s ha hi hj psi hp (k+1)
    have hplane := original_block_lastStep_correction_relative_tolerance
      hw0 hw1 K width hK n r s ha hi hj psi hp heta k hk
    let C := quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (lastStepSourceDerivativeBudget w K width s i j a c))
    have hpair := Q'.add_le_add_left (C+C) _ _ (Q'.add_le_add hplane hplane)
    exact Q'.le_trans' _ _ _ hg (Q'.le_trans' _ _ _ hpair (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1)))
        (.add (.add (.add (.var 0) (.var 0)) (.add (.const 0) (.const 0)))
          (.mul (.const 2) (.var 1)))
        (by decide) (fun
          | 0 => quaternionHaar (N width)
              (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
                (lastStepSourceDerivativeBudget w K width s i j a c))
          | _ => eta*B))))
  · rename_i ha
    have hz := blockAngularSquare_zero (blockConditionalRatio_fringe_independent
      hw0 hw1 K width hhead n (r+1) (by omega) hp (k+1) s
        ((fringeBlocks_mem_iff width s).mpr ⟨hs, ha⟩))
    have heq := haar_of_coeff (blocks := N width)
      ((hz.mul_left (polyMul q q)).trans (RatPolyCoeffEqv.mul_zero_right _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _ herr
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))))

/-- New literal signed bulk; no ordering with the old score budget is
assumed. Rmixed and the negative Rdiagonal retain their exact order. -/
def sourceDerivativeSignedBulk {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A)*
    ((1-w)*sourceDerivativeAngularBudget hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

/-- Original energy with only reciprocal correction paid relatively.
The projected source and both signed Taylor remainders are unchanged. -/
theorem original_block_sourceDerivative_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi)
    {zeta : Q'} (hz : (0 : Q') < zeta) (k : Nat)
    (hk : lastStepCorrectionPaidCostCutoff hw0 hw1 width zeta ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    weightedMass w K width (polyMul A A)*energy w K width A phi ≤
      sourceDerivativeSignedBulk hw0 hw1 K width hK n r psi (k+1) +
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
  let L := sourceDerivativeAngularBudget hw0 hw1 K width hK n r psi (k+1)
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
  have hang := original_block_sourceDerivative_angular_le
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
theorem original_block_sourceDerivative_cost_relative_tolerance {w : Q'}
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
      sourceDerivativeSignedBulk hw0 hw1 K width hK n r psi (k+1) +
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
  have hen := original_block_sourceDerivative_energy_le hw0 hw1 K width hK n r hN psi hp hz k hc
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
        | 0 => sourceDerivativeSignedBulk hw0 hw1 K width hK n r psi (k+1)
        | 1 => zeta | 2 => delta | 3 => epsilon
        | 4 => Z1 | _ => B))))

#print axioms sourceDerivativeAngularBudget
#print axioms original_block_sourceDerivative_angular_le
#print axioms sourceDerivativeSignedBulk
#print axioms original_block_sourceDerivative_energy_le
#print axioms original_block_sourceDerivative_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy
