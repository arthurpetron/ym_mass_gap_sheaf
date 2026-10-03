/-
The complete ORIGINAL active-link/six-plane angular budget with only its
reciprocal correction paid by the SAME surviving square.  The leading score
keeps the literal G^2 and lastStepScoreBudget.  Neither signed Taylor remainder
is estimated or removed.  The onset depends on fixed nome, width and tolerance;
no changing-family uniform estimate is asserted.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance (lastStepScoreBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_mono)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.ClusterCount (ofNat_nonneg ofNat_le_ofNat)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

/-- The literal paired-score summand from the complete angular budget.
Only its correction square is replaced by zero. -/
def originalBlockLastStepPairedAngularBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun _ _ => sumBound
      ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
          (lastStepScoreBudget w K width a c))) 0)
    else 0) (N width)

/-- Per-plane allocation includes all six planes and the two copies in
sumBound, including the empty carrier without a denominator case split. -/
def correctionPlaneTolerance (width : Nat) (epsilon : Q') : Q' :=
  epsilon*Q'.invSucc (12*N width)

theorem correctionPlaneTolerance_positive (width : Nat) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : (0 : Q') < correctionPlaneTolerance width epsilon :=
  Q'.mul_pos he (Q'.invSucc_pos (12*N width))

/-- Sum a common error through all six quaternion angular planes. -/
theorem six_error (f g : Nat → Nat → Q') (e : Q')
    (h : ∀ i j, i < 4 → j < 4 → f i j ≤ g i j+e) :
    sixValue f ≤ sixValue g+6*e := by
  refine Q'.le_trans' _ _ _ (sixValue_mono _ _ h) (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 6))
        (.add (.add (.var 2) (.var 6))
          (.add (.add (.var 3) (.var 6))
            (.add (.add (.var 4) (.var 6)) (.add (.var 5) (.var 6)))))))
    (.add (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5)))))) (.mul (.const 6) (.var 6)))
    (by decide) (fun
      | 0 => g 0 1
      | 1 => g 0 2
      | 2 => g 0 3
      | 3 => g 1 2
      | 4 => g 1 3
      | 5 => g 2 3
      | _ => e)

/-- Sum a common error over a finite carrier without a source hypothesis. -/
theorem sum_error (f g : Nat → Q') (e : Q') : (m : Nat) →
    (∀ s, s < m → f s ≤ g s+e) → finSum f m ≤ finSum g m+Q'.ofNat m*e
  | 0, _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 0 _ _ (Q'.zero_mul_eqv e)) (by decide : (0 : Q')+0 ≈ 0)))
  | m+1, h => by
    have hsum := Q'.add_le_add
      (sum_error f g e m (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self m))))
      (h m (Nat.lt_succ_self m))
    refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.add (.var 3) (.var 2)))
        (.add (.add (.var 0) (.var 3)) (.mul (.add (.var 1) (.const 1)) (.var 2)))
        (by decide) (fun
          | 0 => finSum g m
          | 1 => Q'.ofNat m
          | 2 => e
          | _ => g m))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ e
        (Q'.eqv_symm (Q'.ofNat_add_eqv m 1))))

/-- The allocated six-plane/sumBound error stays within epsilon times B. -/
theorem plane_payment (width : Nat) {epsilon B : Q'}
    (he : (0 : Q') ≤ epsilon) (hB : (0 : Q') ≤ B) :
    Q'.ofNat (N width)*(6*(2*(correctionPlaneTolerance width epsilon*B))) ≤ epsilon*B := by
  have hn := Q'.mul_le_mul_of_nonneg_right _ _ _
    (ofNat_le_ofNat (Nat.le_succ (12*N width))) (Q'.invSucc_nonneg (12*N width))
  have hc : Q'.ofNat (12*N width)*Q'.invSucc (12*N width) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc (12*N width)))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _ hc (Q'.mul_nonneg _ _ he hB)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_one_eqv (epsilon*B))))
  have hp := poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.const 6) (.mul (.const 2)
      (.mul (.mul (.var 1) (.var 2)) (.var 3)))))
    (.mul (.mul (.var 1) (.var 3)) (.mul (.mul (.const 12) (.var 0)) (.var 2)))
    (by decide) (fun
      | 0 => Q'.ofNat (N width)
      | 1 => epsilon
      | 2 => Q'.invSucc (12*N width)
      | _ => B)
  exact Q'.eqv_trans _ _ _ hp
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (ClusterCount.ofNat_mul_eqv 12 (N width)))))

/-- Fixed-(nome,width,tolerance) onset; no source amplitude, terminal
depth, heat-prefix cutoff or surviving-norm reciprocal enters it. -/
def lastStepCorrectionPaidCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) (epsilon : Q') : Nat :=
  lastStepRelativeCorrectionCutoff hw0 hw1 width (correctionPlaneTolerance width epsilon)

/-- All active links and six planes are paid at every later successor
reciprocal degree, retaining the actual paired score without modification. -/
theorem original_block_lastStep_angularBudget_correction_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : lastStepCorrectionPaidCutoff hw0 hw1 width epsilon ≤ k) :
    let b := originalBlockTransfer w K width (r+1)
      (polyMul (terminalMessage w K width n) psi)
    originalBlockLastStepAngularBudget hw0 hw1 K width hK n r psi (k+1) ≤
      originalBlockLastStepPairedAngularBudget hw0 hw1 K width hK n r psi (k+1) +
        epsilon*weightedMass w K width (polyMul b b) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) (k+1)
  let Vbar := spatialFringeMass w K width
  let L := (relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
    (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G)) (lastStepScoreBudget w K width a c))
  let e := fun s i j => QuaternionHaarConditionalScoreGradient.reciprocalScoreCorrection
    (4*s+i) (4*s+j) A b (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) (k+1)
  let B := weightedMass w K width (polyMul b b)
  let eta := correctionPlaneTolerance width epsilon
  let f := fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => sumBound L
      (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul (e s i j) (e s i j)))))
    else 0
  let g := fun s => if s ∈ activeBlocks width then sixValue (fun _ _ => sumBound L 0) else 0
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square _ hb)
  have heta : (0 : Q') < eta := correctionPlaneTolerance_positive width he
  have herror : (0 : Q') ≤ 6*(2*(eta*B)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt heta) hB))
  have hp : ∀ s, s < N width → f s ≤ g s+6*(2*(eta*B)) := by
    intro s _hs
    dsimp only [f, g]
    split
    · rename_i hs
      apply six_error
      intro i j hi hj
      have hplane := original_block_lastStep_correction_relative_tolerance
        hw0 hw1 K width hK n r s hs hi hj psi hpsi heta k hk
      have hpair := Q'.add_le_add_left (L+L) _ _ (Q'.add_le_add hplane hplane)
      exact Q'.le_trans' _ _ _ hpair (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1)))
          (.add (.add (.add (.var 0) (.var 0)) (.add (.const 0) (.const 0)))
            (.mul (.const 2) (.var 1)))
          (by decide) (fun
            | 0 => L
            | _ => eta*B)))
    · exact Q'.le_trans' _ _ _ herror
        (Q'.le_of_eqv (Q'.eqv_symm
          (poly_identity_of_normal_eq (.add (.const 0) (.var 0)) (.var 0)
            (by decide) (fun _ => 6*(2*(eta*B))))))
  change finSum f (N width) ≤ finSum g (N width)+epsilon*B
  exact Q'.le_trans' _ _ _ (sum_error f g (6*(2*(eta*B))) (N width) hp)
    (Q'.add_le_add_left _ _ _ (plane_payment width (Q'.le_of_lt he) hB))

/-- Actual projected angular energy, with the SAME surviving-square error.
The leading paired score and both signed Taylor remainders remain unpaid. -/
theorem original_block_lastStep_weightedAngularEnergy_correction_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : lastStepCorrectionPaidCutoff hw0 hw1 width epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      originalBlockLastStepPairedAngularBudget hw0 hw1 K width hK n r psi (k+1) +
        epsilon*weightedMass w K width (polyMul b b) :=
  Q'.le_trans' _ _ _
    (original_block_lastStep_weightedAngularEnergy_le hw0 hw1 K width hK n r hN psi hpsi (k+1))
    (original_block_lastStep_angularBudget_correction_paid hw0 hw1 K width hK n r psi hpsi he k hk)

#print axioms originalBlockLastStepPairedAngularBudget
#print axioms correctionPlaneTolerance
#print axioms correctionPlaneTolerance_positive
#print axioms six_error
#print axioms sum_error
#print axioms plane_payment
#print axioms lastStepCorrectionPaidCutoff
#print axioms original_block_lastStep_angularBudget_correction_paid
#print axioms original_block_lastStep_weightedAngularEnergy_correction_paid

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget
