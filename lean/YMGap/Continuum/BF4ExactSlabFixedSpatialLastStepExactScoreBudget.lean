/-
# The exact ORIGINAL output score, before conditional Jensen

The finite reciprocal derivative is bounded directly by the square of
A*Db-b*DA and its vanishing reciprocal correction. No conditional source
variance is required for this estimate. The older fringe-projected source
budget equals this score budget plus its literal weighted active Jensen
debt. All original action, output, depth and reciprocal factors are kept.

This removes an optional positive overestimate, not the still-open signed
Taylor/drift-to-surviving-norm comparison or changing-family estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy
  (projectedDerivativeAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff (projectedActiveVariance)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity (reciprocalSlope_supported)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_congr sixValue_mono)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

/-- The exact score square suffices for the reciprocal plane estimate.
Only the positive auxiliary sigma is inverted; neither A nor a source
norm is divided out. No kinetic positivity or Jensen input occurs. -/
theorem exact_score_reciprocal_plane_le (sigma : Q') (hsigma : (0 : Q') < sigma)
    (width s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4)
    (A b W : RatPoly) (hA : SupportedQuaternionBlocks (N width) A)
    (hb : SupportedQuaternionBlocks (N width) b) (PW : Certificate (N width) W)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let G := reciprocal A u hu k
    let S := conditionalScore (4*s+i) (4*s+j) A b
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu k
    quaternionHaar (N width) (polyMul W
      (polyMul (polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b)))
        (polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))))) ≤
      (1+sigma)*quaternionHaar (N width)
        (polyMul (polyMul W (polyMul G G)) (polyMul S S)) +
      (1+Q'.recipPos sigma hsigma)*quaternionHaar (N width) (polyMul W (polyMul e e)) := by
  dsimp only
  have hdA := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hA
  have hdb := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hb
  have hG := reciprocal_supported hA u hu k
  have hS := supported_add (supported_polyMul hA hdb) (support_neg (supported_polyMul hb hdA))
  have he := supported_polyMul hb (supported_polyMul
    (supported_add hG (support_neg
      (supported_polyMul hA (reciprocalSlope_supported hA u hu k)))) hdA)
  have hid := reciprocal_score_cleared_derivative (4*s+i) (4*s+j) A b u hu k
  have hrow : RatPolyCoeffEqv
      (polyMul W (polyMul (polyMul (reciprocal A u hu k) (conditionalScore (4*s+i) (4*s+j) A b))
        (polyMul (reciprocal A u hu k) (conditionalScore (4*s+i) (4*s+j) A b))))
      (polyMul (polyMul W (polyMul (reciprocal A u hu k) (reciprocal A u hu k)))
        (polyMul (conditionalScore (4*s+i) (4*s+j) A b) (conditionalScore (4*s+i) (4*s+j) A b))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => W | 1 => reciprocal A u hu k | _ => conditionalScore (4*s+i) (4*s+j) A b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hid.mul hid).mul_left W)))
    (QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_bound sigma hsigma PW
      (supported_polyMul hG hS) he (Q'.le_of_eqv (haar_of_coeff hrow))
      (Q'.le_of_eqv (Q'.eqv_refl _)))

/-- Actual output A=g_(n+r+1), b=T^(r+1)(g_n*psi), with the SAME
original source and reciprocal as the previous projected budget. -/
def exactScoreAngularBudget (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => (1+sigma)*quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (polyMul (conditionalScore (4*s+i) (4*s+j) A b)
          (conditionalScore (4*s+i) (4*s+j) A b))))
    else 0) (N width)

/-- The precise positive overestimate removed from the old angular budget.
The ORIGINAL projected conditional variance retains its actual kinetic mass. -/
def exactScoreJensenGap (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => (1+sigma)*quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (projectedActiveVariance w K width s i j a c)))
    else 0) (N width)

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
      iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) r 1 p).symm

private theorem add_exchange (a b c d : Q') : (a+b)+(c+d) ≈ (a+c)+(b+d) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem sum_add (f g : Nat → Q') : ∀ n,
    finSum (fun s => f s+g s) n ≈ finSum f n+finSum g n
  | 0 => by change (0 : Q') ≈ 0+0; decide
  | n+1 => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_add f g n) (Q'.eqv_refl _))
      (add_exchange _ _ _ _)

private theorem six_add (f g : Nat → Nat → Q') :
    sixValue (fun i j => f i j+g i j) ≈ sixValue f+sixValue g := by
  unfold sixValue
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (add_exchange _ _ _ _))
            (add_exchange _ _ _ _))) (add_exchange _ _ _ _))) (add_exchange _ _ _ _)))
    (add_exchange _ _ _ _)

/-- Exact equality, not just an order comparison: the discarded leading
budget is precisely the weighted ORIGINAL active conditional variance. -/
theorem exactScoreAngularBudget_gap_pin (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) :
    projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi k ≈
      exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k +
        exactScoreJensenGap sigma hw0 hw1 K width hK n r psi k := by
  unfold projectedDerivativeAngularBudget exactScoreAngularBudget exactScoreJensenGap
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun s => ?_) (N width))
    (sum_add _ _ (N width))
  split
  · refine Q'.eqv_trans _ _ _ (sixValue_congr _ _ (fun i j _ _ => ?_)) (six_add _ _)
    let S := conditionalScore (4*s+i) (4*s+j)
      (transferStep w K width (terminalMessage w K width (n+r)))
      (transferStep w K width (originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)))
    let B := lastStepProjectedDerivativeBudget w K width s i j
      (terminalMessage w K width (n+r))
      (originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi))
    have hid : RatPolyCoeffEqv B (polyAdd (polyMul S S) (polyAdd B (polyNeg (polyMul S S)))) :=
      coeffEvalExpr_eqv_of_normalize_eq (.var 0)
        (.add (.mul (.var 1) (.var 1)) (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))))
        (by decide) (fun | 0 => B | _ => S)
    have h := Q'.eqv_trans _ _ _ (haar_of_coeff (hid.mul_left
        (polyMul (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
          (polyMul (blockReciprocal hw0 hw1 K width
            (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) k)
            (blockReciprocal hw0 hw1 K width
              (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) k)))))
      (QuaternionHaarFamilySquare.haar_weighted_add (N width) _ _ _)
    have hh := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (1+sigma) _ _ h)
      (Q'.mul_add_eqv (1+sigma) _ _)
    dsimp only [S, B] at hh
    rw [terminal_output w K width n r, source_output w K width r] at hh
    simpa only [projectedActiveVariance, terminal_output, source_output] using hh
  · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem finite_sum_mono (f g : Nat → Q') : ∀ m,
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_refl' _
  | m+1, h => Q'.add_le_add
      (finite_sum_mono f g m (fun s hs => h s (by omega))) (h m (by omega))

/-- Constructed comparison for the SAME source, action and weights. This
does not assert that either angular budget is small relative to survival. -/
theorem exactScoreAngularBudget_le_projected (sigma : Q') (hsigma : (0 : Q') ≤ sigma)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k ≤
      projectedDerivativeAngularBudget sigma hw0 hw1 K width hK n r psi k := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  have ha : SupportedQuaternionBlocks (N width) a := terminalMessage_supported w K width (n+r)
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) r
      (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hG : SupportedQuaternionBlocks (N width) G :=
    reciprocal_supported (terminalMessage_supported w K width (n+(r+1))) _ _ k
  have hcoef : (0 : Q') ≤ 1+sigma := Q'.zero_le_add _ _ Q'.zero_le_one hsigma
  unfold exactScoreAngularBudget projectedDerivativeAngularBudget
  apply finite_sum_mono
  intro s hs
  split
  · rename_i hactive
    apply sixValue_mono
    intro i j hi hj
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    have hid : RatPolyCoeffEqv (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G)) (polyMul S S))
        (polyMul (polyMul Vbar Vbar) (polyMul (polyMul G S) (polyMul G S))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => polyMul Vbar Vbar | 1 => G | _ => S)
    have h := Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hid))
      (lastStep_projectedDerivative_weighted_multiplier_square_le hw0 hw1 K width hhead
        s i j (activeBlocks_lt width s hactive) hi hj ha hc
        (Certificate.square Vbar (spatialFringeMass_supported w K width)) hG)
    have hh := Q'.mul_le_mul_of_nonneg_left _ _ (1+sigma) h hcoef
    dsimp only [S, a, c] at hh
    rw [terminal_output w K width n r, source_output w K width r] at hh
    exact hh
  · exact Q'.le_refl' _

#print axioms exact_score_reciprocal_plane_le
#print axioms exactScoreAngularBudget
#print axioms exactScoreJensenGap
#print axioms exactScoreAngularBudget_gap_pin
#print axioms exactScoreAngularBudget_le_projected

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget
