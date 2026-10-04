/-
# Reconstruct the ORIGINAL last-step score with a computed error

For a=g_(n+r), c=T^r(g_n psi), the incoming finite ratio phi_k
reconstructs c as a*phi_k+e_k. Both original outputs are retained.
The last-step ratio-noise bounds the first score; the original paired
score bounds the correction. A constructed error certificate gives
J(a,e_k)<=rho^(2k)*P(a)*T(c^2). An asymmetric square triangle retains
leading coefficient 1+eta, and a computed cutoff makes the correction
arbitrarily small in any FIXED certified output weight.

No incoming source, variance or surviving norm is inverted. The rate
depends on nome/width and the error coefficient on the actual window,
source and output weight. This is NOT a changing-family relative noise
estimate, a cancellation of signed drift, or continuum survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget
import YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exact_score_reciprocal_plane_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff relativeCap headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left gap)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle (weighted_square_add_bound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight terminalMessage

/-- The actual transmitted source, before the final original transfer. -/
def incomingNumerator (w : Q') (K width n r : Nat) (psi : RatPoly) : RatPoly :=
  originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)

private theorem incoming_supported (w : Q') (K width n r : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width) (incomingNumerator w K width n r psi) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    r (supported_polyMul (terminalMessage_supported w K width n) hpsi)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Error of the INCOMING reciprocal, not the outgoing ratio. -/
def incomingRatioError {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  polyAdd (incomingNumerator w K width n r psi)
    (polyNeg (polyMul (terminalMessage w K width (n+r))
      (blockConditionalRatio hw0 hw1 K width hK n r psi k)))

private theorem error_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    SupportedQuaternionBlocks (N width) (incomingRatioError hw0 hw1 K width hK n r psi k) :=
  supported_add (incoming_supported w K width n r hpsi)
    (support_neg (supported_polyMul (terminalMessage_supported w K width (n+r))
      (blockConditionalRatio_supported hw0 hw1 K width hK n r hpsi k)))

/-- A polynomial cone certificate, before any choice of output weight.
The positive incoming window and its reciprocal are both constructed. -/
def incomingRatioError_square_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let c := incomingNumerator w K width n r psi
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    Certificate (N width) (polyAdd
      (polyMul (cap ((mixRate hw0 hw1 width)^(2*k))) (polyMul c c))
      (polyNeg (polyMul e e))) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let c := incomingNumerator w K width n r psi
  let u := blockWindowUpper w K width n r
  let hu := blockWindowUpper_positive hw0 hw1 K width hK n r
  let G := reciprocal a u hu k
  let E := polyAdd (polyMul a G) (polyNeg polyOne)
  let t := radius (blockWindowLower w K width n r) u hu ^ k
  have horder : blockWindowLower w K width n r ≤ u :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+r-1)))
  let I := multiplierErrorInterval (terminalMessage_supported w K width (n+r)) hu horder
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).2 k
  let S := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (QuaternionHaarSignedInterval.Interval.neg I)
  have P := (Certificate.square c (incoming_supported w K width n r hpsi)).mul S.certificate
  have he : RatPolyCoeffEqv (incomingRatioError hw0 hw1 K width hK n r psi k)
      (polyMul c (polyNeg E)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.mul (.var 2) (.var 0)))))
      (.mul (.var 0) (.neg (.add (.mul (.var 1) (.var 2)) (.neg (.const 1)))))
      (by decide) (fun | 0 => c | 1 => a | _ => G)
  have hid : RatPolyCoeffEqv (polyAdd (polyMul (cap (t*t)) (polyMul c c))
      (polyNeg (polyMul (incomingRatioError hw0 hw1 K width hK n r psi k)
        (incomingRatioError hw0 hw1 K width hK n r psi k))))
      (polyMul (polyMul c c) (gap (t*t) (polyNeg E))) :=
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (he.mul he))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))
        (.mul (.mul (.var 1) (.var 1))
          (.add (.var 0) (.neg (.mul (.var 2) (.var 2)))))
        (by decide) (fun | 0 => cap (t*t) | 1 => c | _ => polyNeg E))
  have hr := Q'.pow_eqv_congr (blockWindow_radius_pin hw0 hw1 K width hK n r) k
  have hrate : t*t ≈ (mixRate hw0 hw1 width)^(2*k) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr)
        (by simpa only [Nat.two_mul] using (Q'.pow_add_eqv (mixRate hw0 hw1 width) k k).symm))
  exact Certificate.ofCoeff
    ((((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm hrate) polyOne).mul_right (polyMul c c)).add
      (RatPolyCoeffEqv.refl _)).trans hid) P

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem transfer_neg (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polyNeg p)) (polyNeg (transferStep w K width p)) :=
  (transfer_congr w K width (neg_smul p)).trans
    ((transferStep_smul w K width (-1) p).trans (neg_smul _).symm)

/-- A fixed, actual-source envelope for the correction; no norm inverse. -/
def incomingErrorEnvelope (w : Q') (K width n r : Nat) (psi : RatPoly) : RatPoly :=
  polyMul (lastStepErrorBudgetMultiplier w K width (terminalMessage w K width (n+r)))
    (transferStep w K width (polyMul (incomingNumerator w K width n r psi)
      (incomingNumerator w K width n r psi)))

private def envelope_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    Certificate (N width) (incomingErrorEnvelope w K width n r psi) :=
  (lastStepErrorBudgetMultiplier_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+r))).mul
    (transferStep_certificate hw0 hw1 K width hK
      (supported_polyMul (incoming_supported w K width n r hpsi)
        (incoming_supported w K width n r hpsi))
      (Certificate.square _ (incoming_supported w K width n r hpsi)))

/-- The complete original paired correction has a geometric certificate. -/
def incomingRatioError_budget_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    Certificate (N width) (polyAdd
      (polyMul (cap ((mixRate hw0 hw1 width)^(2*k))) (incomingErrorEnvelope w K width n r psi))
      (polyNeg (lastStepScoreBudget w K width a e))) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let c := incomingNumerator w K width n r psi
  let e := incomingRatioError hw0 hw1 K width hK n r psi k
  let v := (mixRate hw0 hw1 width)^(2*k)
  let P := lastStepErrorBudgetMultiplier w K width a
  have hc := incoming_supported w K width n r hpsi
  have he := error_supported hw0 hw1 K width hK n r hpsi k
  have hv : SupportedQuaternionBlocks (N width) (cap v) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact supported_one (N width) s hs
  have T := transferStep_certificate hw0 hw1 K width hK
    (supported_add (supported_polyMul hv (supported_polyMul hc hc))
      (support_neg (supported_polyMul he he)))
    (incomingRatioError_square_certificate hw0 hw1 K width hK n r hdepth hpsi k)
  have ht : RatPolyCoeffEqv
      (transferStep w K width (polyAdd (polyMul (cap v) (polyMul c c))
        (polyNeg (polyMul e e))))
      (polyAdd (polyMul (cap v) (transferStep w K width (polyMul c c)))
        (polyNeg (transferStep w K width (polyMul e e)))) :=
    (transferStep_add w K width _ _).trans
      (((transfer_congr w K width (cap_mul_left v (polyMul c c))).trans
        ((transferStep_smul w K width v _).trans (cap_mul_left v _).symm)).add
        (transfer_neg w K width _))
  have PC := lastStepErrorBudgetMultiplier_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+r))
  have J := lastStepScoreBudget_error_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+r)) he
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (cap v) (incomingErrorEnvelope w K width n r psi))
        (polyNeg (lastStepScoreBudget w K width a e)))
      (polyAdd (polyMul P (polyAdd
        (polyMul (cap v) (transferStep w K width (polyMul c c)))
        (polyNeg (transferStep w K width (polyMul e e)))))
        (polyAdd (polyMul P (transferStep w K width (polyMul e e)))
          (polyNeg (lastStepScoreBudget w K width a e)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 4)))
      (.add (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))))
        (.add (.mul (.var 1) (.var 3)) (.neg (.var 4))))
      (by decide) (fun
        | 0 => cap v | 1 => P | 2 => transferStep w K width (polyMul c c)
        | 3 => transferStep w K width (polyMul e e) | _ => lastStepScoreBudget w K width a e)
  exact Certificate.ofCoeff hid ((PC.mul (Certificate.ofCoeff ht.symm T)).add J)

private theorem weighted_certificate_le {blocks : Nat} {W B p : RatPoly} {v : Q'}
    (MW : Certificate blocks W)
    (C : Certificate blocks (polyAdd (polyMul (cap v) B) (polyNeg p))) :
    quaternionHaar blocks (polyMul W p) ≤ v*quaternionHaar blocks (polyMul W B) := by
  have hn := (MW.mul C).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W p) (polyMul W (polyAdd (polyMul (cap v) B) (polyNeg p))))
      (polyMul (cap v) (polyMul W B)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.var 0) (.add (.mul (.var 2) (.var 3)) (.neg (.var 1)))))
      (.mul (.var 2) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => W | 1 => p | 2 => cap v | _ => B)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left v _)))
      (quaternionHaar_polySmul blocks v _))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

private theorem score_congr (i j : Nat) (A : RatPoly) {b c : RatPoly}
    (h : RatPolyCoeffEqv b c) : RatPolyCoeffEqv (conditionalScore i j A b) (conditionalScore i j A c) :=
  ((angularDerivative_congr i j h).mul_left A).add
    (RatPolyCoeffEqv.neg (h.mul_right (angularDerivative i j A)))

private theorem score_add (i j : Nat) (A b c : RatPoly) :
    RatPolyCoeffEqv (conditionalScore i j A (polyAdd b c))
      (polyAdd (conditionalScore i j A b) (conditionalScore i j A c)) :=
  (((angularDerivative_add i j b c).mul_left A).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.neg (.mul (.add (.var 3) (.var 4)) (.var 5))))
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 3) (.var 5))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 4) (.var 5)))))
      (by decide) (fun
        | 0 => A | 1 => angularDerivative i j b | 2 => angularDerivative i j c
        | 3 => b | 4 => c | _ => angularDerivative i j A))

/-- Explicit fixed-window correction amplitude; it never divides by a source. -/
def incomingScoreErrorCoefficient (w : Q') (K width n r : Nat) (psi W : RatPoly)
    (eta : Q') (heta : (0 : Q') < eta) : Q' :=
  (1+Q'.recipPos eta heta)*(relativeCap w 32*relativeCap w 32)*
    quaternionHaar (N width) (polyMul W (incomingErrorEnvelope w K width n r psi))

/-- ORIGINAL score = incoming-ratio score + transferred reconstruction score.
The last-step conditional noise is the leading term, not accumulated noise. -/
theorem original_lastStep_incomingRatio_score_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi W : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (MW : Certificate (N width) W)
    (eta : Q') (heta : (0 : Q') < eta) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let S := conditionalScore (4*s+i) (4*s+j) A b
    quaternionHaar (N width) (polyMul W (polyMul S S)) ≤
      (1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul W (polyMul (polyMul A A) (lastStepRatioNoise w K width (n+r) phi)))) +
      (mixRate hw0 hw1 width)^(2*k)*incomingScoreErrorCoefficient w K width n r psi W eta heta := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let c := incomingNumerator w K width n r psi
  let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
  let e := incomingRatioError hw0 hw1 K width hhead n r psi k
  let b0 := transferStep w K width (polyMul a phi)
  let b1 := transferStep w K width e
  let S0 := conditionalScore (4*s+i) (4*s+j) A b0
  let S1 := conditionalScore (4*s+i) (4*s+j) A b1
  let L := relativeCap w 32*relativeCap w 32
  have ha := terminalMessage_supported w K width (n+r)
  have he := error_supported hw0 hw1 K width hhead n r hpsi k
  have hp := blockConditionalRatio_supported hw0 hw1 K width hhead n r hpsi k
  have hA := transferStep_supported w K width ha
  have hsn := activeBlocks_lt width s hs
  have hix : 4*s+i < 4*(N width) := by omega
  have hjx : 4*s+j < 4*(N width) := by omega
  have score_support {b : RatPoly} (hb : SupportedQuaternionBlocks (N width) b) :
      SupportedQuaternionBlocks (N width) (conditionalScore (4*s+i) (4*s+j) A b) :=
    supported_add (supported_polyMul hA (angularDerivative_supported_at hix hjx hb))
      (support_neg (supported_polyMul hb (angularDerivative_supported_at hix hjx hA)))
  have hS0 := score_support (transferStep_supported w K width (supported_polyMul ha hp))
  have hS1 := score_support (transferStep_supported w K width he)
  have h0 := weighted_certificate_le MW
    (lastStepRatioNoise_score_certificate hw0 hw1 K width hK (n+r) s hs hi hj hp)
  have hjerr := weighted_certificate_le MW
    (incomingRatioError_budget_certificate hw0 hw1 K width hhead n r hdepth hpsi k)
  have h1 := Q'.le_trans' _ _ _
    (weighted_certificate_le MW (lastStep_score_certificate hw0 hw1 K width hK s hs hi hj ha he))
    (Q'.mul_le_mul_of_nonneg_left _ _ L hjerr (SumOfSquares.q_mul_self_nonneg (relativeCap w 32)))
  have hsplit : RatPolyCoeffEqv c (polyAdd (polyMul a phi) e) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.mul (.var 1) (.var 2))
        (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))))
      (by decide) (fun | 0 => c | 1 => a | _ => phi)
  have hS := (score_congr (4*s+i) (4*s+j) A
    ((transfer_congr w K width hsplit).trans (transferStep_add w K width _ _))).trans
      (score_add (4*s+i) (4*s+j) A b0 b1)
  have ht := weighted_square_add_bound eta heta MW hS0 hS1 h0 h1
  have hright :
      (1+eta)*(L*quaternionHaar (N width)
        (polyMul W (polyMul (polyMul A A) (lastStepRatioNoise w K width (n+r) phi)))) +
      (1+Q'.recipPos eta heta)*(L*((mixRate hw0 hw1 width)^(2*k)*
        quaternionHaar (N width) (polyMul W (incomingErrorEnvelope w K width n r psi)))) ≈
      (1+eta)*(L*quaternionHaar (N width)
        (polyMul W (polyMul (polyMul A A) (lastStepRatioNoise w K width (n+r) phi)))) +
      (mixRate hw0 hw1 width)^(2*k)*incomingScoreErrorCoefficient w K width n r psi W eta heta :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
        (by decide) (fun
          | 0 => 1+Q'.recipPos eta heta | 1 => L | 2 => (mixRate hw0 hw1 width)^(2*k)
          | _ => quaternionHaar (N width) (polyMul W (incomingErrorEnvelope w K width n r psi))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hS.mul hS).mul_left W)))
    (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv hright))

/-- The ACTUAL outgoing reciprocal cancels the leading A^2 by a constructed
multiplier certificate, not by division. Its degree l is independent of k.
This is the score form required by the existing exact-score gradient consumer. -/
theorem original_lastStep_incomingRatio_reciprocal_score_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi W : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (MW : Certificate (N width) W)
    (eta : Q') (heta : (0 : Q') < eta) (k l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let M := polyMul W (polyMul G G)
    let S := conditionalScore (4*s+i) (4*s+j) A b
    quaternionHaar (N width) (polyMul M (polyMul S S)) ≤
      (1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul W (lastStepRatioNoise w K width (n+r) phi))) +
      (mixRate hw0 hw1 width)^(2*k)*incomingScoreErrorCoefficient w K width n r psi M eta heta := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := transferStep w K width (terminalMessage w K width (n+r))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  let noise := lastStepRatioNoise w K width (n+r) phi
  let L := relativeCap w 32*relativeCap w 32
  have hAt : terminalMessage w K width (n+(r+1)) = A := by
    rw [show n+(r+1) = (n+r)+1 by omega, ← terminalMessage_next w K width (n+r)]
  have hG : SupportedQuaternionBlocks (N width) G :=
    reciprocal_supported (terminalMessage_supported w K width (n+(r+1))) _ _ l
  have horder : blockWindowLower w K width n (r+1) ≤ blockWindowUpper w K width n (r+1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hhead (n+(r+1)-1)))
  have MQ := multiplierSquareCertificate
    (terminalMessage_supported w K width (n+(r+1)))
    (blockWindowLower_positive hw0 hw1 K width hhead n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) horder
    (blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)).1
    (blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)).2 l
  change Certificate (N width) (polyAdd polyOne (polyNeg
    (polyMul (polyMul (terminalMessage w K width (n+(r+1))) G)
      (polyMul (terminalMessage w K width (n+(r+1))) G)))) at MQ
  rw [hAt] at MQ
  have PN := lastStepRatioNoise_certificate hw0 hw1 K width hhead (n+r)
    (blockConditionalRatio_supported hw0 hw1 K width hhead n r hpsi k)
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (cap 1) noise)
        (polyNeg (polyMul (polyMul G G) (polyMul (polyMul A A) noise))))
      (polyMul (polyAdd polyOne (polyNeg (polyMul (polyMul A G) (polyMul A G)))) noise) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.const 1) (.var 0))
        (.neg (.mul (.mul (.var 1) (.var 1)) (.mul (.mul (.var 2) (.var 2)) (.var 0)))))
      (.mul (.add (.const 1) (.neg
        (.mul (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))))) (.var 0))
      (by decide) (fun | 0 => noise | 1 => G | _ => A)
  have hlead0 := weighted_certificate_le MW (Certificate.ofCoeff hid (MQ.mul PN))
  have hlead : quaternionHaar (N width)
      (polyMul (polyMul W (polyMul G G)) (polyMul (polyMul A A) noise)) ≤
      quaternionHaar (N width) (polyMul W noise) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W (polyMul G G) _)))
      (Q'.le_trans' _ _ _ hlead0 (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (1+eta)
    (Q'.mul_le_mul_of_nonneg_left _ _ L hlead (SumOfSquares.q_mul_self_nonneg (relativeCap w 32)))
    (Q'.zero_le_add 1 eta Q'.zero_le_one (Q'.le_of_lt heta))
  exact Q'.le_trans' _ _ _
    (original_lastStep_incomingRatio_score_square_le hw0 hw1 K width hK n r hdepth s hs hi hj
      hpsi (MW.mul (Certificate.square G hG)) eta heta k)
    (Q'.add_le_add hscale (Q'.le_of_eqv (Q'.eqv_refl _)))

/-- Concrete join to the existing exact-gradient consumer. Incoming noise
replaces the paired Jensen budget; BOTH finite approximation corrections
remain. k and l are independent, and no scaling or relative norm claim is made. -/
theorem original_lastStep_incomingRatio_gradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi W : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (MW : Certificate (N width) W)
    (eta sigma : Q') (heta : (0 : Q') < eta) (hsigma : (0 : Q') < sigma) (k l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) l
    quaternionHaar (N width) (polyMul W (polyMul d d)) ≤
      (1+sigma)*((1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul W (lastStepRatioNoise w K width (n+r) phi))) +
        (mixRate hw0 hw1 width)^(2*k)*incomingScoreErrorCoefficient w K width n r psi
          (polyMul W (polyMul G G)) eta heta) +
      (1+Q'.recipPos sigma hsigma)*quaternionHaar (N width) (polyMul W (polyMul e e)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let b := transferStep w K width (incomingNumerator w K width n r psi)
  let u := blockWindowUpper w K width n (r+1)
  let hu := blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  have hAt : terminalMessage w K width (n+(r+1)) = A := by
    rw [show n+(r+1) = (n+r)+1 by omega, ← terminalMessage_next w K width (n+r)]
  have hG : G = reciprocal A u hu l := by
    change reciprocal (terminalMessage w K width (n+(r+1))) u hu l = _
    rw [hAt]
  have hgrad := exact_score_reciprocal_plane_le sigma hsigma width s i j
    (activeBlocks_lt width s hs) hi hj A b W
    (transferStep_supported w K width (terminalMessage_supported w K width (n+r)))
    (transferStep_supported w K width (incoming_supported w K width n r hpsi)) MW u hu l
  dsimp only at hgrad
  rw [← hG] at hgrad
  have hscore := original_lastStep_incomingRatio_reciprocal_score_le
    hw0 hw1 K width hK n r hdepth s hs hi hj hpsi MW eta heta k l
  exact Q'.le_trans' _ _ _ hgrad
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ (1+sigma) hscore
        (Q'.zero_le_add 1 sigma Q'.zero_le_one (Q'.le_of_lt hsigma)))
      (Q'.le_of_eqv (Q'.eqv_refl _)))

/-- Computed onset for this actual window/weight/source, not a uniform family onset. -/
def incomingScoreErrorCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width n r : Nat) (psi W : RatPoly) (eta : Q') (heta : (0 : Q') < eta)
    (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
    (incomingScoreErrorCoefficient w K width n r psi W eta heta) epsilon

/-- The geometric correction actually vanishes at a computed cutoff.
Zero input is allowed; no zero surviving norm is identified with zero input. -/
theorem original_lastStep_incomingRatio_score_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi W : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (MW : Certificate (N width) W)
    (eta : Q') (heta : (0 : Q') < eta) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (k : Nat) (hk : incomingScoreErrorCutoff hw0 hw1 K width n r psi W eta heta epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let S := conditionalScore (4*s+i) (4*s+j) A b
    quaternionHaar (N width) (polyMul W (polyMul S S)) ≤
      (1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul W (polyMul (polyMul A A) (lastStepRatioNoise w K width (n+r) phi)))) + epsilon := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hC : (0 : Q') ≤ incomingScoreErrorCoefficient w K width n r psi W eta heta :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.zero_le_add 1 _ Q'.zero_le_one (Q'.le_of_lt (Q'.recipPos_pos eta heta)))
        (SumOfSquares.q_mul_self_nonneg (relativeCap w 32)))
      ((MW.mul (envelope_certificate hw0 hw1 K width hhead n r hpsi)).haar_nonnegative)
  have hg := PositiveContractionResidual.geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width) hC hepsilon
    (2*k) (Nat.le_trans hk (by omega))
  exact Q'.le_trans' _ _ _
    (original_lastStep_incomingRatio_score_square_le hw0 hw1 K width hK n r hdepth s hs hi hj
      hpsi MW eta heta k) (Q'.add_le_add_left _ _ _ hg)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.incomingRatioError_square_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.incomingRatioError_budget_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.original_lastStep_incomingRatio_score_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.original_lastStep_incomingRatio_reciprocal_score_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.original_lastStep_incomingRatio_gradient_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.incomingScoreErrorCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement.original_lastStep_incomingRatio_score_tolerance
