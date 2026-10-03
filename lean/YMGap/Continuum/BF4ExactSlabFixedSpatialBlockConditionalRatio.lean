/-
# Polynomial conditional ratios of the ORIGINAL finite block

For A=g_(n+t) and b=T^t(g_n*psi), a certified interval for psi produces
the actual relative certificates C*A plus/minus b. The fresh last transfer step
constructs a positive window for A. Its floor/cap ratio cancels the previous
terminal mass, leaving precisely the existing nome/width-dependent mixRate.
The explicit polynomial ratios have square cap C^2 without a reciprocal
floor in that cap, and reconstruct b in the SAME original V-weighted norm.
No angular convergence, signed-cost estimate, survival or scaling is proved.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
import YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm
import YMGap.Continuum.QuaternionHaarReciprocalWeightedError
import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
import YMGap.Continuum.BF4DyadicWilsonSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm
open YMGap.Continuum.QuaternionHaarReciprocalWeightedError
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (ownCenteredBound)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight terminalMessage
  weightedMass

def blockWindowLower (w : Q') (K width n t : Nat) : Q' :=
  kineticFloor w width * weightedMass w K width (terminalMessage w K width (n+t-1))

def blockWindowUpper (w : Q') (K width n t : Nat) : Q' :=
  kineticCap w width * weightedMass w K width (terminalMessage w K width (n+t-1))

theorem blockWindowLower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    (0 : Q') < blockWindowLower w K width n t :=
  Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
    (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1))

theorem blockWindowUpper_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    (0 : Q') < blockWindowUpper w K width n t :=
  Q'.mul_pos (kineticCap_positive hw0 hw1 width)
    (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1))

private theorem window_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
  Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1)))

private theorem terminal_predecessor (w : Q') (K width n t : Nat) (hdepth : 1 ≤ n+t) :
    transferStep w K width (terminalMessage w K width (n+t-1)) =
      terminalMessage w K width (n+t) :=
  (terminalMessage_next w K width (n+t-1)).trans
    (congrArg (terminalMessage w K width) (show n+t-1+1 = n+t by omega))

/-- Both sides of the window are CONSTRUCTED from the original last step. -/
def blockWindowCertificates {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t) :
    Certificate (N width) (polyAdd (terminalMessage w K width (n+t))
      (polyNeg (cap (blockWindowLower w K width n t)))) ×
    Certificate (N width) (polyAdd (cap (blockWindowUpper w K width n t))
      (polyNeg (terminalMessage w K width (n+t)))) := by
  have L := transferStepLowerCertificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+t-1))
    (terminalMessage_certificate hw0 hw1 K width hK (n+t-1))
  have U := transferStepUpperCertificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+t-1))
    (terminalMessage_certificate hw0 hw1 K width hK (n+t-1))
  rw [terminal_predecessor w K width n t hdepth] at L U
  exact ⟨L, U⟩

private theorem block_terminal (w : Q') (K width n t : Nat) :
    originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n t polyOne).symm

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      transferStep w K width (originalBlockTransfer w K width t p) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem block_linear (w : Q') (K width : Nat) :
    (t : Nat) → (c d : Q') → (p q : RatPoly) →
    RatPolyCoeffEqv (originalBlockTransfer w K width t (polyAdd (polySmul c p) (polySmul d q)))
      (polyAdd (polySmul c (originalBlockTransfer w K width t p))
        (polySmul d (originalBlockTransfer w K width t q)))
  | 0, _, _, _, _ => RatPolyCoeffEqv.refl _
  | t+1, c, d, p, q => by
      rw [block_succ, block_succ, block_succ]
      exact (transfer_congr w K width (block_linear w K width t c d p q)).trans
        ((transferStep_add w K width _ _).trans
          ((transferStep_smul w K width c _).add (transferStep_smul w K width d _)))

private theorem block_congr (w : Q') (K width : Nat) :
    (t : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
    RatPolyCoeffEqv (originalBlockTransfer w K width t p) (originalBlockTransfer w K width t q)
  | 0, _, _, h => h
  | t+1, _, _, h => by
      rw [block_succ, block_succ]
      exact transfer_congr w K width (block_congr w K width t h)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Positivity of the FULL original block supplies both relative source signs. -/
def blockRelativeCertificates {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) {psi : RatPoly} {C : Q'}
    (I : Interval (N width) psi C) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    Certificate (N width) (polyAdd (polyMul (cap C) A) b) ×
    Certificate (N width) (polyAdd (polyMul (cap C) A) (polyNeg b)) := by
  dsimp only
  let g := terminalMessage w K width n
  let p := polyMul g psi
  have hg := terminalMessage_supported w K width n
  have G := terminalMessage_certificate hw0 hw1 K width hK n
  have initial_plus : RatPolyCoeffEqv (polyMul g (polyAdd (cap C) psi))
      (polyAdd (polySmul C g) (polySmul 1 p)) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.mul_comm g (cap C)).trans (cap_mul_left C g)).add
        (RatPolyCoeffEqv.one_smul p).symm)
  have initial_minus : RatPolyCoeffEqv (polyMul g (polyAdd (cap C) (polyNeg psi)))
      (polyAdd (polySmul C g) (polySmul (-1) p)) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.mul_comm g (cap C)).trans (cap_mul_left C g)).add
        (((RatPolyCoeffEqv.refl g).mul (neg_smul psi)).trans
          (RatPolyCoeffEqv.polyMul_smul_right (-1) g psi)))
  have L := iterateStep_certificate hw0 hw1 K width hK t _
    (supported_polyMul hg (supported_add (support_smul (supported_one _) C) I.support))
    (G.mul I.lower)
  have U := iterateStep_certificate hw0 hw1 K width hK t _
    (supported_polyMul hg (supported_add (support_smul (supported_one _) C)
      (support_neg I.support))) (G.mul I.upper)
  have pl := (block_congr w K width t initial_plus).trans (block_linear w K width t C 1 g p)
  have pu := (block_congr w K width t initial_minus).trans (block_linear w K width t C (-1) g p)
  rw [block_terminal w K width n t] at pl pu
  have pl' := pl.trans ((cap_mul_left C _).symm.add (RatPolyCoeffEqv.one_smul _))
  have pu' := pu.trans ((cap_mul_left C _).symm.add (neg_smul _).symm)
  exact ⟨Certificate.ofCoeff pl'.symm L, Certificate.ofCoeff pu'.symm U⟩

def blockReciprocal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) : RatPoly :=
  reciprocal (terminalMessage w K width (n+t)) (blockWindowUpper w K width n t)
    (blockWindowUpper_positive hw0 hw1 K width hK n t) k

def blockConditionalRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  polyMul (blockReciprocal hw0 hw1 K width hK n t k)
    (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi))

private theorem source_supported (w : Q') (K width n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    t (supported_polyMul (terminalMessage_supported w K width n) hp)

theorem blockConditionalRatio_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    SupportedQuaternionBlocks (N width) (blockConditionalRatio hw0 hw1 K width hK n t psi k) :=
  supported_polyMul (reciprocal_supported (terminalMessage_supported w K width (n+t))
    _ _ k) (source_supported w K width n t hp)

/-- The cap does NOT divide by the lower terminal window. -/
def blockConditionalRatio_squareCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} {C : Q'} (I : Interval (N width) psi C) (k : Nat) :
    Certificate (N width) (polyAdd (cap (C*C))
      (polyNeg (polyMul (blockConditionalRatio hw0 hw1 K width hK n t psi k)
        (blockConditionalRatio hw0 hw1 K width hK n t psi k)))) :=
  reciprocal_dual_square_certificate (terminalMessage_supported w K width (n+t))
    (source_supported w K width n t I.support)
    (blockWindowLower_positive hw0 hw1 K width hK n t)
    (blockWindowUpper_positive hw0 hw1 K width hK n t)
    (window_order hw0 hw1 K width hK n t) I.nonnegative
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2
    (blockRelativeCertificates hw0 hw1 K width hK n t I).1
    (blockRelativeCertificates hw0 hw1 K width hK n t I).2 k

/-- Exact cancellation of the previous terminal mass in the reciprocal rate. -/
theorem blockWindow_radius_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    radius (blockWindowLower w K width n t) (blockWindowUpper w K width n t)
      (blockWindowUpper_positive hw0 hw1 K width hK n t) ≈ mixRate hw0 hw1 width := by
  let u := blockWindowUpper w K width n t
  let l := blockWindowLower w K width n t
  let s := scale u (blockWindowUpper_positive hw0 hw1 K width hK n t)
  have hsu : s*u ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv u (blockWindowUpper_positive hw0 hw1 K width hK n t))
  have huf : u*mixFraction hw0 hw1 width ≈ l :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
        (fun
          | 0 => kineticCap w width
          | 1 => weightedMass w K width (terminalMessage w K width (n+t-1))
          | _ => mixFraction hw0 hw1 width))
      (Q'.mul_eqv_congr_right _ _ _ (mixFraction_mul_cap hw0 hw1 width))
  have hsl : s*l ≈ mixFraction hw0 hw1 width :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm huf))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv s u _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hsu) (Q'.one_mul_eqv _)))
  exact Q'.add_eqv_congr' (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ hsl)

private theorem weighted_pin (w : Q') (K width : Nat) (p : RatPoly) :
    weightedPair (N width) (spatialWeight w K width) p p ≈
      weightedMass w K width (polyMul p p) := by
  unfold weightedPair weightedMass
  exact haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)

/-- Relative reconstruction in the SAME original spatially weighted norm. -/
theorem blockConditionalRatio_reconstruction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let e := polyAdd b (polyNeg (polyMul A (blockConditionalRatio hw0 hw1 K width hK n t psi k)))
    weightedMass w K width (polyMul e e) ≤
      (mixRate hw0 hw1 width)^(2*k) * weightedMass w K width (polyMul b b) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let u := blockWindowUpper w K width n t
  let hu := blockWindowUpper_positive hw0 hw1 K width hK n t
  let E := reciprocalWeightedError b A u hu k
  let e := polyAdd b (polyNeg (polyMul A (blockConditionalRatio hw0 hw1 K width hK n t psi k)))
  have he : RatPolyCoeffEqv e E :=
    (RatPolyCoeffEqv.refl b).add (RatPolyCoeffEqv.neg
      ((RatPolyCoeffEqv.mul_comm A _).trans
        ((RatPolyCoeffEqv.mul_comm _ b).mul_right A)))
  have hbound := reciprocal_weighted_error_le
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
    (terminalMessage_supported w K width (n+t)) (source_supported w K width n t hp)
    hu (window_order hw0 hw1 K width hK n t)
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k
  have hr := Q'.pow_eqv_congr (blockWindow_radius_pin hw0 hw1 K width hK n t) k
  have hrate : (radius (blockWindowLower w K width n t) u hu)^k *
      (radius (blockWindowLower w K width n t) u hu)^k ≈
        (mixRate hw0 hw1 width)^(2*k) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr)
        (by simpa only [Nat.two_mul] using (Q'.pow_add_eqv (mixRate hw0 hw1 width) k k).symm))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weightedMass_congr w K width (he.mul he))
      (Q'.eqv_symm (weighted_pin w K width E))))
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hrate)
        (Q'.mul_eqv_congr_left _ _ _ (weighted_pin w K width b)))))

/-- Computed depth/amplitude-independent reconstruction onset; nome and width
remain in the actual mixRate. Zero rate is handled by the existing cutoff. -/
def blockRatioCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width) 1 epsilon

theorem blockConditionalRatio_reconstruction_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockRatioCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let e := polyAdd b (polyNeg (polyMul A (blockConditionalRatio hw0 hw1 K width hK n t psi k)))
    weightedMass w K width (polyMul e e) ≤ epsilon*weightedMass w K width (polyMul b b) := by
  dsimp only
  have hg := PositiveContractionResidual.geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    Q'.zero_le_one hepsilon (2*k) (Nat.le_trans hk (by omega))
  have hr : (mixRate hw0 hw1 width)^(2*k) ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hg
  have hs := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square _ (source_supported w K width n t hp))
  exact Q'.le_trans' _ _ _
    (blockConditionalRatio_reconstruction hw0 hw1 K width hK n t hdepth hp k)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hr hs)

/-- Literal original OWN-centered padded square; cap17 is constructed from
the existing centered square cap16, not supplied as a new source premise. -/
def ownPaddedSquareInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    Interval (N width)
      (shifted (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
        (ownMean hw0 hw1 K width hK n (paddedSquare scale width hwidth))) 17 :=
  Interval.changeCap (by decide : (16 : Q')+1 ≈ (17 : Q'))
    (Interval.ofSquare (ownCenteredBound hw0 hw1 K width hK n
      (paddedSquare scale width hwidth)))

def ownPaddedSquareRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t scale : Nat)
    (hwidth : side scale < width) (k : Nat) : RatPoly :=
  blockConditionalRatio hw0 hw1 K width hK n t
    (shifted (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
      (ownMean hw0 hw1 K width hK n (paddedSquare scale width hwidth))) k

/-- Actual OWN square source, with no unpaid interval or mean-bound input. -/
def ownPaddedSquareRatio_squareCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t scale : Nat)
    (hdepth : 1 ≤ n+t) (hwidth : side scale < width) (k : Nat) :
    Certificate (N width) (polyAdd (cap ((17 : Q')*17))
      (polyNeg (polyMul (ownPaddedSquareRatio hw0 hw1 K width hK n t scale hwidth k)
        (ownPaddedSquareRatio hw0 hw1 K width hK n t scale hwidth k)))) :=
  blockConditionalRatio_squareCertificate hw0 hw1 K width hK n t hdepth
    (ownPaddedSquareInterval hw0 hw1 K width hK n scale hwidth) k

#print axioms blockWindowLower
#print axioms blockWindowUpper
#print axioms blockWindowLower_positive
#print axioms blockWindowUpper_positive
#print axioms blockWindowCertificates
#print axioms blockRelativeCertificates
#print axioms blockReciprocal
#print axioms blockConditionalRatio
#print axioms blockConditionalRatio_supported
#print axioms blockConditionalRatio_squareCertificate
#print axioms blockWindow_radius_pin
#print axioms blockConditionalRatio_reconstruction
#print axioms blockRatioCutoff
#print axioms blockConditionalRatio_reconstruction_tolerance
#print axioms ownPaddedSquareInterval
#print axioms ownPaddedSquareRatio
#print axioms ownPaddedSquareRatio_squareCertificate

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
