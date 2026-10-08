/-
# The original last-window prediction correction is paid together

Actual terminal comparison and arbitrary-input Schur produce
Z*||T^d r||_V^2 <= (1+eta)^2*W*||r||_V^2. At the constructed fixed-nome,
fixed-width depth onset, (1+eta)^2<=2. Weighted symmetry then makes
C=W*Id-Z*T^(2*d) contractive at scale W, without requiring C to be positive.
The actual finite reciprocal gives the complete signed prediction payment
2*mixRate^k*W*||b||_V^2. Both chronological masses and every spatial factor
are retained. Zero source norm, zero rate and d=0 are included.

This finite original-action estimate does not pay the relative innovation,
produce a scaling-uniform onset, or close any physical/continuum obligation.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurArbitrarySource
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedPredictionPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurArbitrarySource
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise blockNoise_variance_loss)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift (futureBlockDrift_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound (weightedMass_pair_square_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle (weighted_square_add_le)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.PositiveContractionResidual (geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

private def pair (w : Q') (K width : Nat) (p q : RatPoly) : Q' :=
  weightedMass w K width (polyMul p q)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem block_supported (w : Q') (K width d : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    SupportedQuaternionBlocks (N width) (originalBlockTransfer w K width d p) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) d hp

private theorem block_compose (w : Q') (K width d : Nat) (p : RatPoly) :
    originalBlockTransfer w K width d (originalBlockTransfer w K width d p) =
      originalBlockTransfer w K width (2*d) p := by
  simpa only [Nat.two_mul] using
    (iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) d d p).symm

private theorem terminal_block (w : Q') (K width m d : Nat) :
    originalBlockTransfer w K width d (terminalMessage w K width m) =
      terminalMessage w K width (m+d) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) m d polyOne).symm

private theorem pair_comm (w : Q') (K width : Nat) (p q : RatPoly) :
    pair w K width p q ≈ pair w K width q p :=
  weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)

private theorem pair_linear_right (w : Q') (K width : Nat) (p q r : RatPoly) (a b : Q') :
    pair w K width p (polyAdd (polySmul a q) (polySmul b r)) ≈
      a*pair w K width p q + b*pair w K width p r :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right _ _ _))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right a p q))
          (weightedMass_smul w K width a _))
        (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right b p r))
          (weightedMass_smul w K width b _))))

private theorem pair_linear_left (w : Q') (K width : Nat) (p q r : RatPoly) (a b : Q') :
    pair w K width (polyAdd (polySmul a p) (polySmul b q)) r ≈
      a*pair w K width p r + b*pair w K width q r :=
  Q'.eqv_trans _ _ _ (pair_comm w K width _ _)
    (Q'.eqv_trans _ _ _ (pair_linear_right w K width r p q a b)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (pair_comm w K width r p))
        (Q'.mul_eqv_congr_left _ _ _ (pair_comm w K width r q))))

private theorem square_linear (w : Q') (K width : Nat) (p q : RatPoly) (a b : Q') :
    let y := polyAdd (polySmul a p) (polySmul b q)
    pair w K width y y ≈
      (a*a)*pair w K width p p + (2*a*b)*pair w K width p q +
        (b*b)*pair w K width q q := by
  dsimp only
  have h := Q'.eqv_trans _ _ _ (pair_linear_left w K width p q _ a b)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (pair_linear_right w K width p p q a b))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (pair_linear_right w K width q p q a b)
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (pair_comm w K width q p))))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
      (.mul (.var 1) (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4)))))
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3)))
      (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
    (fun | 0 => a | 1 => b | 2 => pair w K width p p
         | 3 => pair w K width p q | _ => pair w K width q q))

private theorem block_pair (w : Q') (K width d : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q) :
    pair w K width p (originalBlockTransfer w K width (2*d) q) ≈
      pair w K width (originalBlockTransfer w K width d p) (originalBlockTransfer w K width d q) := by
  have h := iterateStep_weighted_symmetric w K width d (block_supported w K width d hq) hp
  change pair w K width p (originalBlockTransfer w K width d
      (originalBlockTransfer w K width d q)) ≈
    pair w K width (originalBlockTransfer w K width d q) (originalBlockTransfer w K width d p) at h
  rw [block_compose] at h
  exact Q'.eqv_trans _ _ _ h (pair_comm w K width _ _)

private theorem bracket_upper_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m d : Nat) (hm : 1 ≤ m) :
    (0 : Q') ≤ (filteredTerminalBracket hw0 hw1 K width hK m 0 d (by omega)).upper := by
  let J := filteredTerminalBracket hw0 hw1 K width hK m 0 d (by omega)
  let a := terminalMessage w K width m
  let A := terminalMessage w K width (m+d)
  have ha := terminalMessage_mass_positive hw0 hw1 K width hK m
  have hA := Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (m+d))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK J.upperCertificate
  have he : weightedMass w K width (polyAdd (polySmul J.upper a) (polySmul (-1) A)) ≈
      J.upper*weightedMass w K width a + -(weightedMass w K width A) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width J.upper a)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) A)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => weightedMass w K width A))))
  have hu := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  exact Q'.nonneg_of_mul_pos ha (Q'.le_trans' _ _ _ hA
    (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- The produced ORIGINAL terminal Schur comparison covers ANY supported
signed input, not just a transmitted source. Both chronological masses remain. -/
theorem original_arbitrary_normalized_schur_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (m : Nat) (hm : 1 ≤ m) (d : Nat) {r : RatPoly}
    (hr : SupportedQuaternionBlocks (N width) r) :
    let a := terminalMessage w K width m
    let A := terminalMessage w K width (m+d)
    let eta := comparisonEta hw0 hw1 width (m-1)
    pair w K width a a * pair w K width (originalBlockTransfer w K width d r)
      (originalBlockTransfer w K width d r) ≤
      ((1+eta)*(1+eta)) * (pair w K width A A * pair w K width r r) := by
  dsimp only
  let J := filteredTerminalBracket hw0 hw1 K width hK m 0 d (by omega)
  let l := J.lower
  let H := J.upper
  let F := 1+comparisonEta hw0 hw1 width (m-1)
  let Z := pair w K width (terminalMessage w K width m) (terminalMessage w K width m)
  let W := pair w K width (terminalMessage w K width (m+d)) (terminalMessage w K width (m+d))
  let B := pair w K width r r
  have hl : (0 : Q') ≤ l := Q'.le_of_lt
    (terminalComparison_lower_positive hw0 hw1 K width hK (m-1) d 0)
  have hH : (0 : Q') ≤ H := bracket_upper_nonnegative hw0 hw1 K width hK m d hm
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one
    (comparisonEta_nonnegative hw0 hw1 width (m-1))
  have hZ : (0 : Q') ≤ Z := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK m m)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square r hr)
  have PU : Certificate (N width) (polyAdd (polySmul H (terminalMessage w K width m))
      (polyNeg (originalBlockTransfer w K width d (terminalMessage w K width m)))) := by
    rw [terminal_block]
    exact Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (neg_smul _)) J.upperCertificate
  have hn := original_block_terminal_schur_arbitrary_source_le hw0 hw1 K width hK m hm d hr H hH PU
  have hw := terminalComparison_relative_width hw0 hw1 K width hK (m-1) d 0
  have hHle : H ≤ F*l := by
    have h := Q'.add_le_add_right _ _ l hw
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => H | _ => l)))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.var 1))
        (.mul (.add (.const 1) (.var 0)) (.var 1)) (by decide)
        (fun | 0 => comparisonEta hw0 hw1 width (m-1) | _ => l))))
  have hHs : H*H ≤ (F*F)*(l*l) := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg hHle hHle (Q'.mul_nonneg _ _ hF hl) hH)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => F | _ => l)))
  have hlow : (l*l)*Z ≤ W := by
    simpa only [Nat.add_zero] using filtered_terminal_partition_lower hw0 hw1 K width hK m 0 d (by omega)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ Z hn hZ
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ Z
    (Q'.mul_le_mul_of_nonneg_right _ _ B hHs hB) hZ
  have he : Z*(((F*F)*(l*l))*B) ≈ (F*F)*(((l*l)*Z)*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3)))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.mul (.mul (.var 2) (.var 2)) (.var 0)) (.var 3)))
      (by decide) (fun | 0 => Z | 1 => F | 2 => l | _ => B)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ (F*F)
      (Q'.mul_le_mul_of_nonneg_right _ _ B hlow hB) (SumOfSquares.q_mul_self_nonneg F))))

private theorem onset_factor_le_two {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width m : Nat)
    (honset : blockConditionalDriftDepthCutoff hw0 hw1 width (⟨1, 3⟩ : Q') ≤ m-1) :
    (1+comparisonEta hw0 hw1 width (m-1))*(1+comparisonEta hw0 hw1 width (m-1)) ≤ 2 := by
  have heta : comparisonEta hw0 hw1 width (m-1) ≤ (⟨1, 3⟩ : Q') := by
    change comparisonKappa hw0 hw1 width * (mixRate hw0 hw1 width)^(m-1) ≤ (⟨1, 3⟩ : Q')
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (geometric_bound (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
        (comparisonKappa_nonnegative hw0 hw1 width) (by decide) (m-1) honset)
  have hf := Q'.add_le_add_left (1 : Q') _ _ heta
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg hf hf (by decide)
    (Q'.zero_le_add _ _ Q'.zero_le_one (comparisonEta_nonnegative hw0 hw1 width (m-1))))
    (by decide)

/-- The ACTUAL signed correction operator is contractive at scale W after
the produced fixed-nome/width onset. No positivity of this operator is used. -/
theorem original_signed_prediction_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (m : Nat) (hm : 1 ≤ m) (d : Nat)
    (honset : blockConditionalDriftDepthCutoff hw0 hw1 width (⟨1, 3⟩ : Q') ≤ m-1)
    {r : RatPoly} (hr : SupportedQuaternionBlocks (N width) r) :
    let a := terminalMessage w K width m
    let A := terminalMessage w K width (m+d)
    let Z := pair w K width a a
    let W := pair w K width A A
    let C := polyAdd (polySmul W r) (polySmul (-Z) (originalBlockTransfer w K width (2*d) r))
    pair w K width C C ≤ (W*W)*pair w K width r r := by
  dsimp only
  let Z := pair w K width (terminalMessage w K width m) (terminalMessage w K width m)
  let W := pair w K width (terminalMessage w K width (m+d)) (terminalMessage w K width (m+d))
  let S := (1+comparisonEta hw0 hw1 width (m-1))*(1+comparisonEta hw0 hw1 width (m-1))
  let U := originalBlockTransfer w K width d r
  let V := originalBlockTransfer w K width (2*d) r
  have hZ := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK m m)
  have hW := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (m+d) (m+d))
  have hU := block_supported w K width d hr
  have hUn := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square U hU)
  have h2 := original_arbitrary_normalized_schur_le hw0 hw1 K width hK m hm d hU
  dsimp only at h2
  rw [block_compose] at h2
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ Z h2 hZ
  have hpin : pair w K width (polyAdd (polySmul W r) (polySmul (-Z) V))
      (polyAdd (polySmul W r) (polySmul (-Z) V)) ≈
      (W*W)*pair w K width r r + -(2*W*Z*pair w K width U U) +
        Z*(Z*pair w K width V V) := by
    exact Q'.eqv_trans _ _ _ (square_linear w K width r V W (-Z))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (block_pair w K width d hr hr))))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
            (.mul (.mul (.mul (.const 2) (.var 0)) (.neg (.var 1))) (.var 3)))
            (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.var 4)))
          (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
            (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))))
            (.mul (.var 1) (.mul (.var 1) (.var 4)))) (by decide)
          (fun | 0 => W | 1 => Z | 2 => pair w K width r r
               | 3 => pair w K width U U | _ => pair w K width V V)))
  have hpaid := Q'.add_le_add_left ((W*W)*pair w K width r r + -(2*W*Z*pair w K width U U)) _ _ hscaled
  have hregroup : (W*W)*pair w K width r r + -(2*W*Z*pair w K width U U) +
      Z*(S*(W*pair w K width U U)) ≈
      (W*W)*pair w K width r r + ((S + -2)*W*Z)*pair w K width U U :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))))
        (.mul (.var 1) (.mul (.var 4) (.mul (.var 0) (.var 3)))))
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.add (.var 4) (.neg (.const 2))) (.var 0)) (.var 1)) (.var 3)))
      (by decide) (fun
        | 0 => W
        | 1 => Z
        | 2 => pair w K width r r
        | 3 => pair w K width U U
        | _ => S)
  have hnegative : ((S + -2)*W*Z)*pair w K width U U ≤ 0 := by
    have hs := Q'.add_le_add_right _ _ (-2) (onset_factor_le_two hw0 hw1 width m honset)
    have hs0 : S + -2 ≤ 0 := Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (by decide : (2 : Q') + -2 ≈ 0))
    have h := Q'.mul_le_mul_of_nonneg_right _ _ (W*Z*pair w K width U U) hs0
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hW hZ) hUn)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_symm
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
        (fun | 0 => S + -2 | 1 => W | 2 => Z | _ => pair w K width U U))))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.zero_mul_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) (Q'.le_trans' _ _ _ hpaid
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hnegative)
        (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))))))

private theorem abs_le_square {x c : Q'} (hc : (0 : Q') ≤ c) (h : x*x ≤ c*c) : Q'.abs x ≤ c := by
  have hab : Q'.abs x*Q'.abs x ≈ x*x := by
    unfold Q'.abs
    split
    · exact Q'.eqv_refl _
    · exact poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => x)
  have hs := Q'.le_trans' _ _ _ (Q'.le_of_eqv hab) h
  show (Q'.abs x).num * (c.den : Int) ≤ c.num * ((Q'.abs x).den : Int)
  apply Int.not_lt.mp
  intro hcx
  have hcx' : c < Q'.abs x := hcx
  have hx := Q'.lt_of_le_of_lt hc hcx'
  exact (Int.not_lt.mpr hs) (Q'.lt_of_le_of_lt
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hcx') hc)
    (Q'.mul_lt_mul_of_pos_left hx hcx'))

/-- The FOUR original last-window cross terms are controlled together for
the ACTUAL finite reciprocal. No source, norm, or error estimate is assumed. -/
theorem blockConditionalRatio_signedPrediction_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t d : Nat) (hdepth : 1 ≤ n+t)
    (honset : blockConditionalDriftDepthCutoff hw0 hw1 width (⟨1, 3⟩ : Q') ≤ n+t-1)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+t)
    let A := terminalMessage w K width (n+t+d)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let p := polyMul a (blockConditionalRatio hw0 hw1 K width hK n t psi k)
    let e := polyAdd b (polySmul (-1) p)
    let s := polyAdd b p
    Q'.abs (pair w K width A A * pair w K width e s +
      -(pair w K width a a * pair w K width (originalBlockTransfer w K width d e)
        (originalBlockTransfer w K width d s))) ≤
      2*(mixRate hw0 hw1 width)^k * pair w K width A A * pair w K width b b := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let A := terminalMessage w K width (n+t+d)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let p := polyMul a (blockConditionalRatio hw0 hw1 K width hK n t psi k)
  let e := polyAdd b (polySmul (-1) p)
  let s := polyAdd b p
  let Z := pair w K width a a
  let W := pair w K width A A
  let B := pair w K width b b
  let delta := (mixRate hw0 hw1 width)^k
  let C := polyAdd (polySmul W s) (polySmul (-Z) (originalBlockTransfer w K width (2*d) s))
  have hb := block_supported w K width t (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hp' := supported_polyMul (terminalMessage_supported w K width (n+t))
    (blockConditionalRatio_supported hw0 hw1 K width hK n t hp k)
  have he := supported_add hb (support_smul hp' (-1))
  have hs := supported_add hb hp'
  have hC := supported_add (support_smul hs W) (support_smul (block_supported w K width (2*d) hs) (-Z))
  have hB := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square b hb)
  have hW := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (n+t+d) (n+t+d))
  have hd := Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) k
  have hpn : pair w K width p p ≤ B := Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => a | _ => blockConditionalRatio hw0 hw1 K width hK n t psi k))))
    (blockConditionalRatio_surviving_square_le hw0 hw1 K width hK n t hdepth hp k)
  have hsn : pair w K width s s ≤ 4*B := by
    have h : pair w K width s s ≤ (B+B)+(pair w K width p p+pair w K width p p) := by
      simpa only [pair, weightedMass, s, B, b, p, a] using weighted_square_add_le
        (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK) hb hp'
    exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.le_refl' _) (Q'.add_le_add hpn hpn))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
        (.mul (.const 4) (.var 0)) (by decide) (fun _ => B))))
  have hep : RatPolyCoeffEqv e (polyAdd b (polyNeg p)) :=
    (RatPolyCoeffEqv.refl _).add (neg_smul p).symm
  have hen : pair w K width e e ≤ (delta*delta)*B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedMass_congr w K width (hep.mul hep)))
      (Q'.le_trans' _ _ _ (blockConditionalRatio_reconstruction hw0 hw1 K width hK n t hdepth hp k)
        (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (by
          simpa only [Nat.two_mul] using Q'.pow_add_eqv (mixRate hw0 hw1 width) k k))))
  have hCn : pair w K width C C ≤ (W*W)*(4*B) := Q'.le_trans' _ _ _
    (original_signed_prediction_square_le hw0 hw1 K width hK (n+t) hdepth d honset hs)
    (Q'.mul_le_mul_of_nonneg_left _ _ (W*W) hsn (SumOfSquares.q_mul_self_nonneg W))
  have hC0 := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square C hC)
  have heB0 := Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg delta) hB
  have hbound := Q'.le_trans' _ _ _ (weightedMass_pair_square_le hw0 hw1 K width hK he hC)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hen hC0)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hCn heB0))
  have hsq : pair w K width e C * pair w K width e C ≤ (2*delta*W*B)*(2*delta*W*B) :=
    Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.var 1) (.var 1)) (.mul (.const 4) (.var 2))))
      (.mul (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))) (by decide)
      (fun | 0 => delta | 1 => W | _ => B)))
  have hab := abs_le_square (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hd) hW) hB) hsq
  have hpin : pair w K width e C ≈ W*pair w K width e s +
      -(Z*pair w K width (originalBlockTransfer w K width d e) (originalBlockTransfer w K width d s)) :=
    Q'.eqv_trans _ _ _ (pair_linear_right w K width e s _ W (-Z))
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (block_pair w K width d he hs)) (Q'.neg_mul_eqv _ _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin)) hab

private theorem block_congr (w : Q') (K width : Nat) :
    (d : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (originalBlockTransfer w K width d p) (originalBlockTransfer w K width d q)
  | 0, _, _, h => h
  | d+1, p, q, h => by
      change RatPolyCoeffEqv (originalBlockTransfer w K width d (transferStep w K width p))
        (originalBlockTransfer w K width d (transferStep w K width q))
      exact block_congr w K width d (partialHaarHeads_congr (N width)
        ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width)))

private theorem block_signed_sum (w : Q') (K width : Nat) :
    (d : Nat) → (p q : RatPoly) → (c : Q') →
      RatPolyCoeffEqv (originalBlockTransfer w K width d (polyAdd p (polySmul c q)))
        (polyAdd (originalBlockTransfer w K width d p) (polySmul c (originalBlockTransfer w K width d q)))
  | 0, _, _, _ => RatPolyCoeffEqv.refl _
  | d+1, p, q, c => by
      change RatPolyCoeffEqv (originalBlockTransfer w K width d (transferStep w K width (polyAdd p (polySmul c q))))
        (polyAdd (originalBlockTransfer w K width d (transferStep w K width p))
          (polySmul c (originalBlockTransfer w K width d (transferStep w K width q))))
      exact (block_congr w K width d ((transferStep_add w K width _ _).trans
        ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width c q)))).trans
        (block_signed_sum w K width d (transferStep w K width p) (transferStep w K width q) c)

private theorem pair_difference (w : Q') (K width : Nat) (b p : RatPoly) :
    pair w K width (polyAdd b (polySmul (-1) p)) (polyAdd b p) ≈
      pair w K width b b + -(pair w K width p p) := by
  have hpoly : RatPolyCoeffEqv (polyMul (polyAdd b (polySmul (-1) p)) (polyAdd b p))
      (polyAdd (polyMul b b) (polyNeg (polyMul p p))) :=
    (((RatPolyCoeffEqv.refl _).add (neg_smul p).symm).mul (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
        (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => b | _ => p))
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width hpoly)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (weightedMass_congr w K width (neg_smul _))
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => pair w K width p p))))))

private theorem block_difference_pair (w : Q') (K width d : Nat) (b p : RatPoly) :
    pair w K width (originalBlockTransfer w K width d (polyAdd b (polySmul (-1) p)))
      (originalBlockTransfer w K width d (polyAdd b p)) ≈
      pair w K width (originalBlockTransfer w K width d b) (originalBlockTransfer w K width d b) +
        -(pair w K width (originalBlockTransfer w K width d p) (originalBlockTransfer w K width d p)) := by
  have hsum : RatPolyCoeffEqv (originalBlockTransfer w K width d (polyAdd b p))
      (polyAdd (originalBlockTransfer w K width d b) (originalBlockTransfer w K width d p)) :=
    (block_congr w K width d ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul p).symm)).trans
      ((block_signed_sum w K width d b p 1).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul _)))
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width ((block_signed_sum w K width d b p (-1)).mul hsum))
    (pair_difference w K width _ _)

private theorem noise_endpoint_pin (w : Q') (K width d : Nat) {a phi : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hphi : SupportedQuaternionBlocks (N width) phi) :
    weightedMass w K width (blockNoise w K width d a phi) ≈
      weightedMass w K width (polyMul (polyMul a (originalBlockTransfer w K width (2*d) a)) (polyMul phi phi)) +
        -(pair w K width (originalBlockTransfer w K width d (polyMul a phi))
          (originalBlockTransfer w K width d (polyMul a phi))) := by
  have hsym := iterateStep_weighted_symmetric w K width (2*d)
    (supported_polyMul ha (supported_polyMul hphi hphi)) ha
  have hfirst := Q'.eqv_trans _ _ _ hsym
    (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => a | 1 => phi | _ => originalBlockTransfer w K width (2*d) a)))
  exact Q'.eqv_trans _ _ _ (blockNoise_variance_loss w K width d ha hphi)
    (Q'.add_eqv_congr_right _ _ _ hfirst)

/-- Quantitative ORIGINAL block-noise/cost pin for the actual reciprocal.
The remaining innovation ceiling is NOT assumed or proved by this estimate.
Both chronological masses, arbitrary signed psi, d=0 and zero norms remain. -/
theorem blockConditionalRatio_noiseCost_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t d : Nat) (hdepth : 1 ≤ n+t)
    (honset : blockConditionalDriftDepthCutoff hw0 hw1 width (⟨1, 3⟩ : Q') ≤ n+t-1)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+t)
    let A := terminalMessage w K width (n+t+d)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    let Z := pair w K width a a
    let W := pair w K width A A
    Q'.abs (W*pair w K width b b +
      -(Z*pair w K width (originalBlockTransfer w K width d b) (originalBlockTransfer w K width d b)) +
      -(Z*weightedMass w K width (blockNoise w K width d a phi))) ≤
      (comparisonEta hw0 hw1 width (n+t-1) + 2*(mixRate hw0 hw1 width)^k) * W * pair w K width b b := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let A := terminalMessage w K width (n+t+d)
  let F := terminalMessage w K width (n+t+2*d)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let p := polyMul a phi
  let e := polyAdd b (polySmul (-1) p)
  let s := polyAdd b p
  let Z := pair w K width a a
  let W := pair w K width A A
  let J := pair w K width a F
  let B := pair w K width b b
  let D := pair w K width (originalBlockTransfer w K width d b) (originalBlockTransfer w K width d b)
  let P := pair w K width p p
  let Q := pair w K width (originalBlockTransfer w K width d p) (originalBlockTransfer w K width d p)
  let M := weightedMass w K width (polyMul (polyMul a F) (polyMul phi phi))
  let eta := comparisonEta hw0 hw1 width (n+t-1)
  let delta := (mixRate hw0 hw1 width)^k
  let correction := W*pair w K width e s +
    -(Z*pair w K width (originalBlockTransfer w K width d e) (originalBlockTransfer w K width d s))
  have ha := terminalMessage_supported w K width (n+t)
  have hphi := blockConditionalRatio_supported hw0 hw1 K width hK n t hp k
  have hW : (0 : Q') ≤ W := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (n+t+d) (n+t+d))
  have heta := comparisonEta_nonnegative hw0 hw1 width (n+t-1)
  have hJ : J ≈ W := by
    simpa only [terminal_block] using block_pair w K width d ha ha
  have hpn : P ≤ B := Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => a | _ => phi))))
    (blockConditionalRatio_surviving_square_le hw0 hw1 K width hK n t hdepth hp k)
  have hdraw : Q'.abs (J*P + -(Z*M)) ≤ eta*J*P := by
    have h := futureBlockDrift_abs_le hw0 hw1 K width hK (n+t-1) (2*d) hphi
    dsimp only at h
    rw [show n+t-1+1 = n+t by omega] at h
    exact h
  have hdrift : Q'.abs (W*P + -(Z*M)) ≤ eta*W*B := by
    have hpin := Q'.add_eqv_congr_right _ _ (-(Z*M)) (Q'.mul_eqv_congr_right _ _ P hJ)
    have hpaid := Q'.mul_eqv_congr_right _ _ P (Q'.mul_eqv_congr_left eta _ _ hJ)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ hdraw (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpaid)
        (Q'.mul_le_mul_of_nonneg_left _ _ (eta*W) hpn (Q'.mul_nonneg _ _ heta hW))))
  have hcorrection : Q'.abs correction ≤ 2*delta*W*B :=
    blockConditionalRatio_signedPrediction_abs_le hw0 hw1 K width hK n t d hdepth honset hp k
  have hnoise : weightedMass w K width (blockNoise w K width d a phi) ≈ M + -Q := by
    simpa only [terminal_block] using noise_endpoint_pin w K width d ha hphi
  have hsign : correction ≈ W*(B + -P) + -(Z*(D + -Q)) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left W _ _ (pair_difference w K width b p))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left Z _ _ (block_difference_pair w K width d b p)))
  have hsplit : W*B + -(Z*D) + -(Z*weightedMass w K width (blockNoise w K width d a phi)) ≈
      (W*P + -(Z*M)) + correction := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left Z _ _ hnoise)))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
          (.neg (.mul (.var 1) (.add (.var 4) (.neg (.var 5))))))
        (.add (.add (.mul (.var 0) (.var 6)) (.neg (.mul (.var 1) (.var 4))))
          (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 6))))
            (.neg (.mul (.var 1) (.add (.var 3) (.neg (.var 5)))))))
        (by decide) (fun
          | 0 => W | 1 => Z | 2 => B | 3 => D | 4 => M | 5 => Q | _ => P))
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hsign)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hdrift hcorrection)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.mul (.mul (.var 0) (.var 2)) (.var 3))
            (.mul (.mul (.mul (.const 2) (.var 1)) (.var 2)) (.var 3)))
          (.mul (.mul (.add (.var 0) (.mul (.const 2) (.var 1))) (.var 2)) (.var 3))
          (by decide) (fun | 0 => eta | 1 => delta | 2 => W | _ => B)))))

#print axioms pair_difference
#print axioms block_difference_pair
#print axioms noise_endpoint_pin
#print axioms blockConditionalRatio_noiseCost_abs_le
#print axioms original_arbitrary_normalized_schur_le
#print axioms square_linear
#print axioms onset_factor_le_two
#print axioms block_pair
#print axioms original_signed_prediction_square_le
#print axioms blockConditionalRatio_signedPrediction_abs_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedPredictionPayment
