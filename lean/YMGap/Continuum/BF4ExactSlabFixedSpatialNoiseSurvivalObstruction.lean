/-
# A finite original-action obstruction to blanket noise survival

At width one the actual origin face has an inactive retained link. Subtract
its exact finite spin-one spatial coefficient, retaining the entire original
action. Its transmitted source is zero under every supported Haar test,
but its input squared Haar norm is at least one. Original spatial, terminal
and transfer floor certificates make the one-step noise strictly positive.

The multiplier is literally Vbar squared times Gout squared, with output
time n+1 and reciprocal degree ONE. Degree zero would be the zero polynomial.
Consequently no finite scalar pays this full historical noise from the
transmitted surviving square for every supported original source.

This prunes a blanket noise-to-surviving-square estimate. It does not
obstruct the combined exact score, a padded family, a completed comparison,
or the Clay target. No completed-kernel theorem is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.BF4ExactSlabWidthOneGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialNoiseSurvivalObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul cap_mul_left)
open YMGap.Continuum.QuaternionHaarDensityVariance
  (shifted shifted_supported raw_square_floor)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation
  (floor_insertion squareFloorCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry
  (spatialFaces_one far01_x0_index activeBlocks_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer
  (inactive_fundamental_transfer_pair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
  (plaquette_supported shifted_square_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
  (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (transferStep_add transferStep_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass kineticFloor kineticFloor_positive transferStepLowerCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr spatialFloorCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate
   weightedMass_product_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
  (messageFloor messageFloor_positive messageFloorCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
  (blockNoise blockNoise_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
  (blockReciprocal blockWindowUpper blockWindowUpper_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)

local notation "N" => List.length (baseLinks 1)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

private def face : Z4Plaq := ((0, 0, 0, 0), .p01)

private theorem face_mem : face ∈ spatialFaces 1 := by
  rw [spatialFaces_one]
  exact (by decide)

private theorem face_inactive : ¬ FullyActive 1 face := by
  intro ha
  have hlink := ha ((0, 1, 0, 0), .x0) (by decide)
  rw [far01_x0_index, activeBlocks_one] at hlink
  exact (by decide : ¬ (2 : Nat) ∈ [0, 1, 4]) hlink

/-- Literal original width-one origin character at its finite spatial center. -/
def originSource (w : Q') : RatPoly :=
  shifted (characterPolynomial (plaquette 1 face).scalar 1) (coeffW w 1)

theorem originSource_supported (w : Q') : SupportedQuaternionBlocks N (originSource w) :=
  shifted_supported (plaquette_supported 1 face) (coeffW w 1)

private theorem transfer_congr (w : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K 1 p) (transferStep w K 1 q) :=
  partialHaarHeads_congr N
    ((h.mul_left (spatialWeight w K 1)).mul_left (kineticWeight w K 1))

private theorem haar_smul_right (c : Q') (p q : RatPoly) :
    quaternionHaar N (polyMul p (polySmul c q)) ≈
      c*quaternionHaar N (polyMul p q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c p q))
    (quaternionHaar_polySmul N c (polyMul p q))

private theorem haar_neg : ∀ p : RatPoly,
    quaternionHaar N (polyNeg p) ≈ -quaternionHaar N p
  | [] => by change (0 : Q') ≈ -0; decide
  | term::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv term.2 (quaternionHaarMono N term.1)) (haar_neg rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Annihilation under every supported Haar test, not coefficient equality. -/
theorem origin_transmitted_pair_zero (w : Q') (K : Nat) (hK1 : 1 ≤ K) (n : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    quaternionHaar N (polyMul p (transferStep w K 1
      (polyMul (terminalMessage w K 1 n) (originSource w)))) ≈ 0 := by
  let g := terminalMessage w K 1 n
  let chi := characterPolynomial (plaquette 1 face).scalar 1
  let c := coeffW w 1
  let X := quaternionHaar N (polyMul p (transferStep w K 1 g))
  have hin : RatPolyCoeffEqv (polyMul g (originSource w))
      (polyAdd (polyMul g chi) (polySmul (-c) g)) := by
    unfold originSource shifted
    exact (RatPolyCoeffEqv.mul_add_right g (polySmul 1 chi) (polySmul (-c) polyOne)).trans
      (((RatPolyCoeffEqv.one_smul chi).mul_left g).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-c) g polyOne).trans
          ((RatPolyCoeffEqv.mul_one g).smul (-c))))
  have ht := (transfer_congr w K hin).trans
    ((transferStep_add w K 1 (polyMul g chi) (polySmul (-c) g)).trans
      ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K 1 (-c) g)))
  have hm : quaternionHaar N (polyMul p (transferStep w K 1 (polyMul g chi))) ≈ c*X :=
    inactive_fundamental_transfer_pair w K 1 n hK1 face_mem face_inactive p hp
  have he : quaternionHaar N (polyMul p (transferStep w K 1 (polyMul g (originSource w)))) ≈
      c*X + (-c)*X :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((ht.mul_left p).trans (RatPolyCoeffEqv.mul_add_right p _ _)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
        (Q'.add_eqv_congr' hm (haar_smul_right (-c) p (transferStep w K 1 g))))
  exact Q'.eqv_trans _ _ _ he
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 0)) (.var 1)))
      (.const 0) (by decide) (fun | 0 => c | _ => X))

/-- The unchanged V-weighted transmitted surviving square is exactly null. -/
theorem origin_transmitted_surviving_square_zero (w : Q') (K : Nat)
    (hK1 : 1 ≤ K) (n : Nat) :
    let b := originalBlockTransfer w K 1 1
      (polyMul (terminalMessage w K 1 n) (originSource w))
    weightedMass w K 1 (polyMul b b) ≈ 0 := by
  let b := transferStep w K 1 (polyMul (terminalMessage w K 1 n) (originSource w))
  have hb := transferStep_supported w K 1
    (supported_polyMul (terminalMessage_supported w K 1 n) (originSource_supported w))
  have hz := origin_transmitted_pair_zero w K hK1 n
    (supported_polyMul (spatialWeight_supported w K 1) hb)
  dsimp only
  unfold weightedMass
  change quaternionHaar N (polyMul (spatialWeight w K 1) (polyMul b b)) ≈ 0
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K 1) b b))) hz

private theorem original_noise_haar_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    (0 : Q') < quaternionHaar N (blockNoise w K 1 1 (terminalMessage w K 1 n) (originSource w)) := by
  let g := terminalMessage w K 1 n
  let psi := originSource w
  let input := polyMul g (polyMul psi psi)
  let A := transferStep w K 1 g
  let U := transferStep w K 1 input
  let b := transferStep w K 1 (polyMul g psi)
  let delta := (headFloor w)^(spatialFaces 1).length
  have hdelta : (0 : Q') < delta := HKPos.pow_pos (headFloor_positive hw0 hw1) _
  have hpsi := originSource_supported w
  have hg := terminalMessage_supported w K 1 n
  have PG := terminalMessage_certificate hw0 hw1 K 1 hK n
  have PP := Certificate.square psi hpsi
  have hbare : (1 : Q') ≤ quaternionHaar N (polyMul psi psi) :=
    shifted_square_floor 1 face face_mem (coeffW w 1)
  have hspatial : delta ≤ weightedMass w K 1 (polyMul psi psi) := by
    unfold weightedMass
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv delta))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ delta hbare (Q'.le_of_lt hdelta))
        (raw_square_floor (spatialFloorCertificate hw0 hw1 K 1 hK) hpsi))
  have hinputmass : (0 : Q') < weightedMass w K 1 input := by
    have hfloor := weightedMass_product_floor hw0 hw1 K 1 hK PP
      (messageFloorCertificate hw0 hw1 K 1 hK n)
    have hpin := weightedMass_congr w K 1 (RatPolyCoeffEqv.mul_comm (polyMul psi psi) g)
    exact HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_pos (messageFloor_positive hw0 hw1 K 1 hK n)
        (HeatKernelRGStep.lt_of_lt_of_le hdelta hspatial))
      (Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hpin))
  have hinput := supported_polyMul hg (supported_polyMul hpsi hpsi)
  have PI := PG.mul PP
  have PU := transferStep_certificate hw0 hw1 K 1 hK hinput PI
  have hUfloor := transferStepLowerCertificate hw0 hw1 K 1 hK hinput PI
  have hUhaar : (0 : Q') < quaternionHaar N U := by
    have hfloor := floor_insertion (Certificate.one N) hUfloor
    have hleft : (kineticFloor w 1 * weightedMass w K 1 input)*quaternionHaar N polyOne ≈
        kineticFloor w 1 * weightedMass w K 1 input :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (QPolyHaarPositiveSubstitution.haar_one N))
        (Q'.mul_one_eqv _)
    have hright := haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul U)
    exact HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_pos (kineticFloor_positive hw0 hw1 1) hinputmass)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hright)))
  have LA : Certificate N (polyAdd A (polyNeg (cap (messageFloor w K 1 (n+1))))) := by
    dsimp only [A, g]
    rw [terminalMessage_next]
    exact messageFloorCertificate hw0 hw1 K 1 hK (n+1)
  have hAU : (0 : Q') < quaternionHaar N (polyMul A U) :=
    HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_pos (messageFloor_positive hw0 hw1 K 1 hK (n+1)) hUhaar)
      (Q'.le_trans' _ _ _ (floor_insertion PU LA)
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm U A))))
  have hb := transferStep_supported w K 1 (supported_polyMul hg hpsi)
  have hz : quaternionHaar N (polyMul b b) ≈ 0 :=
    origin_transmitted_pair_zero w K hK1 n hb
  have hpin : quaternionHaar N (blockNoise w K 1 1 g psi) ≈ quaternionHaar N (polyMul A U) := by
    change quaternionHaar N (polyAdd (polyMul A U) (polyNeg (polyMul b b))) ≈ _
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_neg (polyMul b b))
            (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hz) (by decide : -(0 : Q') ≈ 0))))
        (QPoly.q_add_zero_eqv _))
  exact HeatKernelRGStep.lt_of_lt_of_le hAU (Q'.ge_of_eqv hpin)

/-- Strict positivity with the literal output multiplier, at reciprocal degree
one and original terminal time n+1. All finite input depths are retained. -/
theorem origin_weighted_noise_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let Vbar := spatialFringeMass w K 1
    let Gout := blockReciprocal hw0 hw1 K 1 hK n 1 1
    let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
    (0 : Q') < quaternionHaar N (polyMul Lambda
      (blockNoise w K 1 1 (terminalMessage w K 1 n) (originSource w))) := by
  dsimp only
  let Vbar := spatialFringeMass w K 1
  let Gout := blockReciprocal hw0 hw1 K 1 hK n 1 1
  let D := blockNoise w K 1 1 (terminalMessage w K 1 n) (originSource w)
  let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
  let delta := BF4ExactSlabFixedSpatialFringeProjectionWindow.lower w K 1
  let alpha := QuaternionHaarPositiveWindowInverse.scale (blockWindowUpper w K 1 n 1)
    (blockWindowUpper_positive hw0 hw1 K 1 hK n 1)
  have halpha : (0 : Q') < alpha := QuaternionHaarPositiveWindowInverse.scale_positive _ _
  have hdelta : (0 : Q') < delta :=
    BF4ExactSlabFixedSpatialFringeProjectionWindow.lower_positive hw0 hw1 K 1
  have hG : RatPolyCoeffEqv Gout (cap alpha) := by
    change RatPolyCoeffEqv
      (polySmul alpha (polyAdd polyOne (polyMul
        (polyNeg (QuaternionHaarPositiveWindowInverse.remainder
          (terminalMessage w K 1 (n+1)) (blockWindowUpper w K 1 n 1)
          (blockWindowUpper_positive hw0 hw1 K 1 hK n 1))) polyZero))) (cap alpha)
    exact (((RatPolyCoeffEqv.refl polyOne).add (RatPolyCoeffEqv.mul_zero_right _)).trans
      (RatPolyCoeffEqv.add_zero polyOne)).smul alpha
  have PN := blockNoise_certificate hw0 hw1 K 1 hK 1
    (terminalMessage_supported w K 1 n) (originSource_supported w)
    (terminalMessage_certificate hw0 hw1 K 1 hK n)
  have hfloor := floor_insertion PN
    (squareFloorCertificate (Q'.le_of_lt hdelta)
      (BF4ExactSlabFixedSpatialFringeProjectionWindow.lowerCertificate hw0 hw1 K 1 hK))
  have hvv : (0 : Q') < quaternionHaar N (polyMul (polyMul Vbar Vbar) D) :=
    HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_pos (Q'.mul_pos hdelta hdelta)
        (original_noise_haar_positive hw0 hw1 K hK hK1 n))
      (Q'.le_trans' _ _ _ hfloor
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm D (polyMul Vbar Vbar)))))
  have hGG := (hG.mul hG).trans (cap_mul alpha alpha)
  have hid : RatPolyCoeffEqv (polyMul Lambda D)
      (polySmul (alpha*alpha) (polyMul (polyMul Vbar Vbar) D)) :=
    (((RatPolyCoeffEqv.refl (polyMul Vbar Vbar)).mul hGG).mul_right D).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => polyMul Vbar Vbar | 1 => cap (alpha*alpha) | _ => D)).trans
        (cap_mul_left (alpha*alpha) (polyMul (polyMul Vbar Vbar) D)))
  have hpin := Q'.eqv_trans _ _ _ (haar_of_coeff hid)
    (quaternionHaar_polySmul N (alpha*alpha) (polyMul (polyMul Vbar Vbar) D))
  exact HeatKernelRGStep.lt_of_lt_of_le (Q'.mul_pos (Q'.mul_pos halpha halpha) hvv)
    (Q'.ge_of_eqv hpin)

/-- No arbitrary finite scalar can bound this literal full noise by the
transmitted surviving square. In particular n=1 meets the innovation depth
guard; no claim about the primary combined exact score follows. -/
theorem origin_no_noise_survival_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (C : Q') :
    let b := originalBlockTransfer w K 1 1
      (polyMul (terminalMessage w K 1 n) (originSource w))
    let Vbar := spatialFringeMass w K 1
    let Gout := blockReciprocal hw0 hw1 K 1 hK n 1 1
    let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
    ¬ quaternionHaar N (polyMul Lambda
        (blockNoise w K 1 1 (terminalMessage w K 1 n) (originSource w))) ≤
      C*weightedMass w K 1 (polyMul b b) := by
  dsimp only
  intro hbound
  have hz := origin_transmitted_surviving_square_zero w K hK1 n
  have hright := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left C _ _ hz) (Q'.mul_zero_eqv C)
  have hle := Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright)
  exact (by decide : ¬ (0 : Q') < 0)
    (Q'.pos_of_lt_of_le (origin_weighted_noise_positive hw0 hw1 K hK hK1 n) hle)

#print axioms originSource
#print axioms originSource_supported
#print axioms origin_transmitted_pair_zero
#print axioms origin_transmitted_surviving_square_zero
#print axioms origin_weighted_noise_positive
#print axioms origin_no_noise_survival_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialNoiseSurvivalObstruction
