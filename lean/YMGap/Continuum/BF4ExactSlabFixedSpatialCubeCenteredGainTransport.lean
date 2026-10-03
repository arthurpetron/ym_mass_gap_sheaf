/-
# Original centered cube gain and quadratic cost

The literal original messages U=T1 and b=TF-cU are retained. Each weighted
source is first tested against the full original action, then its reduced
representative pays fringe peeling, and finally the original messages are
restored under the cube action by supported tests. No raw original-message
locality or centered eigenpin is assumed. Young's actual square gives the
signed lower bound C2-a²Q <= 2G. This is finite source algebra, not a gain
sign, OWN-mean bound, reserve or scaling result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
import YMGap.Continuum.QuaternionHaarRelativePredictionFloor
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (commutatorGain centeredMessage centeredMessage_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight (spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection (centeredBentMessage)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_scale)
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep cubeWeight cubeTransfer bentObservable weightedMass
  terminalMessage kineticWeight spatialWeight centeredMessage

private def psi (c : Q') : RatPoly := polyAdd bentObservable (polySmul (-c) polyOne)

/-- The literal ORIGINAL endpoint U*(F-c), before normalization. -/
def centeredOriginalEndpoint (w c : Q') : RatPoly :=
  polyMul (transferStep w 1 2 polyOne) (psi c)

/-- Literal original gain, with arbitrary reference coefficient a. -/
def centeredOriginalGain (w c a : Q') : Q' :=
  let b := centeredBentMessage w c
  weightedMass w 1 2 (polyMul b (polyAdd b (polySmul (-a) (centeredOriginalEndpoint w c))))

def centeredOriginalSquare (w c : Q') : Q' :=
  weightedMass w 1 2 (polyMul (centeredBentMessage w c) (centeredBentMessage w c))

def centeredOriginalYoungCost (w c : Q') : Q' :=
  weightedMass w 1 2 (polyMul (centeredOriginalEndpoint w c) (centeredOriginalEndpoint w c))

/-- Exact source identification with the existing depth-zero original signed
commutator gain. The reference a and the center c remain arbitrary. -/
theorem original_commutator_gain_pin (w c a : Q') :
    commutatorGain w 1 2 0 bentObservable c a ≈ centeredOriginalGain w c a := by
  have hzero : terminalMessage w 1 2 0 = polyOne := by
    unfold terminalMessage
    rfl
  have ht : RatPolyCoeffEqv (transferStep w 1 2 (polyMul polyOne bentObservable))
      (transferStep w 1 2 bentObservable) := by
    unfold transferStep
    exact partialHaarHeads_congr N
      ((RatPolyCoeffEqv.refl (kineticWeight w 1 2)).mul
        ((RatPolyCoeffEqv.refl (spatialWeight w 1 2)).mul
          (RatPolyCoeffEqv.one_mul bentObservable)))
  have hb := centeredMessage_pin w 1 2 0 bentObservable c
  rw [hzero] at hb
  have hmessage : RatPolyCoeffEqv (centeredMessage w 1 2 0 bentObservable c)
      (centeredBentMessage w c) :=
    hb.trans (ht.add (RatPolyCoeffEqv.refl _))
  have hpsi : RatPolyCoeffEqv (shifted bentObservable c) (psi c) :=
    (RatPolyCoeffEqv.one_smul bentObservable).add (RatPolyCoeffEqv.refl _)
  have hu : RatPolyCoeffEqv
      (polyMul (transferStep w 1 2 (terminalMessage w 1 2 0)) (shifted bentObservable c))
      (centeredOriginalEndpoint w c) := by
    rw [hzero]
    exact (RatPolyCoeffEqv.refl _).mul hpsi
  have hg := hmessage.mul (hmessage.add (hu.smul (-a)))
  exact weightedMass_congr w 1 2 hg

private def reducedMessage (w c : Q') : RatPoly :=
  polyAdd (cubeTransfer w 1 bentObservable) (polySmul (-c) (cubeTransfer w 1 polyOne))

private def reducedEndpoint (w c : Q') : RatPoly :=
  polyMul (cubeTransfer w 1 polyOne) (psi c)

private theorem psi_supported (c : Q') : SupportedQuaternionBlocks N (psi c) :=
  supported_add bentObservable_supported (polySmul_supported (supported_one N) (-c))

private theorem message_supported (w c : Q') : SupportedQuaternionBlocks N (centeredBentMessage w c) :=
  supported_add (transferStep_supported w 1 2 bentObservable_supported)
    (polySmul_supported (transferStep_supported w 1 2 (supported_one N)) (-c))

private theorem endpoint_supported (w c : Q') : SupportedQuaternionBlocks N (centeredOriginalEndpoint w c) :=
  supported_polyMul (transferStep_supported w 1 2 (supported_one N)) (psi_supported c)

private theorem reducedMessage_supported (w c : Q') : SupportedQuaternionBlocks N (reducedMessage w c) :=
  supported_add (cubeTransfer_supported w 1 bentObservable_supported)
    (polySmul_supported (cubeTransfer_supported w 1 (supported_one N)) (-c))

private theorem reducedEndpoint_supported (w c : Q') : SupportedQuaternionBlocks N (reducedEndpoint w c) :=
  supported_polyMul (cubeTransfer_supported w 1 (supported_one N)) (psi_supported c)

private theorem message_pin (w c : Q') :
    SupportedHaarEqv N (centeredBentMessage w c) (reducedMessage w c) :=
  (original_bent_message_cube w 1).add ((original_vacuum_message_cube w 1).smul (-c))

private theorem endpoint_pin (w c : Q') :
    SupportedHaarEqv N (centeredOriginalEndpoint w c) (reducedEndpoint w c) :=
  (original_vacuum_message_cube w 1).mul (SupportedHaarEqv.refl N (psi c))
    (psi_supported c) (cubeTransfer_supported w 1 (supported_one N))

private theorem reducedMessage_independent (w c : Q') (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (reducedMessage w c) :=
  quaternionBlockIndependent_polyAdd (cubeTransfer_independent w 1 i hi hn bentObservable_supported)
    (quaternionBlockIndependent_polySmul (-c) (cubeTransfer_independent w 1 i hi hn (supported_one N)))

private theorem reducedEndpoint_independent (w c : Q') (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (reducedEndpoint w c) :=
  quaternionBlockIndependent_polyMul (cubeTransfer_independent w 1 i hi hn (supported_one N))
    (quaternionBlockIndependent_polyAdd (bentObservable_cube_independent i hi hn)
      (quaternionBlockIndependent_polySmul (-c) (quaternionBlockIndependent_polyOne i)))

private theorem weight_supported (w : Q') : SupportedQuaternionBlocks N (cubeWeight w 1) := by
  unfold cubeWeight
  exact heatProduct_supported w 1 2 cubeFaces

private theorem paid_weight_pin (w : Q') {p r : RatPoly}
    (h : SupportedHaarEqv N p r) (hr : SupportedQuaternionBlocks N r)
    (hi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i r) :
    weightedMass w 1 2 p ≈ quaternionHaar N (polyMul (cubeWeight w 1) p) := by
  unfold weightedMass
  have h0 := h (spatialWeight w 1 2) (spatialWeight_supported w 1 2)
  have h1 := spatialWeight_haar_active w 1 2 r hr (fun i hf =>
    hi i (fringeBlocks_lt 2 i hf)
      (fun hc => ((fringeBlocks_mem_iff 2 i).mp hf).2 (cubeIndices_active i hc)))
  have h2 := haar_of_coeff (blocks := N) ((activeSpatialWeight_cube w 1).mul_right r)
  have h3 := h (cubeWeight w 1) (weight_supported w)
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_symm h3)))

theorem centeredSquare_cube_pin (w c : Q') :
    centeredOriginalSquare w c ≈ quaternionHaar N (polyMul (cubeWeight w 1)
      (polyMul (centeredBentMessage w c) (centeredBentMessage w c))) :=
  paid_weight_pin w ((message_pin w c).mul (message_pin w c)
    (message_supported w c) (reducedMessage_supported w c))
    (supported_polyMul (reducedMessage_supported w c) (reducedMessage_supported w c))
    (fun i hi hn => quaternionBlockIndependent_polyMul
      (reducedMessage_independent w c i hi hn) (reducedMessage_independent w c i hi hn))

theorem youngCost_cube_pin (w c : Q') :
    centeredOriginalYoungCost w c ≈ quaternionHaar N (polyMul (cubeWeight w 1)
      (polyMul (centeredOriginalEndpoint w c) (centeredOriginalEndpoint w c))) :=
  paid_weight_pin w ((endpoint_pin w c).mul (endpoint_pin w c)
    (endpoint_supported w c) (reducedEndpoint_supported w c))
    (supported_polyMul (reducedEndpoint_supported w c) (reducedEndpoint_supported w c))
    (fun i hi hn => quaternionBlockIndependent_polyMul
      (reducedEndpoint_independent w c i hi hn) (reducedEndpoint_independent w c i hi hn))

theorem gain_cube_pin (w c a : Q') :
    centeredOriginalGain w c a ≈ quaternionHaar N (polyMul (cubeWeight w 1)
      (polyMul (centeredBentMessage w c)
        (polyAdd (centeredBentMessage w c) (polySmul (-a) (centeredOriginalEndpoint w c))))) := by
  have htail := (message_pin w c).add ((endpoint_pin w c).smul (-a))
  exact paid_weight_pin w ((message_pin w c).mul htail
    (supported_add (message_supported w c) (polySmul_supported (endpoint_supported w c) (-a)))
    (reducedMessage_supported w c))
    (supported_polyMul (reducedMessage_supported w c)
      (supported_add (reducedMessage_supported w c) (polySmul_supported (reducedEndpoint_supported w c) (-a))))
    (fun i hi hn => quaternionBlockIndependent_polyMul (reducedMessage_independent w c i hi hn)
      (quaternionBlockIndependent_polyAdd (reducedMessage_independent w c i hi hn)
        (quaternionBlockIndependent_polySmul (-a) (reducedEndpoint_independent w c i hi hn))))

private theorem young_collect (s q j g a : Q') (h : 2*a*j ≤ (a*a)*q+s)
    (hg : g ≈ s+(-a)*j) : s-(a*a)*q ≤ 2*g := by
  have he : ((a*a)*q+s)-(2*a*j) ≈ 2*(s+(-a)*j)-(s-(a*a)*q) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 4) (.var 4)) (.var 1)) (.var 0))
        (.neg (.mul (.mul (.const 2) (.var 4)) (.var 2))))
      (.add (.mul (.const 2) (.add (.var 0) (.mul (.neg (.var 4)) (.var 2))))
        (.neg (.add (.var 0) (.neg (.mul (.mul (.var 4) (.var 4)) (.var 1))))))
      (by decide) (fun | 0 => s | 1 => q | 2 => j | _ => a)
  have ht := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hg)) (Q'.eqv_refl (-(s-(a*a)*q)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le h)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he ht)))

/-- The actual Young square pays the whole signed cross. No sign or range
of a or c is required, and no all-nome head guard is used. -/
theorem gain_young_lower (w c a : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hdelta : cubeFundamentalDelta w ≤ 1) :
    centeredOriginalSquare w c - (a*a)*centeredOriginalYoungCost w c ≤
      2*centeredOriginalGain w c a := by
  let V := cubeWeight w 1
  let b := centeredBentMessage w c
  let u := centeredOriginalEndpoint w c
  let s := quaternionHaar N (polyMul V (polyMul b b))
  let q := quaternionHaar N (polyMul V (polyMul u u))
  let j := quaternionHaar N (polyMul V (polyMul u b))
  have hy : 2*a*j ≤ (a*a)*q+s :=
    weighted_square_young (cubeFundamentalCertificate w ha hdelta)
      (endpoint_supported w c) (message_supported w c) a
  have hp : RatPolyCoeffEqv (polyMul b (polyAdd b (polySmul (-a) u)))
      (polyAdd (polyMul b b) (polySmul (-a) (polyMul u b))) :=
    (RatPolyCoeffEqv.mul_add_right b b _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-a) b u).trans
          ((RatPolyCoeffEqv.mul_comm b u).smul (-a))))
  have hg : centeredOriginalGain w c a ≈ s+(-a)*j :=
    Q'.eqv_trans _ _ _ (gain_cube_pin w c a)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (hp.mul_left V))
        (Q'.eqv_trans _ _ _ (haar_weighted_add N V _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl s) (weighted_scale N V (polyMul u b) (-a)))))
  have hc := young_collect s q j (centeredOriginalGain w c a) a hy hg
  have hs := centeredSquare_cube_pin w c
  have hq := youngCost_cube_pin w c
  have he := Q'.add_eqv_congr' hs
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (a*a) _ _ hq))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hc

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.centeredOriginalEndpoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.centeredOriginalGain
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.centeredOriginalSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.centeredOriginalYoungCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.original_commutator_gain_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.centeredSquare_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.youngCost_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.gain_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport.gain_young_lower
