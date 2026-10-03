/-
# Original cube gain transport at arbitrary cutoff

The original messages U=T1 and b=TF-cU retain the full action at every K.
Supported tested transport pays fringe peeling before restoring these same
messages under the actual six-face cube weight. Young's square gives the
signed bound C2-a²Q <= 2G whenever that actual weight has a Certificate.
The center and reference coefficient remain arbitrary. No centered eigenpin,
head guard, gain sign, reserve, or scaling conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport

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

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep cubeWeight cubeTransfer bentObservable weightedMass
  terminalMessage kineticWeight spatialWeight centeredMessage

private def psi (c : Q') : RatPoly := polyAdd bentObservable (polySmul (-c) polyOne)

/-- The literal original signed message TF-cT1 at cutoff K. -/
def centeredBentMessage (w : Q') (K : Nat) (c : Q') : RatPoly :=
  polyAdd (transferStep w K 2 bentObservable)
    (polySmul (-c) (transferStep w K 2 polyOne))

/-- The literal original endpoint U*(F-c), before normalization. -/
def centeredOriginalEndpoint (w : Q') (K : Nat) (c : Q') : RatPoly :=
  polyMul (transferStep w K 2 polyOne) (psi c)

/-- Literal original gain with arbitrary reference coefficient a. -/
def centeredOriginalGain (w : Q') (K : Nat) (c a : Q') : Q' :=
  let b := centeredBentMessage w K c
  weightedMass w K 2 (polyMul b
    (polyAdd b (polySmul (-a) (centeredOriginalEndpoint w K c))))

def centeredOriginalSquare (w : Q') (K : Nat) (c : Q') : Q' :=
  weightedMass w K 2 (polyMul (centeredBentMessage w K c) (centeredBentMessage w K c))

def centeredOriginalYoungCost (w : Q') (K : Nat) (c : Q') : Q' :=
  weightedMass w K 2 (polyMul (centeredOriginalEndpoint w K c) (centeredOriginalEndpoint w K c))

/-- Exact identification with the existing original depth-zero commutator gain. -/
theorem original_commutator_gain_pin (w : Q') (K : Nat) (c a : Q') :
    commutatorGain w K 2 0 bentObservable c a ≈ centeredOriginalGain w K c a := by
  have hzero : terminalMessage w K 2 0 = polyOne := by
    unfold terminalMessage
    rfl
  have ht : RatPolyCoeffEqv (transferStep w K 2 (polyMul polyOne bentObservable))
      (transferStep w K 2 bentObservable) := by
    unfold transferStep
    exact partialHaarHeads_congr N
      ((RatPolyCoeffEqv.refl (kineticWeight w K 2)).mul
        ((RatPolyCoeffEqv.refl (spatialWeight w K 2)).mul
          (RatPolyCoeffEqv.one_mul bentObservable)))
  have hb := centeredMessage_pin w K 2 0 bentObservable c
  rw [hzero] at hb
  have hmessage : RatPolyCoeffEqv (centeredMessage w K 2 0 bentObservable c)
      (centeredBentMessage w K c) :=
    hb.trans (ht.add (RatPolyCoeffEqv.refl _))
  have hpsi : RatPolyCoeffEqv (shifted bentObservable c) (psi c) :=
    (RatPolyCoeffEqv.one_smul bentObservable).add (RatPolyCoeffEqv.refl _)
  have hu : RatPolyCoeffEqv
      (polyMul (transferStep w K 2 (terminalMessage w K 2 0)) (shifted bentObservable c))
      (centeredOriginalEndpoint w K c) := by
    rw [hzero]
    exact (RatPolyCoeffEqv.refl _).mul hpsi
  have hg := hmessage.mul (hmessage.add (hu.smul (-a)))
  exact weightedMass_congr w K 2 hg

private def reducedMessage (w : Q') (K : Nat) (c : Q') : RatPoly :=
  polyAdd (cubeTransfer w K bentObservable) (polySmul (-c) (cubeTransfer w K polyOne))

private def reducedEndpoint (w : Q') (K : Nat) (c : Q') : RatPoly :=
  polyMul (cubeTransfer w K polyOne) (psi c)

private theorem psi_supported (c : Q') : SupportedQuaternionBlocks N (psi c) :=
  supported_add bentObservable_supported (polySmul_supported (supported_one N) (-c))

private theorem message_supported (w : Q') (K : Nat) (c : Q') :
    SupportedQuaternionBlocks N (centeredBentMessage w K c) :=
  supported_add (transferStep_supported w K 2 bentObservable_supported)
    (polySmul_supported (transferStep_supported w K 2 (supported_one N)) (-c))

private theorem endpoint_supported (w : Q') (K : Nat) (c : Q') :
    SupportedQuaternionBlocks N (centeredOriginalEndpoint w K c) :=
  supported_polyMul (transferStep_supported w K 2 (supported_one N)) (psi_supported c)

private theorem reducedMessage_supported (w : Q') (K : Nat) (c : Q') :
    SupportedQuaternionBlocks N (reducedMessage w K c) :=
  supported_add (cubeTransfer_supported w K bentObservable_supported)
    (polySmul_supported (cubeTransfer_supported w K (supported_one N)) (-c))

private theorem reducedEndpoint_supported (w : Q') (K : Nat) (c : Q') :
    SupportedQuaternionBlocks N (reducedEndpoint w K c) :=
  supported_polyMul (cubeTransfer_supported w K (supported_one N)) (psi_supported c)

private theorem message_pin (w : Q') (K : Nat) (c : Q') :
    SupportedHaarEqv N (centeredBentMessage w K c) (reducedMessage w K c) :=
  (original_bent_message_cube w K).add ((original_vacuum_message_cube w K).smul (-c))

private theorem endpoint_pin (w : Q') (K : Nat) (c : Q') :
    SupportedHaarEqv N (centeredOriginalEndpoint w K c) (reducedEndpoint w K c) :=
  (original_vacuum_message_cube w K).mul (SupportedHaarEqv.refl N (psi c))
    (psi_supported c) (cubeTransfer_supported w K (supported_one N))

private theorem reducedMessage_independent (w : Q') (K : Nat) (c : Q')
    (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (reducedMessage w K c) :=
  quaternionBlockIndependent_polyAdd (cubeTransfer_independent w K i hi hn bentObservable_supported)
    (quaternionBlockIndependent_polySmul (-c) (cubeTransfer_independent w K i hi hn (supported_one N)))

private theorem reducedEndpoint_independent (w : Q') (K : Nat) (c : Q')
    (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (reducedEndpoint w K c) :=
  quaternionBlockIndependent_polyMul (cubeTransfer_independent w K i hi hn (supported_one N))
    (quaternionBlockIndependent_polyAdd (bentObservable_cube_independent i hi hn)
      (quaternionBlockIndependent_polySmul (-c) (quaternionBlockIndependent_polyOne i)))

private theorem weight_supported (w : Q') (K : Nat) : SupportedQuaternionBlocks N (cubeWeight w K) := by
  unfold cubeWeight
  exact heatProduct_supported w K 2 cubeFaces

private theorem paid_weight_pin (w : Q') (K : Nat) {p r : RatPoly}
    (h : SupportedHaarEqv N p r) (hr : SupportedQuaternionBlocks N r)
    (hi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i r) :
    weightedMass w K 2 p ≈ quaternionHaar N (polyMul (cubeWeight w K) p) := by
  unfold weightedMass
  have h0 := h (spatialWeight w K 2) (spatialWeight_supported w K 2)
  have h1 := spatialWeight_haar_active w K 2 r hr (fun i hf =>
    hi i (fringeBlocks_lt 2 i hf)
      (fun hc => ((fringeBlocks_mem_iff 2 i).mp hf).2 (cubeIndices_active i hc)))
  have h2 := haar_of_coeff (blocks := N) ((activeSpatialWeight_cube w K).mul_right r)
  have h3 := h (cubeWeight w K) (weight_supported w K)
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_symm h3)))

theorem centeredSquare_cube_pin (w : Q') (K : Nat) (c : Q') :
    centeredOriginalSquare w K c ≈ quaternionHaar N (polyMul (cubeWeight w K)
      (polyMul (centeredBentMessage w K c) (centeredBentMessage w K c))) :=
  paid_weight_pin w K ((message_pin w K c).mul (message_pin w K c)
    (message_supported w K c) (reducedMessage_supported w K c))
    (supported_polyMul (reducedMessage_supported w K c) (reducedMessage_supported w K c))
    (fun i hi hn => quaternionBlockIndependent_polyMul
      (reducedMessage_independent w K c i hi hn) (reducedMessage_independent w K c i hi hn))

theorem youngCost_cube_pin (w : Q') (K : Nat) (c : Q') :
    centeredOriginalYoungCost w K c ≈ quaternionHaar N (polyMul (cubeWeight w K)
      (polyMul (centeredOriginalEndpoint w K c) (centeredOriginalEndpoint w K c))) :=
  paid_weight_pin w K ((endpoint_pin w K c).mul (endpoint_pin w K c)
    (endpoint_supported w K c) (reducedEndpoint_supported w K c))
    (supported_polyMul (reducedEndpoint_supported w K c) (reducedEndpoint_supported w K c))
    (fun i hi hn => quaternionBlockIndependent_polyMul
      (reducedEndpoint_independent w K c i hi hn) (reducedEndpoint_independent w K c i hi hn))

theorem gain_cube_pin (w : Q') (K : Nat) (c a : Q') :
    centeredOriginalGain w K c a ≈ quaternionHaar N (polyMul (cubeWeight w K)
      (polyMul (centeredBentMessage w K c)
        (polyAdd (centeredBentMessage w K c) (polySmul (-a) (centeredOriginalEndpoint w K c))))) := by
  have htail := (message_pin w K c).add ((endpoint_pin w K c).smul (-a))
  exact paid_weight_pin w K ((message_pin w K c).mul htail
    (supported_add (message_supported w K c) (polySmul_supported (endpoint_supported w K c) (-a)))
    (reducedMessage_supported w K c))
    (supported_polyMul (reducedMessage_supported w K c)
      (supported_add (reducedMessage_supported w K c)
        (polySmul_supported (reducedEndpoint_supported w K c) (-a))))
    (fun i hi hn => quaternionBlockIndependent_polyMul (reducedMessage_independent w K c i hi hn)
      (quaternionBlockIndependent_polyAdd (reducedMessage_independent w K c i hi hn)
        (quaternionBlockIndependent_polySmul (-a) (reducedEndpoint_independent w K c i hi hn))))

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

/-- An actual cube-weight Certificate pays Young's signed square at any cutoff.
No sign or range of the center or reference coefficient is required. -/
theorem gain_young_lower (w : Q') (K : Nat) (c a : Q')
    (P : Certificate N (cubeWeight w K)) :
    centeredOriginalSquare w K c - (a*a)*centeredOriginalYoungCost w K c ≤
      2*centeredOriginalGain w K c a := by
  let V := cubeWeight w K
  let b := centeredBentMessage w K c
  let u := centeredOriginalEndpoint w K c
  let s := quaternionHaar N (polyMul V (polyMul b b))
  let q := quaternionHaar N (polyMul V (polyMul u u))
  let j := quaternionHaar N (polyMul V (polyMul u b))
  have hy : 2*a*j ≤ (a*a)*q+s :=
    weighted_square_young P (endpoint_supported w K c) (message_supported w K c) a
  have hp : RatPolyCoeffEqv (polyMul b (polyAdd b (polySmul (-a) u)))
      (polyAdd (polyMul b b) (polySmul (-a) (polyMul u b))) :=
    (RatPolyCoeffEqv.mul_add_right b b _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-a) b u).trans
          ((RatPolyCoeffEqv.mul_comm b u).smul (-a))))
  have hg : centeredOriginalGain w K c a ≈ s+(-a)*j :=
    Q'.eqv_trans _ _ _ (gain_cube_pin w K c a)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (hp.mul_left V))
        (Q'.eqv_trans _ _ _ (haar_weighted_add N V _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl s) (weighted_scale N V (polyMul u b) (-a)))))
  have hc := young_collect s q j (centeredOriginalGain w K c a) a hy hg
  have hs := centeredSquare_cube_pin w K c
  have hq := youngCost_cube_pin w K c
  have he := Q'.add_eqv_congr' hs
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (a*a) _ _ hq))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hc

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredBentMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredOriginalEndpoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredOriginalGain
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredOriginalSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredOriginalYoungCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.original_commutator_gain_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.centeredSquare_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.youngCost_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.gain_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.gain_young_lower
