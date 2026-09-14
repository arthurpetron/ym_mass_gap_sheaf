/-
# Composition of boundary-retaining fundamental tubes

The one-layer identity accepts an arbitrary retained polynomial. Insert
another layer into that slot and induct: the exact selected-channel
transmission is the product of w_i^12, for an arbitrary finite list of
nomes. At constant nome the exponent is 12 times the tube length.

This is a theorem about the displayed signed Haar polynomials, not about
the full interacting transfer operator. Spatial heat weights, other spin
channels, centering and volume limits are not silently restored. In
particular a positive selected tube is not yet a positive original response.
-/

import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

namespace YMGap.Continuum.SU2QuaternionFundamentalTubeComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

local infix:50 " ≈ " => Q'.eqv
local notation "P" => plaquette 0 1 2 3

/-- A new layer uses four new lower variables and the SAME four upper
variables used by the next layer, whose entire polynomial is shifted. -/
def addLayer (w : Q') (boundary : RatPoly) : RatPoly :=
  polySmul (fourHeatCoefficients w) (factorProduct
    [sideCharacter 0 4, sideCharacter 1 5, sideCharacter 2 6,
      sideCharacter 3 7, liftBoundary 4 boundary])

def tubeChain : List Q' → RatPoly → RatPoly
  | [], boundary => boundary
  | w :: ws, boundary => addLayer w (tubeChain ws boundary)

/-- Explicit coupling dependence, allowing a different nome in every layer. -/
def transmission : List Q' → Q'
  | [] => 1
  | w :: ws => qpow w 12 * transmission ws

theorem addLayer_haar (w : Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks+4) (polyMul P (addLayer w boundary)) ≈
      qpow w 12 * quaternionHaar blocks (polyMul P boundary) := by
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _))
    (weighted_tube_boundary_haar w blocks boundary)

/-- All-length conditional propagation with arbitrary retained spectators.
No intermediate layer is replaced by an independent copy of its boundary. -/
theorem tubeChain_haar (ws : List Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 4*ws.length) (polyMul P (tubeChain ws boundary)) ≈
      transmission ws * quaternionHaar blocks (polyMul P boundary) := by
  induction ws with
  | nil => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | cons w ws ih =>
      have hn : blocks + 4*(w::ws).length = (blocks + 4*ws.length) + 4 := by simp; omega
      rw [hn]
      exact Q'.eqv_trans _ _ _ (addLayer_haar w (blocks + 4*ws.length) (tubeChain ws boundary))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

theorem transmission_constant (w : Q') (n : Nat) :
    transmission (List.replicate n w) ≈ qpow w (12*n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih) ?_
      have he : 12*(n+1) = 12 + 12*n := by omega
      rw [he]
      exact Q'.eqv_symm (RingNormaliser.qpow_add w 12 (12*n))

theorem homogeneous_tube_haar (w : Q') (n blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 4*n) (polyMul P (tubeChain (List.replicate n w) boundary)) ≈
      qpow w (12*n) * quaternionHaar blocks (polyMul P boundary) := by
  have h := tubeChain_haar (List.replicate n w) blocks boundary
  rw [List.length_replicate] at h
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _ (transmission_constant w n))

/-- The selected twelve-side-face contribution at the required three-step separation. -/
theorem threeLayer_tube_haar (w : Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 12) (polyMul P (tubeChain [w,w,w] boundary)) ≈
      qpow w 36 * quaternionHaar blocks (polyMul P boundary) :=
  homogeneous_tube_haar w 3 blocks boundary

theorem plaquette_mean_zero : quaternionHaar 4 P ≈ 0 := by decide +kernel

theorem plaquette_square_one : quaternionHaar 4 (polyMul P P) ≈ 1 := by decide +kernel

/-- Closing with the actual top character gives exactly the transmission. -/
theorem tubeChain_closed (ws : List Q') :
    quaternionHaar (4 + 4*ws.length) (polyMul P (tubeChain ws P)) ≈ transmission ws :=
  Q'.eqv_trans _ _ _ (tubeChain_haar ws 4 P)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ plaquette_square_one) (Q'.mul_one_eqv _))

theorem tubeChain_one_end_zero (ws : List Q') :
    quaternionHaar (4 + 4*ws.length) (polyMul P (tubeChain ws polyOne)) ≈ 0 := by
  have hm := Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_one_right 4 P) plaquette_mean_zero
  exact Q'.eqv_trans _ _ _ (tubeChain_haar ws 4 polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.mul_zero_eqv _))

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

theorem transmission_positive (ws : List Q') (hw : ∀ w, w ∈ ws → (0 : Q') < w) :
    (0 : Q') < transmission ws := by
  induction ws with
  | nil => decide
  | cons w ws ih =>
      exact Q'.mul_pos (qpow_positive (hw w List.mem_cons_self) 12)
        (ih (fun v hv => hw v (List.mem_cons_of_mem w hv)))

/-- Strict positivity of THIS displayed selected Haar term, not the full response. -/
theorem tubeChain_closed_positive (ws : List Q') (hw : ∀ w, w ∈ ws → (0 : Q') < w) :
    (0 : Q') < quaternionHaar (4 + 4*ws.length) (polyMul P (tubeChain ws P)) :=
  Q'.pos_of_lt_of_le (transmission_positive ws hw) (Q'.ge_of_eqv (tubeChain_closed ws))

theorem threeLayer_closed (w : Q') :
    quaternionHaar 16 (polyMul P (tubeChain [w,w,w] P)) ≈ qpow w 36 :=
  Q'.eqv_trans _ _ _ (tubeChain_closed [w,w,w]) (transmission_constant w 3)

/-- Without the lower probe insertion, every selected tube layer integrates
to zero. The boundary can still contain arbitrary further layers/spectators. -/
theorem addLayer_without_probe_zero (w : Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks+4) (addLayer w boundary) ≈ 0 := by
  let fs := [sideCharacter 0 4, sideCharacter 1 5, sideCharacter 2 6, sideCharacter 3 7]
  have h := partialFactors_boundary_haar 4 blocks fs boundary
  have hf : partialFactors 4 fs = [polyZero,polyZero,polyZero,polyZero] := by
    dsimp only [fs]
    decide +kernel
  have hz : factorProduct (partialFactors 4 fs ++ [boundary]) = polyZero := by rw [hf]; rfl
  rw [hz] at h
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_zero_eqv _))

theorem tubeChain_without_probe_zero (w : Q') (ws : List Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 4*(w::ws).length) (tubeChain (w::ws) boundary) ≈ 0 := by
  have hn : blocks + 4*(w::ws).length = (blocks + 4*ws.length) + 4 := by simp; omega
  rw [hn]
  exact addLayer_without_probe_zero w (blocks + 4*ws.length) (tubeChain ws boundary)

def centeredPlaquette (c : Q') : RatPoly := polyAdd P (polySmul (-c) polyOne)

private theorem centered_end_moment (d : Q') : quaternionHaar 4 (polyMul P (centeredPlaquette d)) ≈ 1 := by
  have hz := Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right 4 (-d) P polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_one_right 4 P) plaquette_mean_zero)) (Q'.mul_zero_eqv _))
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' plaquette_square_one hz) (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The selected connected signal is unchanged by ANY centering constants.
This removes the disconnected endpoint terms for this exact tube, not for
the remaining interacting face selections. -/
theorem tubeChain_centering_invariant (w : Q') (ws : List Q') (c d : Q') :
    quaternionHaar (4 + 4*(w::ws).length)
        (polyMul (centeredPlaquette c) (tubeChain (w::ws) (centeredPlaquette d))) ≈
      transmission (w::ws) := by
  let blocks := 4 + 4*(w::ws).length
  let chain := tubeChain (w::ws) (centeredPlaquette d)
  have hmain := Q'.eqv_trans _ _ _ (tubeChain_haar (w::ws) 4 (centeredPlaquette d))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (centered_end_moment d)) (Q'.mul_one_eqv _))
  have hunit : quaternionHaar blocks (polyMul polyOne chain) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_one_right _ _)
        (tubeChain_without_probe_zero w ws 4 (centeredPlaquette d)))
  have hconstant : quaternionHaar blocks (polyMul (polySmul (-c) polyOne) chain) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _) hunit)) (Q'.mul_zero_eqv _)))
  rw [centeredPlaquette, polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hmain hconstant) (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem threeLayer_centering_invariant (w c d : Q') :
    quaternionHaar 16 (polyMul (centeredPlaquette c) (tubeChain [w,w,w] (centeredPlaquette d))) ≈
      qpow w 36 :=
  Q'.eqv_trans _ _ _ (tubeChain_centering_invariant w [w,w] c d) (transmission_constant w 3)

end YMGap.Continuum.SU2QuaternionFundamentalTubeComposition

#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.addLayer
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.transmission
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.addLayer_haar
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_haar
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.transmission_constant
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.homogeneous_tube_haar
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.threeLayer_tube_haar
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.plaquette_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.plaquette_square_one
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_closed
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_one_end_zero
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.transmission_positive
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_closed_positive
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.threeLayer_closed
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.addLayer_without_probe_zero
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_without_probe_zero
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.centeredPlaquette
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.tubeChain_centering_invariant
#print axioms YMGap.Continuum.SU2QuaternionFundamentalTubeComposition.threeLayer_centering_invariant
