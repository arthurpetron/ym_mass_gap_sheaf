/-
# Four full heat kernels transmit the ordered plaquette by w^12

Every kernel contains all spins 0..K. The boundary polynomial is retained
on the same carrier, with explicit support and independence from the four
eliminated lower links. No independence of the full interacting action is
asserted. This is an exact finite Haar identity, not a spectral bound.
-/

import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation

namespace YMGap.Continuum.SU2QuaternionFullHeatTubeLayer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

local infix:50 " ≈ " => Q'.eqv

/-- Remaining original packet factors, followed by the SAME insertion. -/
def pending (offset : Nat) (w : Q') (K : Nat) : Nat → RatPoly → RatPoly
  | 0, r => polyMul (heatAt offset (offset+4) w K) (polyMul (heatAt (offset+1) (offset+5) w K)
      (polyMul (heatAt (offset+2) (offset+6) w K) (polyMul (heatAt (offset+3) (offset+7) w K) r)))
  | 1, r => polyMul (heatAt (offset+1) (offset+5) w K)
      (polyMul (heatAt (offset+2) (offset+6) w K) (polyMul (heatAt (offset+3) (offset+7) w K) r))
  | 2, r => polyMul (heatAt (offset+2) (offset+6) w K) (polyMul (heatAt (offset+3) (offset+7) w K) r)
  | 3, r => polyMul (heatAt (offset+3) (offset+7) w K) r
  | _, r => r

theorem pending_step (offset : Nat) (w : Q') (K : Nat) (i : Fin 4) (r : RatPoly) :
    pending offset w K i.val r = polyMul (heatAt (offset+i.val) (offset+(i.val+4)) w K)
      (pending offset w K (i.val+1) r) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Fin.ext_iff]; omega
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem pending_supported {blocks offset : Nat} (hb : offset+7 < blocks) (w : Q') (K start : Nat)
    (r : RatPoly) (hr : SupportedQuaternionBlocks blocks r) :
    SupportedQuaternionBlocks blocks (pending offset w K start r) := by
  have hk (j : Nat) (hj : j < 4) : SupportedQuaternionBlocks blocks (heatAt (offset+j) (offset+(j+4)) w K) :=
    heat_supported (by omega) (by omega) w K
  match start with
  | 0 => exact supported_polyMul (hk 0 (by decide)) (supported_polyMul (hk 1 (by decide))
      (supported_polyMul (hk 2 (by decide)) (supported_polyMul (hk 3 (by decide)) hr)))
  | 1 => exact supported_polyMul (hk 1 (by decide)) (supported_polyMul (hk 2 (by decide)) (supported_polyMul (hk 3 (by decide)) hr))
  | 2 => exact supported_polyMul (hk 2 (by decide)) (supported_polyMul (hk 3 (by decide)) hr)
  | 3 => exact supported_polyMul (hk 3 (by decide)) hr
  | _+4 => exact hr

/-- Earlier slots do not occur in the remaining kernels. -/
theorem pending_independent (offset slot : Nat) (w : Q') (K start : Nat) (r : RatPoly)
    (hr : HasQuaternionBlockDegree slot 0 r) (hl : slot < offset+start) (hu : slot < offset+4) :
    HasQuaternionBlockDegree slot 0 (pending offset w K start r) := by
  have hk (j : Nat) (hj : start ≤ j) : HasQuaternionBlockDegree slot 0 (heatAt (offset+j) (offset+(j+4)) w K) :=
    heat_independent slot (offset+j) (offset+(j+4)) (by omega) (by omega) w K
  match start with
  | 0 => exact (hk 0 (by omega)).mul ((hk 1 (by omega)).mul ((hk 2 (by omega)).mul ((hk 3 (by omega)).mul hr)))
  | 1 => exact (hk 1 (by omega)).mul ((hk 2 (by omega)).mul ((hk 3 (by omega)).mul hr))
  | 2 => exact (hk 2 (by omega)).mul ((hk 3 (by omega)).mul hr)
  | 3 => exact (hk 3 (by omega)).mul hr
  | _+4 => exact hr

theorem stage_haar (tailBlocks offset : Nat) (hb : offset+7 < tailBlocks+1) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (i : Fin 4) (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : HasQuaternionBlockDegree (offset+i.val) 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (stagedPlaquette offset i.val) (pending offset w K i.val r)) ≈
      qpow w 3 * quaternionHaar (tailBlocks+1)
        (polyMul (stagedPlaquette offset (i.val+1)) (pending offset w K (i.val+1) r)) := by
  rw [pending_step]
  have hperm := ((RatPolyCoeffEqv.mul_assoc (stagedPlaquette offset i.val)
    (heatAt (offset+i.val) (offset+(i.val+4)) w K) (pending offset w K (i.val+1) r)).symm.trans
    ((RatPolyCoeffEqv.mul_comm _ _).mul_right _)).trans (RatPolyCoeffEqv.mul_assoc _ _ _)
  refine Q'.eqv_trans _ _ _ (haar_of_coeff hperm) ?_
  exact (plaquette_step tailBlocks offset hb w K hK i).pairing _
    (pending_supported hb w K (i.val+1) r hr)
    (pending_independent offset (offset+i.val) w K (i.val+1) r hd (by omega) (by omega))

private theorem four_factors (w z : Q') :
    qpow w 3 * (qpow w 3 * (qpow w 3 * (qpow w 3 * z))) ≈ qpow w 12 * z := by
  have h (a b : Nat) (v : Q') : qpow w a * (qpow w b * v) ≈ qpow w (a+b) * v :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (qpow_add w a b)))
  exact Q'.eqv_trans _ _ _ (h 3 3 _) (Q'.eqv_trans _ _ _ (h 6 3 _) (h 9 3 _))

/-- A full-cutoff layer, with no selected-spin replacement on the left. -/
theorem one_layer (tailBlocks offset : Nat) (hb : offset+7 < tailBlocks+1) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ i : Fin 4, HasQuaternionBlockDegree (offset+i.val) 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (plaquette offset (offset+1) (offset+2) (offset+3))
      (pending offset w K 0 r)) ≈ qpow w 12 * quaternionHaar (tailBlocks+1)
        (polyMul (plaquette (offset+4) (offset+5) (offset+6) (offset+7)) r) := by
  have h0 := stage_haar tailBlocks offset hb w K hK 0 r hr (hd 0)
  have h1 := stage_haar tailBlocks offset hb w K hK 1 r hr (hd 1)
  have h2 := stage_haar tailBlocks offset hb w K hK 2 r hr (hd 2)
  have h3 := stage_haar tailBlocks offset hb w K hK 3 r hr (hd 3)
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ h1 (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ h2 (Q'.mul_eqv_congr_left _ _ _ h3))))) (four_factors w _))

end YMGap.Continuum.SU2QuaternionFullHeatTubeLayer

#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.pending
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.pending_step
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.pending_supported
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.pending_independent
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.stage_haar
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeLayer.one_layer
