/-
# Arbitrary-length propagation through full finite heat kernels

Consecutive layers share their four physical boundary variables on one
fixed Haar carrier. Every heat kernel contains the complete packet 0..K.
All spectator variables and the terminal polynomial remain on that carrier.

The dependence on each layer's nome is explicit: the exact transmission is
the product of w_i^12, or w^(12*n) at constant nome. This does not control
the interacting background, whose factors may use the eliminated links.
-/

import YMGap.Continuum.SU2QuaternionFullHeatTubeLayer
import YMGap.Continuum.SU2QuaternionFundamentalTubeComposition

namespace YMGap.Continuum.SU2QuaternionFullHeatTubeComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionFundamentalTubeComposition (transmission transmission_constant)
open YMGap.Continuum.SU2QuaternionFullHeatTubeLayer

local infix:50 " ≈ " => Q'.eqv

/-- The original four-factor ordered plaquette on one slice. -/
def slice (offset : Nat) : RatPoly := plaquette offset (offset+1) (offset+2) (offset+3)

/-- Each full layer reuses the preceding layer's actual upper variables. -/
def chain (offset K : Nat) : List Q' → RatPoly → RatPoly
  | [], r => r
  | w::ws, r => pending offset w K 0 (chain (offset+4) K ws r)

theorem chain_supported {blocks : Nat} (offset K : Nat) (ws : List Q')
    (hb : offset+4*ws.length+3 < blocks) (r : RatPoly) (hr : SupportedQuaternionBlocks blocks r) :
    SupportedQuaternionBlocks blocks (chain offset K ws r) := by
  induction ws generalizing offset with
  | nil => exact hr
  | cons w ws ih =>
    apply pending_supported (by simp only [List.length_cons] at hb; omega) w K 0
    exact ih (offset+4) (by simp only [List.length_cons] at hb; omega)

theorem chain_independent (offset slot K : Nat) (ws : List Q') (r : RatPoly)
    (hd : HasQuaternionBlockDegree slot 0 r) (hs : slot < offset) :
    HasQuaternionBlockDegree slot 0 (chain offset K ws r) := by
  induction ws generalizing offset with
  | nil => exact hd
  | cons w ws ih =>
    exact pending_independent offset slot w K 0 _ (ih (offset+4) (by omega)) (by omega) (by omega)

/-- All-length same-carrier propagation. The only boundary independence
required is from precisely the lower 4*length links that are eliminated. -/
theorem chain_haar (tailBlocks offset K : Nat) (hK : 1 ≤ K) (ws : List Q')
    (hb : offset+4*ws.length+3 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+4*ws.length → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (slice offset) (chain offset K ws r)) ≈
      transmission ws * quaternionHaar (tailBlocks+1) (polyMul (slice (offset+4*ws.length)) r) := by
  induction ws generalizing offset with
  | nil => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | cons w ws ih =>
    have ht : offset+4+4*ws.length+3 < tailBlocks+1 := by simp only [List.length_cons] at hb; omega
    have hs := chain_supported (offset+4) K ws ht r hr
    have hi (i : Fin 4) : HasQuaternionBlockDegree (offset+i.val) 0 (chain (offset+4) K ws r) :=
      chain_independent (offset+4) (offset+i.val) K ws r
        (hd (offset+i.val) (by omega) (by simp only [List.length_cons]; omega)) (by omega)
    have h1 := one_layer tailBlocks offset (by simp only [List.length_cons] at hb; omega) w K hK _ hs hi
    have h2 := ih (offset+4) ht (fun slot hl hu => hd slot (by omega) (by simp only [List.length_cons]; omega))
    have he : offset+4+4*ws.length = offset+4*(w::ws).length := by simp only [List.length_cons]; omega
    rw [he] at h2
    exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

theorem homogeneous_chain_haar (tailBlocks offset K n : Nat) (hK : 1 ≤ K) (w : Q')
    (hb : offset+4*n+3 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+4*n → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (slice offset) (chain offset K (List.replicate n w) r)) ≈
      qpow w (12*n) * quaternionHaar (tailBlocks+1) (polyMul (slice (offset+4*n)) r) := by
  have h := chain_haar tailBlocks offset K hK (List.replicate n w) (by simpa only [List.length_replicate] using hb)
    r hr (by simpa only [List.length_replicate] using hd)
  simp only [List.length_replicate] at h
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _ (transmission_constant w n))

/-- Three layers of the full packet, not twelve selected spin-one factors. -/
theorem three_layer_haar (tailBlocks offset K : Nat) (hK : 1 ≤ K) (w : Q')
    (hb : offset+15 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+12 → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (slice offset) (chain offset K [w,w,w] r)) ≈
      qpow w 36 * quaternionHaar (tailBlocks+1) (polyMul (slice (offset+12)) r) :=
  homogeneous_chain_haar tailBlocks offset K 3 hK w hb r hr hd

end YMGap.Continuum.SU2QuaternionFullHeatTubeComposition

#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.slice
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.chain
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.chain_supported
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.chain_independent
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.chain_haar
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.homogeneous_chain_haar
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeComposition.three_layer_haar
