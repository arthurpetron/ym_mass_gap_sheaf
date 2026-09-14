/-
# Exact connected transmission, including the boundary's nonzero mean

The full tube preserves the boundary mass and sends the lower plaquette's
conditional mean to transmission times the upper plaquette. Consequently
its connected numerator is exactly transmission times the upper boundary
variance numerator. The identity is valid even for signed boundary data;
it does not assert positivity without a positive boundary law.

This proves the vacuum subtraction algebraically before any error estimate.
It does not bound the remaining plaquettes using eliminated tube links.
-/

import YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum

namespace YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionFullHeatTubeLayer
open YMGap.Continuum.SU2QuaternionFullHeatTubeComposition
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionFundamentalTubeComposition (transmission transmission_constant)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Unnormalized connected moment: the partition is not silently set to one. -/
def connectedNumerator (blocks : Nat) (p q weight : RatPoly) : Q' :=
  quaternionHaar blocks weight * quaternionHaar blocks (polyMul p (polyMul q weight)) +
    -(quaternionHaar blocks (polyMul p weight) * quaternionHaar blocks (polyMul q weight))

theorem pending_congr (offset : Nat) (w : Q') (K start : Nat) {r s : RatPoly} (h : RatPolyCoeffEqv r s) :
    RatPolyCoeffEqv (pending offset w K start r) (pending offset w K start s) := by
  match start with
  | 0 => exact (((h.mul_left _).mul_left _).mul_left _).mul_left _
  | 1 => exact ((h.mul_left _).mul_left _).mul_left _
  | 2 => exact (h.mul_left _).mul_left _
  | 3 => exact h.mul_left _
  | _+4 => exact h

theorem pending_right_mul (offset : Nat) (w : Q') (K start : Nat) (r q : RatPoly) :
    RatPolyCoeffEqv (polyMul (pending offset w K start r) q) (pending offset w K start (polyMul r q)) := by
  have go (k : RatPoly) {p p' : RatPoly} (h : RatPolyCoeffEqv (polyMul p q) p') :
      RatPolyCoeffEqv (polyMul (polyMul k p) q) (polyMul k p') :=
    (RatPolyCoeffEqv.mul_assoc k p q).trans (h.mul_left k)
  match start with
  | 0 => exact go _ (go _ (go _ (go _ (.refl _))))
  | 1 => exact go _ (go _ (go _ (.refl _)))
  | 2 => exact go _ (go _ (.refl _))
  | 3 => exact go _ (.refl _)
  | _+4 => exact .refl _

theorem chain_congr (offset K : Nat) (ws : List Q') {r s : RatPoly} (h : RatPolyCoeffEqv r s) :
    RatPolyCoeffEqv (chain offset K ws r) (chain offset K ws s) := by
  induction ws generalizing offset with
  | nil => exact h
  | cons w ws ih => exact pending_congr offset w K 0 (ih (offset+4))

theorem chain_right_mul (offset K : Nat) (ws : List Q') (r q : RatPoly) :
    RatPolyCoeffEqv (polyMul (chain offset K ws r) q) (chain offset K ws (polyMul r q)) := by
  induction ws generalizing offset with
  | nil => exact .refl _
  | cons w ws ih => exact (pending_right_mul offset w K 0 _ q).trans (pending_congr offset w K 0 (ih (offset+4)))

theorem chain_insert (offset K : Nat) (ws : List Q') (r q : RatPoly) :
    RatPolyCoeffEqv (polyMul q (chain offset K ws r)) (chain offset K ws (polyMul q r)) :=
  (RatPolyCoeffEqv.mul_comm _ _).trans ((chain_right_mul offset K ws r q).trans
    (chain_congr offset K ws (RatPolyCoeffEqv.mul_comm r q)))

theorem slice_supported {blocks : Nat} (offset : Nat) (hb : offset+3 < blocks) :
    SupportedQuaternionBlocks blocks (slice offset) := by
  have hs (j : Nat) (hj : j ≤ 3) : QuaternionSupported blocks (PolyQuaternion.coordinateVariable (offset+j)) :=
    QuaternionSupported.coordinate (by omega)
  exact character_supported ((((hs 0 (by decide)).mul (hs 1 (by decide))).mul
    (hs 2 (by decide)).conj).mul (hs 3 (by decide)).conj).scalar 1

theorem slice_independent (offset slot : Nat) (hs : slot < offset) : HasQuaternionBlockDegree slot 0 (slice offset) := by
  have hd (j : Nat) : HasPolyQuaternionBlockDegree slot 0 (PolyQuaternion.coordinateVariable (offset+j)) := by
    have h := hasPolyQuaternionBlockDegree_coordinateVariable (offset+j) slot
    rw [if_neg (show slot ≠ offset+j by omega)] at h
    exact h
  exact character_independent ((((hd 0).mul (hd 1)).mul (hd 2).conj).mul (hd 3).conj).scalar 1

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem scale_determinant (z t b a : Q') :
    z*(t*b) + -((t*a)*a) ≈ t*(z*b + -(a*a)) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.mul (.mul (.var 1) (.var 3)) (.var 3))))
    (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 3) (.var 3))))) (by decide)
    (fun | 0 => z | 1 => t | 2 => b | _ => a)

/-- All-length covariance propagation under arbitrary retained boundary
weight, with its mass and mean kept exactly, on one shared carrier. -/
theorem connected_transport (tailBlocks offset K : Nat) (hK : 1 ≤ K) (ws : List Q')
    (hb : offset+4*ws.length+3 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+4*ws.length → HasQuaternionBlockDegree slot 0 r) :
    connectedNumerator (tailBlocks+1) (slice offset) (slice (offset+4*ws.length)) (chain offset K ws r) ≈
      transmission ws * connectedNumerator (tailBlocks+1) (slice (offset+4*ws.length)) (slice (offset+4*ws.length)) r := by
  let top := slice (offset+4*ws.length)
  have ht := supported_polyMul (slice_supported _ hb) hr
  have hdt (slot : Nat) (hl : offset ≤ slot) (hu : slot < offset+4*ws.length) :
      HasQuaternionBlockDegree slot 0 (polyMul top r) := (slice_independent _ slot hu).mul (hd slot hl hu)
  have hz := chain_vacuum tailBlocks offset K ws hb r hr hd
  have hl := chain_haar tailBlocks offset K hK ws hb r hr hd
  have hp := chain_insert offset K ws r top
  have hu := Q'.eqv_trans _ _ _ (haar_of_coeff hp) (chain_vacuum tailBlocks offset K ws hb _ ht hdt)
  have hc := Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left (slice offset))) (chain_haar tailBlocks offset K hK ws hb _ ht hdt)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (qmul hz hc) (Q'.neg_eqv_congr _ _ (qmul hl hu))) ?_
  exact scale_determinant _ _ _ _

theorem three_layer_connected (tailBlocks offset K : Nat) (hK : 1 ≤ K) (w : Q')
    (hb : offset+15 < tailBlocks+1) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : ∀ slot : Nat, offset ≤ slot → slot < offset+12 → HasQuaternionBlockDegree slot 0 r) :
    connectedNumerator (tailBlocks+1) (slice offset) (slice (offset+12)) (chain offset K [w,w,w] r) ≈
      qpow w 36 * connectedNumerator (tailBlocks+1) (slice (offset+12)) (slice (offset+12)) r :=
  Q'.eqv_trans _ _ _ (connected_transport tailBlocks offset K hK [w,w,w] hb r hr hd)
    (Q'.mul_eqv_congr_right _ _ _ (transmission_constant w 3))

end YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance

#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.connectedNumerator
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.pending_congr
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.pending_right_mul
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.chain_congr
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.chain_right_mul
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.chain_insert
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.slice_supported
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.slice_independent
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.connected_transport
#print axioms YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance.three_layer_connected
