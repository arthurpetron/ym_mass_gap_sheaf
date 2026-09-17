/-
# Positive-spin selection for arbitrary orientations of an exposed word

The same full Haar carrier and every retained multiplier are preserved.
Only the exposed block is required independent. Cyclic scalar identities
rotate the word without commuting its quaternion factors.
-/

import YMGap.Continuum.SU2QuaternionFourBlockSelection
import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionOrientedWordSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)

local infix:50 " ≈ " => Q'.eqv

def word (a b c d : Nat) (r0 r1 r2 r3 : Bool) : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
    (orientedCoordinateQuaternion a r0) (orientedCoordinateQuaternion b r1))
    (orientedCoordinateQuaternion c r2)) (orientedCoordinateQuaternion d r3)

theorem scalar_cyclic (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul a b) c) d).scalar
      (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul b c) d) a).scalar :=
  (((PolyQuaternionCoeffEqv.mul_assoc a b c).mul (PolyQuaternionCoeffEqv.refl d)).trans
    (PolyQuaternionCoeffEqv.mul_assoc a (PolyQuaternion.mul b c) d)).scalar.trans
      (polyQuaternion_mul_scalar_cyclic a (PolyQuaternion.mul (PolyQuaternion.mul b c) d))

theorem word_cyclic (a b c d : Nat) (r0 r1 r2 r3 : Bool) :
    RatPolyCoeffEqv (word a b c d r0 r1 r2 r3).scalar (word b c d a r1 r2 r3 r0).scalar :=
  scalar_cyclic _ _ _ _

private theorem oriented_supported {blocks block : Nat} (h : block < blocks) (r : Bool) :
    Supported blocks (orientedCoordinateQuaternion block r) := by
  cases r
  · exact Supported.coordinate h
  · exact (Supported.coordinate h).conj

theorem word_supported {blocks a b c d : Nat} (ha : a < blocks) (hb : b < blocks)
    (hc : c < blocks) (hd : d < blocks) (r0 r1 r2 r3 : Bool) (spin : Nat) :
    SupportedQuaternionBlocks blocks (characterPolynomial (word a b c d r0 r1 r2 r3).scalar spin) :=
  character_supported ((((oriented_supported ha r0).mul (oriented_supported hb r1)).mul
    (oriented_supported hc r2)).mul (oriented_supported hd r3)).scalar spin

theorem word_prefix {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool) : QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion e.steps (word a.val b.val c.val d.val r0 r1 r2 r3))
      (exposedFourWord r0 r1 r2 r3) := by
  unfold word
  rw [applyQuaternionBlockSwapChainQuaternion_mul, applyQuaternionBlockSwapChainQuaternion_mul,
    applyQuaternionBlockSwapChainQuaternion_mul]
  exact (((applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps (by omega) e.source_zero r0).mul
    (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps (by omega) e.source_one r1)).mul
    (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps (by omega) e.source_two r2)).mul
    (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps hb e.source_three r3)

theorem character_prefix {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool) (spin : Nat) : QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain e.steps (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin))
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) := by
  have h := (word_prefix hb e r0 r1 r2 r3).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at h
  exact (applyQuaternionBlockSwapChain_character_prefix e.steps _ spin).trans (h.character spin)

theorem head_bound_zero : ∀ p : RatPoly, HasQuaternionBlockDegree 0 0 p → headDegreeBound p = 0
  | [], _ => rfl
  | t::p, h => by
    rw [headDegreeBound, h t List.mem_cons_self,
      head_bound_zero p (fun s hs => h s (List.mem_cons_of_mem t hs))]
    rfl

/-- Every positive spin, including even spins, has zero conditional mean. -/
theorem selected_zero {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool) (spin : Nat) (hs : 0 < spin)
    (q : RatPoly) (hq : SupportedQuaternionBlocks blocks q) (hd : HasQuaternionBlockDegree a.val 0 q) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin) q) ≈ 0 := by
  have hc := word_supported a.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 spin
  have hcan := word_supported (blocks := blocks) (by omega : 0 < blocks) (by omega : 1 < blocks)
    (by omega : 2 < blocks) hb r0 r1 r2 r3 spin
  have htq := applyQuaternionBlockSwapChain_supported e.steps q hq
  have htd : HasQuaternionBlockDegree 0 0 (applyQuaternionBlockSwapChain e.steps q) := by
    apply chain_degree e.steps (by omega)
    rw [e.source_zero]
    exact hd
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_applyQuaternionBlockSwapChain e.steps _
    (supported_polyMul hc hq))) ?_
  rw [chain_mul]
  refine Q'.eqv_trans _ _ _ (quaternionHaar_prefixPolynomialEqv blocks
    ((character_prefix hb e r0 r1 r2 r3 spin).mul (QuaternionPrefixPolynomialEqv.refl blocks _))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported e.steps _ hc) htq)
    (supported_polyMul hcan htq)) ?_
  exact exposedCharacter_haar_zero hb r0 r1 r2 r3 spin _ (by rw [head_bound_zero _ htd]; exact hs)

theorem haar_cyclic (blocks a b c d : Nat) (r0 r1 r2 r3 : Bool) (spin : Nat) (q : RatPoly) :
    quaternionHaar blocks (polyMul (characterPolynomial (word a b c d r0 r1 r2 r3).scalar spin) q) ≈
      quaternionHaar blocks (polyMul (characterPolynomial (word b c d a r1 r2 r3 r0).scalar spin) q) :=
  QuaternionHaarSquareCertificate.haar_of_coeff
    ((characterPolynomial_coeffEqv (word_cyclic a b c d r0 r1 r2 r3) spin).mul (RatPolyCoeffEqv.refl q))

/-- A retained multiplier may depend on all three other links and all spectators. -/
theorem any_slot_zero {blocks : Nat} (hb : 3 < blocks) (a b c d : Fin blocks)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (r0 r1 r2 r3 : Bool) (spin : Nat) (hs : 0 < spin) (q : RatPoly)
    (hq : SupportedQuaternionBlocks blocks q) (slot : Nat)
    (hm : slot = a.val ∨ slot = b.val ∨ slot = c.val ∨ slot = d.val)
    (hd : HasQuaternionBlockDegree slot 0 q) :
    quaternionHaar blocks (polyMul (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin) q) ≈ 0 := by
  rcases hm with rfl | rfl | rfl | rfl
  · exact selected_zero hb (fourBlockExposure hb a b c d hab hac had hbc hbd hcd) r0 r1 r2 r3 spin hs q hq hd
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin q)
      (selected_zero hb (fourBlockExposure hb b c d a hbc hbd (Ne.symm hab) hcd (Ne.symm hac) (Ne.symm had))
        r1 r2 r3 r0 spin hs q hq hd)
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin q)
      (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r1 r2 r3 r0 spin q)
        (selected_zero hb (fourBlockExposure hb c d a b hcd (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd) hab)
          r2 r3 r0 r1 spin hs q hq hd))
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin q)
      (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r1 r2 r3 r0 spin q)
        (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r2 r3 r0 r1 spin q)
          (selected_zero hb (fourBlockExposure hb d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc)
            r3 r0 r1 r2 spin hs q hq hd)))

/-- Higher-spin selection for every orientation, with the entire independent
spectator retained. The bound sees only the fixed insertion after exposure. -/
theorem selected_product_zero {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool) (spin : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (hd : HasQuaternionBlockDegree a.val 0 q) (hs : selectionBound e p < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin)
      (polyMul p q)) ≈ 0 := by
  have hc := word_supported a.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 spin
  have hcan := word_supported (blocks := blocks) (by omega : 0 < blocks) (by omega : 1 < blocks)
    (by omega : 2 < blocks) hb r0 r1 r2 r3 spin
  have htp := applyQuaternionBlockSwapChain_supported e.steps p hp
  have htq := applyQuaternionBlockSwapChain_supported e.steps q hq
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_applyQuaternionBlockSwapChain e.steps _
    (supported_polyMul hc (supported_polyMul hp hq)))) ?_
  rw [chain_mul, chain_mul]
  refine Q'.eqv_trans _ _ _ (quaternionHaar_prefixPolynomialEqv blocks
    ((character_prefix hb e r0 r1 r2 r3 spin).mul (QuaternionPrefixPolynomialEqv.refl blocks _))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported e.steps _ hc) (supported_polyMul htp htq))
    (supported_polyMul hcan (supported_polyMul htp htq))) ?_
  apply SU2QuaternionAllCarrierExposedSelection.exposedCharacter_independent_product_zero
    hb r0 r1 r2 r3 spin _ _ _ hs
  apply chain_degree e.steps (by omega)
  rw [e.source_zero]
  exact hd

private theorem head_bound_le_of_degree : ∀ (p : RatPoly) (degree : Nat),
    HasQuaternionBlockDegree 0 degree p → headDegreeBound p ≤ degree
  | [], _, _ => Nat.zero_le _
  | t::p, degree, h => by
    change max (quaternionBlockDegree t.1 0) (headDegreeBound p) ≤ degree
    exact Nat.max_le.mpr ⟨Nat.le_of_eq (h t List.mem_cons_self),
      head_bound_le_of_degree p degree (fun s hs => h s (List.mem_cons_of_mem t hs))⟩

private theorem selected_homogeneous_product_zero {blocks : Nat} (hb : 3 < blocks)
    {a b c d : Fin blocks} (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool)
    (spin degree : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree a.val degree p) (hdq : HasQuaternionBlockDegree a.val 0 q)
    (hs : degree < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin)
      (polyMul p q)) ≈ 0 := by
  apply selected_product_zero hb e r0 r1 r2 r3 spin p q hp hq hdq
  apply Nat.lt_of_le_of_lt (head_bound_le_of_degree _ degree ?_) hs
  apply chain_degree e.steps (by omega)
  rw [e.source_zero]
  exact hdp

/-- Select at any physical slot without commuting the quaternion factors.
The insertion may have arbitrary degree at every other coordinate; the
spectator may share all of those coordinates and all remaining variables. -/
theorem any_slot_product_zero {blocks : Nat} (hb : 3 < blocks) (a b c d : Fin blocks)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (r0 r1 r2 r3 : Bool) (spin : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (slot degree : Nat)
    (hm : slot = a.val ∨ slot = b.val ∨ slot = c.val ∨ slot = d.val)
    (hdp : HasQuaternionBlockDegree slot degree p) (hdq : HasQuaternionBlockDegree slot 0 q)
    (hs : degree < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar spin)
      (polyMul p q)) ≈ 0 := by
  rcases hm with rfl | rfl | rfl | rfl
  · exact selected_homogeneous_product_zero hb
      (fourBlockExposure hb a b c d hab hac had hbc hbd hcd)
      r0 r1 r2 r3 spin degree p q hp hq hdp hdq hs
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin (polyMul p q))
      (selected_homogeneous_product_zero hb
        (fourBlockExposure hb b c d a hbc hbd (Ne.symm hab) hcd (Ne.symm hac) (Ne.symm had))
        r1 r2 r3 r0 spin degree p q hp hq hdp hdq hs)
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin (polyMul p q))
      (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r1 r2 r3 r0 spin (polyMul p q))
        (selected_homogeneous_product_zero hb
          (fourBlockExposure hb c d a b hcd (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd) hab)
          r2 r3 r0 r1 spin degree p q hp hq hdp hdq hs))
  · exact Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r0 r1 r2 r3 spin (polyMul p q))
      (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r1 r2 r3 r0 spin (polyMul p q))
        (Q'.eqv_trans _ _ _ (haar_cyclic blocks _ _ _ _ r2 r3 r0 r1 spin (polyMul p q))
          (selected_homogeneous_product_zero hb
            (fourBlockExposure hb d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc)
            r3 r0 r1 r2 spin degree p q hp hq hdp hdq hs)))

end YMGap.Continuum.SU2QuaternionOrientedWordSelection

#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.word
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.scalar_cyclic
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.word_cyclic
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.word_supported
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.word_prefix
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.character_prefix
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.head_bound_zero
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.selected_zero
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.haar_cyclic
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.any_slot_zero
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.selected_product_zero
#print axioms YMGap.Continuum.SU2QuaternionOrientedWordSelection.any_slot_product_zero
