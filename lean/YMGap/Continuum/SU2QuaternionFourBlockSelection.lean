/-
# Exact high-spin cancellation for any four distinct physical coordinates

The explicit four-block exposure is connected to the original ordered
word a b c^-1 d^-1 and to the same full product-Haar functional. Every
multiplier is transported, with support checked on both sides. A factor
independent of a may have unrestricted degrees in all other variables.

The computable selection bound depends only on the fixed insertion after
the four swaps. No averaging over the remaining factors, spectral estimate,
or unproved analytic input enters this result.
-/

import YMGap.Continuum.SU2QuaternionFourBlockExposure
import YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionFourBlockSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
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
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.SU2QuaternionFourBlockExposure

local infix:50 " ≈ " => Q'.eqv

def coordinateWord (a b c d : Nat) : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
    (orientedCoordinateQuaternion a false) (orientedCoordinateQuaternion b false))
    (orientedCoordinateQuaternion c true)) (orientedCoordinateQuaternion d true)

theorem word_prefix {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) : QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion e.steps (coordinateWord a.val b.val c.val d.val))
      (exposedFourWord false false true true) := by
  unfold coordinateWord
  rw [applyQuaternionBlockSwapChainQuaternion_mul, applyQuaternionBlockSwapChainQuaternion_mul,
    applyQuaternionBlockSwapChainQuaternion_mul]
  exact (((applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps (by omega)
    e.source_zero false).mul (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps
      (by omega) e.source_one false)).mul
    (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps (by omega) e.source_two true)).mul
    (applyQuaternionBlockSwapChain_orientedCoordinate_prefix e.steps hb e.source_three true)

theorem character_prefix {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (spin : Nat) : QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain e.steps (characterPolynomial (coordinateWord a.val b.val c.val d.val).scalar spin))
      (characterPolynomial (exposedFourWord false false true true).scalar spin) := by
  have hw := (word_prefix hb e).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hw
  exact (applyQuaternionBlockSwapChain_character_prefix e.steps _ spin).trans (hw.character spin)

theorem chain_mul {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyMul p q) =
      polyMul (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons swap rest ih =>
    simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_mul, ih]

theorem chain_coeff {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => exact h
  | cons swap rest ih => exact ih (RatPolyCoeffEqv.reindex swap h)

theorem chain_degree {blocks target degree : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (ht : target < blocks) {p : RatPoly}
    (hd : HasQuaternionBlockDegree (quaternionBlockSwapChainSource steps target) degree p) :
    HasQuaternionBlockDegree target degree (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing target p with
  | nil => exact hd
  | cons swap rest ih =>
    exact ih ht (blockDegree_reindex swap (quaternionBlockSwapChainSource_lt rest ht) rfl hd)

private theorem supported_polyOne (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem supported_polyVar {blocks i : Nat} (hi : i < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar i) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem supported_polyAdd {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := fun t ht =>
  (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem supported_polyNeg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem supported_polySmul {blocks : Nat} {p : RatPoly} {a : Q'}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private structure QSupported (blocks : Nat) (q : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks q.scalar
  iPart : SupportedQuaternionBlocks blocks q.iPart
  jPart : SupportedQuaternionBlocks blocks q.jPart
  kPart : SupportedQuaternionBlocks blocks q.kPart

private theorem QSupported.conj {blocks : Nat} {q : PolyQuaternion} (h : QSupported blocks q) :
    QSupported blocks (PolyQuaternion.conj q) :=
  ⟨h.scalar, supported_polyNeg h.iPart, supported_polyNeg h.jPart, supported_polyNeg h.kPart⟩

private theorem QSupported.mul {blocks : Nat} {p q : PolyQuaternion}
    (hp : QSupported blocks p) (hq : QSupported blocks q) : QSupported blocks (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply supported_polyAdd | apply supported_polyNeg | apply supported_polyMul

private theorem coordinate_support {blocks block : Nat} (hb : block < blocks) :
    QSupported blocks (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_polyVar <;> omega

private theorem character_support {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    ∀ spin, SupportedQuaternionBlocks blocks (characterPolynomial p spin)
  | 0 => supported_polyOne blocks
  | 1 => supported_polySmul hp
  | spin + 2 => supported_polyAdd
      (supported_polyMul (supported_polySmul hp) (character_support hp (spin + 1)))
      (supported_polySmul (character_support hp spin))

theorem word_character_support {blocks a b c d : Nat}
    (ha : a < blocks) (hb : b < blocks) (hc : c < blocks) (hd : d < blocks) (spin : Nat) :
    SupportedQuaternionBlocks blocks (characterPolynomial (coordinateWord a b c d).scalar spin) :=
  character_support ((((coordinate_support ha).mul (coordinate_support hb)).mul
    (coordinate_support hc).conj).mul (coordinate_support hd).conj).scalar spin

/-- The other factors never enter this computable degree bound. -/
def selectionBound {blocks : Nat} {a b c d : Fin blocks} (e : FourBlockExposure a b c d) (p : RatPoly) : Nat :=
  headDegreeBound (applyQuaternionBlockSwapChain e.steps p)

/-- Same full Haar carrier, original four-link word, unrestricted independent factor. -/
theorem selected_product_zero {blocks : Nat} (hb : 3 < blocks) {a b c d : Fin blocks}
    (e : FourBlockExposure a b c d) (spin : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (hd : HasQuaternionBlockDegree a.val 0 q) (hs : selectionBound e p < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (coordinateWord a.val b.val c.val d.val).scalar spin) (polyMul p q)) ≈ 0 := by
  have hc := word_character_support a.isLt b.isLt c.isLt d.isLt spin
  have hcan : SupportedQuaternionBlocks blocks
      (characterPolynomial (exposedFourWord false false true true).scalar spin) :=
    word_character_support (by omega) (by omega) (by omega) hb spin
  have htp := applyQuaternionBlockSwapChain_supported e.steps p hp
  have htq := applyQuaternionBlockSwapChain_supported e.steps q hq
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_applyQuaternionBlockSwapChain e.steps _
    (supported_polyMul hc (supported_polyMul hp hq)))) ?_
  rw [chain_mul, chain_mul]
  refine Q'.eqv_trans _ _ _ (quaternionHaar_prefixPolynomialEqv blocks
    ((character_prefix hb e spin).mul (QuaternionPrefixPolynomialEqv.refl blocks _))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported e.steps _ hc) (supported_polyMul htp htq))
    (supported_polyMul hcan (supported_polyMul htp htq))) ?_
  apply exposedCharacter_independent_product_zero hb false false true true spin _ _ _ hs
  apply chain_degree e.steps (by omega)
  rw [e.source_zero]
  exact hd

end YMGap.Continuum.SU2QuaternionFourBlockSelection

#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.coordinateWord
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.word_prefix
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.character_prefix
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.chain_mul
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.chain_coeff
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.chain_degree
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.word_character_support
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.selectionBound
#print axioms YMGap.Continuum.SU2QuaternionFourBlockSelection.selected_product_zero
