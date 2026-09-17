/-
# Signed multi-time Wilson expressions on the original window carrier

Each generator is a witnessed source spatial loop at an explicit time offset.
Its polynomial uses the existing chronological blocks; its placement uses the
literal shifted original link word. Sums, products and signed rational scales
retain every term and its order. The whole expression is pinned to ONE window
embedding and ONE original slab observable.

The actual physical Wilson algebra supplies temporal-ledger invariance with
the full supported insertion retained. No disjoint-link premise, trace
factorization, full gauge-observable coverage, union embedding or regulator
limit is asserted. Reflection changes offsets only; its geometric validity
and positivity are supplied by the separate reflection consumer.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
import YMGap.Continuum.BF4ExactSlabSpatialWilsonAlgebra
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier (embedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle (middle_polynomial_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (character character_supported)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction (originalChainAction ambientChain)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one supported_add)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- Finite signed syntax retains a complete ordered loop at every generator. -/
inductive WindowExpression (width : Nat) : Type where
  | one : WindowExpression width
  | loop (offset : Nat) (value : SourceLoop width) (spin : Nat) : WindowExpression width
  | add : WindowExpression width → WindowExpression width → WindowExpression width
  | mul : WindowExpression width → WindowExpression width → WindowExpression width
  | smul : Q' → WindowExpression width → WindowExpression width

def Within {width : Nat} (L : Nat) : WindowExpression width → Prop
  | .one => True
  | .loop offset _ _ => offset ≤ L
  | .add e f => Within L e ∧ Within L f
  | .mul e f => Within L e ∧ Within L f
  | .smul _ e => Within L e

/-- Source polynomials depend on width and offsets, never ambient size or placement. -/
def sourcePolynomial {width : Nat} : WindowExpression width → RatPoly
  | .one => polyOne
  | .loop offset value spin =>
      liftBoundary (offset*(N width)) (sourceCharacter width value.edges spin)
  | .add e f => polyAdd (sourcePolynomial e) (sourcePolynomial f)
  | .mul e f => polyMul (sourcePolynomial e) (sourcePolynomial f)
  | .smul c e => polySmul c (sourcePolynomial e)

/-- Literal original slab holonomies at start plus each source offset. -/
def placedPolynomial {width : Nat} (extent start : Nat) : WindowExpression width → RatPoly
  | .one => polyOne
  | .loop offset value spin =>
      character extent (value.edges.map (shiftEntry (start+offset))) spin
  | .add e f => polyAdd (placedPolynomial extent start e) (placedPolynomial extent start f)
  | .mul e f => polyMul (placedPolynomial extent start e) (placedPolynomial extent start f)
  | .smul c e => polySmul c (placedPolynomial extent start e)

/-- Change time offsets without changing any loop, spin, coefficient or operation. -/
def mapOffsets {width : Nat} (f : Nat → Nat) : WindowExpression width → WindowExpression width
  | .one => .one
  | .loop offset value spin => .loop (f offset) value spin
  | .add e g => .add (mapOffsets f e) (mapOffsets f g)
  | .mul e g => .mul (mapOffsets f e) (mapOffsets f g)
  | .smul c e => .smul c (mapOffsets f e)

def mirror {width : Nat} (h : Nat) (e : WindowExpression width) : WindowExpression width :=
  mapOffsets (fun offset => 2*h-offset) e

theorem within_mono {width L L' : Nat} (hL : L ≤ L') :
    ∀ e : WindowExpression width, Within L e → Within L' e
  | .one, _ => True.intro
  | .loop _ _ _, h => Nat.le_trans h hL
  | .add e f, h => ⟨within_mono hL e h.1, within_mono hL f h.2⟩
  | .mul e f, h => ⟨within_mono hL e h.1, within_mono hL f h.2⟩
  | .smul _ e, h => within_mono hL e h

theorem within_mapOffsets {width L L' : Nat} (f : Nat → Nat)
    (hf : ∀ offset, offset ≤ L → f offset ≤ L') :
    ∀ e : WindowExpression width, Within L e → Within L' (mapOffsets f e)
  | .one, _ => True.intro
  | .loop offset _ _, h => hf offset h
  | .add e g, h => ⟨within_mapOffsets f hf e h.1, within_mapOffsets f hf g h.2⟩
  | .mul e g, h => ⟨within_mapOffsets f hf e h.1, within_mapOffsets f hf g h.2⟩
  | .smul _ e, h => within_mapOffsets f hf e h

/-- Truncated subtraction puts every mirrored generator inside the doubled window. -/
theorem mirror_within {width : Nat} (h : Nat) :
    ∀ e : WindowExpression width, Within (2*h) (mirror h e)
  | .one => True.intro
  | .loop offset _ _ => Nat.sub_le (2*h) offset
  | .add e f => ⟨mirror_within h e, mirror_within h f⟩
  | .mul e f => ⟨mirror_within h e, mirror_within h f⟩
  | .smul _ e => mirror_within h e

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

theorem source_supported {width : Nat} (L : Nat) :
    ∀ e : WindowExpression width, Within L e →
      SupportedQuaternionBlocks ((L+1)*(N width)) (sourcePolynomial e)
  | .one, _ => supported_one _
  | .loop offset value spin, h => by
      have hoffset : offset ≤ L := h
      have hle : N width + offset*(N width) ≤ (L+1)*(N width) := by
        have hm := Nat.mul_le_mul_right (N width) hoffset
        rw [Nat.succ_mul]
        omega
      exact support_mono
        (lift_supported (sourceCharacter_supported width value.edges spin) (offset*(N width))) hle
  | .add e f, h => supported_add (source_supported L e h.1) (source_supported L f h.2)
  | .mul e f, h => supported_polyMul (source_supported L e h.1) (source_supported L f h.2)
  | .smul c e, h => supported_smul (source_supported L e h) c

theorem placed_supported {width : Nat} (extent start : Nat) :
    ∀ e : WindowExpression width, SupportedQuaternionBlocks (B extent) (placedPolynomial extent start e)
  | .one => supported_one _
  | .loop offset value spin =>
      character_supported extent (value.edges.map (shiftEntry (start+offset))) spin
  | .add e f => supported_add (placed_supported extent start e) (placed_supported extent start f)
  | .mul e f => supported_polyMul (placed_supported extent start e) (placed_supported extent start f)
  | .smul c e => supported_smul (placed_supported extent start e) c

private theorem scheduled_character_pin {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent)
    (offset : Nat) (hoffset : offset ≤ L) (value : SourceLoop width) (spin : Nat) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding L hw ht).polynomial
        (liftBoundary (offset*(N width)) (sourceCharacter width value.edges spin)))
      (character extent (value.edges.map (shiftEntry (start+offset))) spin) := by
  have hcount : offset+(L-offset) = L := by omega
  have htime : start+offset ≤ extent := by omega
  have hplace :
      (embedding L hw ht).polynomial
          (liftBoundary (offset*(N width)) (sourceCharacter width value.edges spin)) =
        (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw htime).polynomial
          (sourceCharacter width value.edges spin) := by
    have h := middle_polynomial_pin (m := offset) (n := L-offset) hw
      (show start+(offset+(L-offset)) ≤ extent by omega)
      (sourceCharacter width value.edges spin) (sourceCharacter_supported width value.edges spin)
    simpa only [BlockEmbedding.polynomial, BlockEmbedding.exponents,
      BlockEmbedding.index, embedding, hcount] using h
  rw [hplace]
  exact .of_prefix (sourceCharacter_pin hw htime value.edges value.physical spin)

/-- ONE chronological embedding realizes the entire signed multi-time expression. -/
theorem expression_pin {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent) :
    ∀ e : WindowExpression width, Within L e →
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding L hw ht).polynomial (sourcePolynomial e))
      (placedPolynomial extent start e)
  | .one, _ => .of_prefix (embedding L hw ht).polynomial_one_prefix
  | .loop offset value spin, h => scheduled_character_pin hw ht offset h value spin
  | .add e f, h => by
      change PaddedPolynomialCoeffEqv (B extent)
        ((embedding L hw ht).polynomial (polyAdd (sourcePolynomial e) (sourcePolynomial f))) _
      rw [BlockEmbedding.polynomial_add]
      exact (expression_pin hw ht e h.1).add (expression_pin hw ht f h.2)
  | .mul e f, h => by
      change PaddedPolynomialCoeffEqv (B extent)
        ((embedding L hw ht).polynomial (polyMul (sourcePolynomial e) (sourcePolynomial f))) _
      rw [BlockEmbedding.polynomial_mul]
      exact (expression_pin hw ht e h.1).mul (expression_pin hw ht f h.2)
  | .smul c e, h => by
      change PaddedPolynomialCoeffEqv (B extent)
        ((embedding L hw ht).polynomial (polySmul c (sourcePolynomial e))) _
      rw [BlockEmbedding.polynomial_smul]
      exact (expression_pin hw ht e h).smul c

/-- Construct the actual physical Wilson-algebra value from source geometry. -/
def placeExpression {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent) :
    (e : WindowExpression width) → Within L e → BF4ExactSlabSpatialWilsonAlgebra.Expression extent
  | .one, _ => .one
  | .loop offset value spin, h =>
      .loop (start+offset) (placeLoop hw (show start+offset ≤ extent by
        have hoffset : offset ≤ L := h
        omega) value) spin
  | .add e f, h => .add (placeExpression hw ht e h.1) (placeExpression hw ht f h.2)
  | .mul e f, h => .mul (placeExpression hw ht e h.1) (placeExpression hw ht f h.2)
  | .smul c e, h => .smul c (placeExpression hw ht e h)

/-- The physical expression evaluates to the literal placed polynomial, not a surrogate. -/
theorem evaluate_placeExpression {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent) :
    ∀ (e : WindowExpression width) (h : Within L e),
    BF4ExactSlabSpatialWilsonAlgebra.evaluate (placeExpression hw ht e h) =
      placedPolynomial extent start e
  | .one, _ => rfl
  | .loop _ _ _, _ => rfl
  | .add e f, h => by
      change polyAdd
        (BF4ExactSlabSpatialWilsonAlgebra.evaluate (placeExpression hw ht e h.1))
        (BF4ExactSlabSpatialWilsonAlgebra.evaluate (placeExpression hw ht f h.2)) =
        polyAdd (placedPolynomial extent start e) (placedPolynomial extent start f)
      rw [evaluate_placeExpression hw ht e h.1, evaluate_placeExpression hw ht f h.2]
  | .mul e f, h => by
      change polyMul
        (BF4ExactSlabSpatialWilsonAlgebra.evaluate (placeExpression hw ht e h.1))
        (BF4ExactSlabSpatialWilsonAlgebra.evaluate (placeExpression hw ht f h.2)) =
        polyMul (placedPolynomial extent start e) (placedPolynomial extent start f)
      rw [evaluate_placeExpression hw ht e h.1, evaluate_placeExpression hw ht f h.2]
  | .smul c e, h => congrArg (polySmul c) (evaluate_placeExpression hw ht e h)

/-- Common-ledger invariance retains the complete supported spectator. -/
theorem placed_ledger_invariant {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent)
    (e : WindowExpression width) (h : Within L e) (cut : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (B extent) r) :
    quaternionHaar (B extent)
        (polyMul r (applyTemporalTranslationLedger extent cut (placedPolynomial extent start e))) ≈
      quaternionHaar (B extent) (polyMul r (placedPolynomial extent start e)) := by
  have hi := BF4ExactSlabSpatialWilsonAlgebra.evaluate_ledger_invariant cut
    (placeExpression hw ht e h) r hr
  rw [evaluate_placeExpression hw ht e h] at hi
  exact hi

/-- The same placed expression traverses the entire selected original action. -/
theorem original_chain_pairing {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent)
    (e : WindowExpression width) (h : Within L e)
    (w : Q') (K actionWidth actionStart steps : Nat) :
    quaternionHaar (B extent)
        (polyMul (placedPolynomial extent start e)
          (originalChainAction w K extent actionWidth actionStart steps)) ≈
      quaternionHaar (B extent)
        (polyMul (placedPolynomial extent start e)
          (ambientChain w K extent actionWidth actionStart steps)) := by
  have hi := BF4ExactSlabSpatialWilsonAlgebra.original_chain_pairing w K extent
    actionWidth actionStart steps (placeExpression hw ht e h)
  rw [evaluate_placeExpression hw ht e h] at hi
  exact hi

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.WindowExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.Within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.sourcePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.placedPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.mapOffsets
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.mirror
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.within_mono
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.within_mapOffsets
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.mirror_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.source_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.placed_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.expression_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.placeExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.evaluate_placeExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.placed_ledger_invariant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow.original_chain_pairing
