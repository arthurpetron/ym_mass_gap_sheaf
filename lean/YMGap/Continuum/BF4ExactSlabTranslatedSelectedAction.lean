/-
# Exact transport of selected original actions and their normalized states

Translate every selected face and the insertion through the same computed
injective Haar placement. Unused target links integrate to one. The target
law here contains exactly the translated selected action, NOT the full
larger-box action. Finite numerator and partition pins give exact normalized
finiteValue and cutoff-limit identities for every 0<w<1, with the existing
explicit Cauchy data. No spatial-boundary smallness is assumed or proved.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def selectedIds (P : Placement) (ids : List Nat) : List Nat := ids.map P.faceId

theorem selectedIds_physical (P : Placement) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (id : Nat) (hi : id ∈ selectedIds P ids) : id ∈ slabPhysicalFaceEdges P.target := by
  obtain ⟨i, hs, rfl⟩ := List.mem_map.mp hi
  exact P.faceId_physical (hids i hs)

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd (f a) (finitePolySum f xs))) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append
        (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul (f a) (polynomialProduct f xs))) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul
        (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem heatFactor_pin (P : Placement) (w : Q') (K : Nat) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges P.source) :
    QuaternionPrefixPolynomialEqv (blocks P.target)
      (P.embedding.polynomial (faceHeatPolynomial w K P.source id))
      (faceHeatPolynomial w K P.target (P.faceId id)) := by
  apply imageSum P.embedding (localFaceTerm w K P.source id)
    (localFaceTerm w K P.target (P.faceId id)) (List.range (K+1))
  intro spin _
  unfold localFaceTerm
  rw [BlockEmbedding.polynomial_smul, P.faceId_pin hi]
  exact (P.character_pin (slabPlaquetteAt_mem hi) spin).smul _

theorem heatProduct_pin (P : Placement) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source) :
    QuaternionPrefixPolynomialEqv (blocks P.target)
      (P.embedding.polynomial (polynomialProduct (faceHeatPolynomial w K P.source) ids))
      (polynomialProduct (faceHeatPolynomial w K P.target) (selectedIds P ids)) := by
  simpa only [selectedIds, polynomialProduct, List.foldr_map] using
    (imageProduct P.embedding (faceHeatPolynomial w K P.source)
      (fun id => faceHeatPolynomial w K P.target (P.faceId id)) ids
      (fun id hi => heatFactor_pin P w K (hids id hi)))

/-- No whole-target action appears: only the translated selected factors. -/
theorem numerator_pin (P : Placement) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks P.source) p) :
    numerator w (blocks P.target) P.target (selectedIds P ids) (P.embedding.polynomial p) K ≈
      numerator w (blocks P.source) P.source ids p K := by
  have himage : QuaternionPrefixPolynomialEqv (blocks P.target)
      (P.embedding.polynomial (polyMul p (polynomialProduct (faceHeatPolynomial w K P.source) ids)))
      (polyMul (P.embedding.polynomial p)
        (polynomialProduct (faceHeatPolynomial w K P.target) (selectedIds P ids))) := by
    rw [BlockEmbedding.polynomial_mul]
    exact (QuaternionPrefixPolynomialEqv.refl _ _).mul (heatProduct_pin P w K ids hids)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ himage
      (P.embedding.polynomial_supported _)
      (supported_polyMul (P.embedding.polynomial_supported p) (heatProduct_supported w K _ _))))
    (P.haar _ (supported_polyMul hp (heatProduct_supported w K _ _)))

theorem partition_pin (P : Placement) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source) :
    heatProductHaar w (blocks P.target) P.target (selectedIds P ids) K ≈
      heatProductHaar w (blocks P.source) P.source ids K :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _
    (heatProduct_pin P w K ids hids) (P.embedding.polynomial_supported _)
    (heatProduct_supported w K _ _)))
    (P.haar _ (heatProduct_supported w K _ _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

variable (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)

/-- The same cutoff is used on both sides, and the reciprocal follows the
exact transported partition, not its floor estimate. -/
theorem finiteValue_pin (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks P.source) p)
    (stage : Nat) :
    finiteValue w hw0 hw1 P.target (selectedIds P ids) (selectedIds_physical P ids hids)
      (P.embedding.polynomial p) stage ≈ finiteValue w hw0 hw1 P.source ids hids p stage := by
  unfold finiteValue
  apply qmul (numerator_pin P w _ ids hids p hp)
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact Q'.recipPos_eqv_congr _ _ _ _ (partition_pin P w _ ids hids)

theorem expectation_pin (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks P.source) p) :
    Equiv (expectation w hw0 hw1 P.target (selectedIds P ids) (selectedIds_physical P ids hids)
      (P.embedding.polynomial p)) (expectation w hw0 hw1 P.source ids hids p) :=
  Equiv_of_ofQ'_limit_close (finite_converges w hw0 hw1 _ _ _ _)
    (finite_converges w hw0 hw1 _ _ _ _)
    (fun epsilon he => ⟨0, fun stage _ => eqv_close (finiteValue_pin P hw0 hw1 ids hids p hp stage) epsilon he⟩)

theorem finiteValue_pin_of_prefix
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks P.source) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks P.target) q)
    (he : QuaternionPrefixPolynomialEqv (blocks P.target) (P.embedding.polynomial p) q)
    (stage : Nat) :
    finiteValue w hw0 hw1 P.target (selectedIds P ids) (selectedIds_physical P ids hids) q stage ≈
      finiteValue w hw0 hw1 P.source ids hids p stage := by
  have hn : numerator w (blocks P.target) P.target (selectedIds P ids)
      (P.embedding.polynomial p) (headCutoff w+stage) ≈
      numerator w (blocks P.target) P.target (selectedIds P ids) q (headCutoff w+stage) :=
    quaternionHaar_prefixPolynomialEqv _ (he.mul (.refl _ _))
      (supported_polyMul (P.embedding.polynomial_supported p) (heatProduct_supported w _ _ _))
      (supported_polyMul hq (heatProduct_supported w _ _ _))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hn))
    (finiteValue_pin P hw0 hw1 ids hids p hp stage)

/-- Literal translated holonomies may replace the polynomial block map. -/
theorem expectation_pin_of_prefix
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks P.source) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks P.target) q)
    (he : QuaternionPrefixPolynomialEqv (blocks P.target) (P.embedding.polynomial p) q) :
    Equiv (expectation w hw0 hw1 P.target (selectedIds P ids) (selectedIds_physical P ids hids) q)
      (expectation w hw0 hw1 P.source ids hids p) :=
  Equiv_of_ofQ'_limit_close (finite_converges w hw0 hw1 _ _ _ _)
    (finite_converges w hw0 hw1 _ _ _ _)
    (fun epsilon ht => ⟨0, fun stage _ => eqv_close
      (finiteValue_pin_of_prefix P hw0 hw1 ids hids p hp q hq he stage) epsilon ht⟩)

end YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction

#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.selectedIds
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.selectedIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.heatFactor_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.heatProduct_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.numerator_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.partition_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.finiteValue_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.expectation_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.finiteValue_pin_of_prefix
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction.expectation_pin_of_prefix
