/-
# Exact representation expansion of the two-slot selected coefficient

The same inclusion-exclusion coefficient is a sum over two bounded
labellings whose union covers the selected faces. Fresh indices preserve
the already selected tail, so no independent-variable premise is used.
-/

import YMGap.Continuum.PolynomialBiadditivePositiveExpansion
import YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct

namespace YMGap.Continuum.PairedPositiveFacePolynomialExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.PolynomialBiadditivePositiveExpansion
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

theorem labelProduct_update_off (g : Nat → Nat → RatPoly) (state : EdgeLabelling)
    (head spin : Nat) : ∀ ids : List Nat, head ∉ ids →
    labelProduct g (setEdgeLabel state head spin) ids = labelProduct g state ids
  | [], _ => rfl
  | id::ids, hn => by
    have he : id ≠ head := fun h => hn (List.mem_cons.mpr (Or.inl h.symm))
    have ht : head ∉ ids := fun h => hn (List.mem_cons_of_mem id h)
    simp only [labelProduct, setEdgeLabel, if_neg he]
    rw [labelProduct_update_off g state head spin ids ht]

theorem labelProduct_set_head (g : Nat → Nat → RatPoly) (state : EdgeLabelling)
    (head spin : Nat) (ids : List Nat) (hn : head ∉ ids) :
    labelProduct g (setEdgeLabel state head spin) (head::ids) =
      polyMul (g head spin) (labelProduct g state ids) := by
  change polyMul (g head (if head = head then spin else state head))
    (labelProduct g (setEdgeLabel state head spin) ids) = _
  rw [if_pos rfl, labelProduct_update_off g state head spin ids hn]

/-- Exact coefficients, including all signs of the original biadditive form. -/
theorem pairedCoefficient_labels (B : Biadditive) (K : Nat) (g : Nat → Nat → RatPoly)
    (h0 : ∀ id, RatPolyCoeffEqv (g id 0) polyOne) : ∀ ids : List Nat, ids.Nodup →
    pairedCoefficient B (fun id => finitePolySum (fun n => g id (n+1)) (List.range K)) ids ≈
      listQSum (fun pair => B.value (labelProduct g pair.1 ids) (labelProduct g pair.2 ids)) (labels K ids)
  | [], _ => Q'.eqv_of_eq (Q'.add_zero' _).symm
  | head::ids, hn => by
    have hf := (List.nodup_cons.mp hn).1
    let term := fun (spins : Nat × Nat) (pair : EdgeLabelling × EdgeLabelling) =>
      B.value (polyMul (g head spins.1) (labelProduct g pair.1 ids))
        (polyMul (g head spins.2) (labelProduct g pair.2 ids))
    have hi := pairedCoefficient_labels
      (B.increment (finitePolySum (fun n => g head (n+1)) (List.range K))) K g h0 ids (List.nodup_cons.mp hn).2
    have hs : listQSum (fun pair => (B.increment (finitePolySum (fun n => g head (n+1)) (List.range K))).value
        (labelProduct g pair.1 ids) (labelProduct g pair.2 ids)) (labels K ids) ≈
        listQSum (fun pair => listQSum (fun spins => term spins pair) (positivePairs K)) (labels K ids) :=
      listQSum_congr_on _ _ _ (fun pair _ => increment_positive B K (g head) (h0 head) _ _)
    have ht : listQSum (fun pair => B.value (labelProduct g pair.1 (head::ids))
        (labelProduct g pair.2 (head::ids))) (labels K (head::ids)) ≈
        listQSum (fun spins => listQSum (term spins) (labels K ids)) (positivePairs K) := by
      change listQSum _ ((positivePairs K).flatMap
        (fun spins => (labels K ids).map (fun pair => setPair pair head spins))) ≈ _
      refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
      simp only [listQSum_map, setPair, labelProduct_set_head g _ head _ ids hf]
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ hi (Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ (listQSum_swap term (positivePairs K) (labels K ids)) (Q'.eqv_symm ht)))

theorem coefficient_expansion (B : Biadditive) (K : Nat) (f : Nat → RatPoly)
    (g : Nat → Nat → RatPoly) (h0 : ∀ id, RatPolyCoeffEqv (g id 0) polyOne)
    (hf : ∀ id, RatPolyCoeffEqv (f id)
      (polyAdd polyOne (finitePolySum (fun n => g id (n+1)) (List.range K))))
    (ids : List Nat) (hn : ids.Nodup) :
    coefficient (fun ys => B.value (polynomialProduct f ys) (polynomialProduct f ys)) ids ≈
      listQSum (fun pair => B.value (labelProduct g pair.1 ids) (labelProduct g pair.2 ids)) (labels K ids) :=
  Q'.eqv_trans _ _ _ (pairedCoefficient_pin B f _ hf ids) (pairedCoefficient_labels B K g h0 ids hn)

end YMGap.Continuum.PairedPositiveFacePolynomialExpansion

#print axioms YMGap.Continuum.PairedPositiveFacePolynomialExpansion.labelProduct_update_off
#print axioms YMGap.Continuum.PairedPositiveFacePolynomialExpansion.labelProduct_set_head
#print axioms YMGap.Continuum.PairedPositiveFacePolynomialExpansion.pairedCoefficient_labels
#print axioms YMGap.Continuum.PairedPositiveFacePolynomialExpansion.coefficient_expansion
