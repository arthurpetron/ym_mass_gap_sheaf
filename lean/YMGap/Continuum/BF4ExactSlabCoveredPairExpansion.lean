/-
# Covered-pair expansion with the ORIGINAL full-slab weighted integrands

Each selected coefficient expands into two bounded spin labellings.
Their union covers the selection and both vanish outside it. The latter
fact restores every omitted face as its exact spin-zero unit, pinning
the selected products to the original full physical slab integrands.
No sign, small-nome estimate, or independent-variable premise is used.
-/

import YMGap.Continuum.PairedPositiveFacePolynomialExpansion
import YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabCoveredPairExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.PairedPositiveFacePolynomialExpansion
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct (labelProduct)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem faceHeatTerm_zero (w : Q') (extent id : Nat) :
    RatPolyCoeffEqv (faceHeatTerm w extent id 0) polyOne :=
  RatPolyCoeffEqv.one_smul polyOne

theorem connectedCoefficient_labels (w : Q') (K extent : Nat) (p q : RatPoly)
    (ids : List Nat) (hn : ids.Nodup) :
    connectedCoefficient w K extent p q ids ≈
      listQSum (fun pair => (connected (boundaryCompleteSlabLinks extent).length p q).value
        (labelProduct (faceHeatTerm w extent) pair.1 ids)
        (labelProduct (faceHeatTerm w extent) pair.2 ids)) (labels K ids) := by
  have ht : (fun id => faceHeatTail w extent id 1 K) =
      (fun id => finitePolySum (fun n => faceHeatTerm w extent id (n+1)) (List.range K)) := by
    funext id
    simp only [faceHeatTail, Nat.add_comm 1]
  have hp := connectedCoefficient_pair_pin w K extent p q ids
  rw [ht] at hp
  exact Q'.eqv_trans _ _ _ hp (pairedCoefficient_labels _ K (faceHeatTerm w extent)
    (faceHeatTerm_zero w extent) ids hn)

private theorem product_coeff_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → RatPolyCoeffEqv (f id) (g id)) →
      RatPolyCoeffEqv (polynomialProduct f ids) (polynomialProduct g ids)
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, h => (h id List.mem_cons_self).mul
      (product_coeff_congr f g ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

private theorem product_filter_unit (f : Nat → RatPoly) (keep : Nat → Bool) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → keep id = false → RatPolyCoeffEqv (f id) polyOne) →
      RatPolyCoeffEqv (polynomialProduct f ids) (polynomialProduct f (ids.filter keep))
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, h => by
    have ih := product_filter_unit f keep ids (fun j hj => h j (List.mem_cons_of_mem id hj))
    cases he : keep id with
    | false =>
      rw [List.filter_cons, he]
      exact ((h id List.mem_cons_self he).mul ih).trans (RatPolyCoeffEqv.one_mul _)
    | true =>
      rw [List.filter_cons, he]
      exact ih.mul_left (f id)

private theorem labelProduct_eq_product (g : Nat → Nat → RatPoly) (state : EdgeLabelling) :
    ∀ ids : List Nat, labelProduct g state ids = polynomialProduct (fun id => g id (state id)) ids
  | [] => rfl
  | id::ids => congrArg (polyMul (g id (state id))) (labelProduct_eq_product g state ids)

/-- Full original action, with all nonselected labels explicitly zero. -/
theorem labelProduct_original (w : Q') (K extent : Nat) (state : EdgeLabelling)
    (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, state id ≤ K) (ho : ∀ id, id ∉ ids → state id = 0) :
    RatPolyCoeffEqv (labelProduct (faceHeatTerm w extent) state ids) (weightedIntegrand w K extent state) := by
  let f := fun id => faceHeatTerm w extent id (state id)
  let keep := fun id => decide (id ∈ ids)
  have hw : RatPolyCoeffEqv (weightedIntegrand w K extent state)
      (polynomialProduct f (slabPhysicalFaceEdges extent)) :=
    (weighted_integrand_eq_product w K extent state).trans
      (product_coeff_congr _ _ _ (fun id _ => by
        unfold weightedFacePolynomial
        rw [coeffAt_heatKernelPacket (Nat.lt_succ_of_le (hb id))]
        exact RatPolyCoeffEqv.refl _))
  have hf := product_filter_unit f keep (slabPhysicalFaceEdges extent) (fun id _ hk => by
    have hnid : id ∉ ids := by simpa only [keep, decide_eq_false_iff_not] using hk
    dsimp only [f]
    rw [ho id hnid]
    exact faceHeatTerm_zero w extent id)
  have hp : ((slabPhysicalFaceEdges extent).filter keep).Perm ids :=
    perm_of_nodup_mem_iff _ _ ((CayleyParentInj.range_nodup _).filter keep) hn (fun id => by
      simp only [List.mem_filter, keep, decide_eq_true_eq]
      exact ⟨fun h => h.2,fun h => ⟨hi id h,h⟩⟩)
  rw [labelProduct_eq_product]
  exact (hw.trans (hf.trans (polynomialProduct_perm f hp))).symm

/-- The exact coefficient uses the original heat weights and signed Haar networks. -/
theorem connectedCoefficient_original (w : Q') (K extent : Nat) (p q : RatPoly)
    (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    connectedCoefficient w K extent p q ids ≈
      listQSum (fun pair => (connected (boundaryCompleteSlabLinks extent).length p q).value
        (weightedIntegrand w K extent pair.1) (weightedIntegrand w K extent pair.2)) (labels K ids) :=
  Q'.eqv_trans _ _ _ (connectedCoefficient_labels w K extent p q ids hn)
    (listQSum_congr_on _ _ _ (fun pair hm => (connected _ p q).congr
      (labelProduct_original w K extent pair.1 ids hn hi
        (fun id => (bounded K ids pair hm id).1) (fun id h => (outside K ids pair hm id h).1))
      (labelProduct_original w K extent pair.2 ids hn hi
        (fun id => (bounded K ids pair hm id).2) (fun id h => (outside K ids pair hm id h).2))))

end YMGap.Continuum.BF4ExactSlabCoveredPairExpansion

#print axioms YMGap.Continuum.BF4ExactSlabCoveredPairExpansion.faceHeatTerm_zero
#print axioms YMGap.Continuum.BF4ExactSlabCoveredPairExpansion.connectedCoefficient_labels
#print axioms YMGap.Continuum.BF4ExactSlabCoveredPairExpansion.labelProduct_original
#print axioms YMGap.Continuum.BF4ExactSlabCoveredPairExpansion.connectedCoefficient_original
