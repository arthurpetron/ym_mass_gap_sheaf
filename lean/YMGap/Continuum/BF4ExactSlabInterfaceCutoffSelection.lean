/-
# Exact finite selection of the entire original slab interface

The maximum of the twenty-four exposed-link degree bounds is explicit
data. Any interface labelling exceeding it contributes zero to the SAME
116-link Haar pairing with the fixed supported insertion. All actual face
heat coefficients are retained as a scalar product, not replaced by ranks.

This file proves the selection rule. The finite enumeration/filter and
cutoff-limit construction are separate consumers of that rule.
-/

import YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection
import YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

namespace YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

/-- A finite maximum, carrying each actual face and its membership proof. -/
def interfaceDegreeBound (p : RatPoly) : Nat :=
  (exactCorrectedSlabFixedFaces.attach.map
    (fun face => selectedFaceDegreeBound face.val face.property p)).foldr Nat.max 0

private theorem mem_le_max : ∀ (xs : List Nat) (n : Nat), n ∈ xs → n ≤ xs.foldr Nat.max 0
  | [], _, h => False.elim (List.not_mem_nil h)
  | a :: xs, n, h => by
    rcases List.mem_cons.mp h with rfl | hn
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (mem_le_max xs n hn) (Nat.le_max_right _ _)

theorem interfaceDegreeBound_spec (p : RatPoly) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    selectedFaceDegreeBound face hface p ≤ interfaceDegreeBound p :=
  mem_le_max _ _ (List.mem_map.mpr ⟨⟨face, hface⟩, List.mem_attach _ _, rfl⟩)

private theorem weighted_fold {A : Type} (weight : A → Q') (factor : A → RatPoly) :
    ∀ xs : List A,
    RatPolyCoeffEqv
      (xs.foldr (fun a p => polyMul (polySmul (weight a) (factor a)) p) polyOne)
      (polySmul (xs.foldr (fun a r => weight a * r) 1)
        (xs.foldr (fun a p => polyMul (factor a) p) polyOne))
  | [] => by
    intro probe
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (ratWeightedSum_smul probe 1 polyOne)
      (Q'.one_mul_eqv _))
  | a :: xs =>
    ((weighted_fold weight factor xs).mul_left _).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

private theorem fold_eq_on {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → f a = g a) →
      xs.foldr (fun a p => polyMul (f a) p) polyOne =
        xs.foldr (fun a p => polyMul (g a) p) polyOne
  | [], _ => rfl
  | a :: xs, h => by
    simp only [List.foldr, h a List.mem_cons_self,
      fold_eq_on f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- Product of the ORIGINAL cutoff heat coefficients on the fixed faces. -/
def interfaceHeatWeight (w : Q') (K : Nat) (boundary : EdgeLabelling) : Q' :=
  (centralFixedFaceIds 0).foldr
    (fun id r => coeffAt (heatKernelPacket K w) (boundary id) * r) 1

theorem interfacePolynomial_eq_weightedInterior (w : Q') (K : Nat) (boundary : EdgeLabelling) :
    RatPolyCoeffEqv (interfacePolynomial w K boundary)
      (polySmul (interfaceHeatWeight w K boundary) (exactCorrectedSlabInteriorInsertion boundary)) := by
  rw [interfacePolynomial_eq_fold]
  have h := weighted_fold (fun id => coeffAt (heatKernelPacket K w) (boundary id))
    (fun id => characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar
      (boundary id)) (centralFixedFaceIds 0)
  have he := fold_eq_on
    (fun id => characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar
      (boundary id))
    (fun id => correctedSlabPlaquetteSpinFactor 1 boundary (slabPlaquetteAt 1 id))
    (centralFixedFaceIds 0) (fun id hid => by
      dsimp only [correctedSlabPlaquetteSpinFactor]
      rw [idxOf_slabPlaquetteAt_one (mem_centralFixedFaceIds.mp hid).1])
  rw [he] at h
  have hm : (exactCorrectedSlabInteriorInsertion boundary) =
      (centralFixedFaceIds 0).foldr (fun id p =>
        polyMul (correctedSlabPlaquetteSpinFactor 1 boundary (slabPlaquetteAt 1 id)) p) polyOne := by
    unfold exactCorrectedSlabInteriorInsertion exactCorrectedSlabFixedFaces
    rw [List.foldr_map]
  rw [← hm] at h
  exact h

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

/-- Separation of weights is coefficientwise and hence valid under P. -/
theorem interfacePolynomial_insert_weightedHaar (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (p : RatPoly) :
    quaternionHaar 116 (polyMul p (interfacePolynomial w K boundary)) ≈
      interfaceHeatWeight w K boundary *
        quaternionHaar 116 (polyMul p (exactCorrectedSlabInteriorInsertion boundary)) := by
  refine Q'.eqv_trans _ _ _ ?_ (quaternionHaar_polySmul 116 _ _)
  rw [haar_weighted, haar_weighted]
  exact (((interfacePolynomial_eq_weightedInterior w K boundary).mul_left p).trans
    (RatPolyCoeffEqv.polyMul_smul_right _ _ _)) (quaternionHaarMono 116)

private theorem above_of_not_within (N : Nat) (boundary : EdgeLabelling) : ∀ ids : List Nat,
    labelWithinB N ids boundary = false → ∃ id, id ∈ ids ∧ N < boundary id
  | [], h => Bool.noConfusion h
  | id :: ids, h => by
    by_cases hi : boundary id < N + 1
    · have ht : labelWithinB N ids boundary = false := by
        simpa only [labelWithinB, decide_eq_true hi, Bool.true_and] using h
      obtain ⟨j, hj, hN⟩ := above_of_not_within N boundary ids ht
      exact ⟨j, List.mem_cons_of_mem id hj, hN⟩
    · exact ⟨id, List.mem_cons_self, by omega⟩

/-- ANY above-bound label makes the entire weighted interface term vanish.
No bounds on its other twenty-three labels are required. -/
theorem interfacePolynomial_insert_zero (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 116 p)
    (hout : labelWithinB (interfaceDegreeBound p) (centralFixedFaceIds 0) boundary = false) :
    quaternionHaar 116 (polyMul p (interfacePolynomial w K boundary)) ≈ 0 := by
  obtain ⟨id, hid, hspin⟩ := above_of_not_within _ boundary _ hout
  have hf : slabPlaquetteAt 1 id ∈ exactCorrectedSlabFixedFaces := List.mem_map.mpr ⟨id, hid, rfl⟩
  have hb := Nat.lt_of_le_of_lt (interfaceDegreeBound_spec p _ hf) hspin
  have hz := interior_insert_haar_zero boundary (slabPlaquetteAt 1 id) hf p hp
    (by rwa [idxOf_slabPlaquetteAt_one (mem_centralFixedFaceIds.mp hid).1])
  exact Q'.eqv_trans _ _ _ (interfacePolynomial_insert_weightedHaar w K boundary p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))

/-- Every retained face has the same actual heat coefficient at later K. -/
theorem interfacePolynomial_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (boundary : EdgeLabelling)
    (hb : ∀ id, id ∈ centralFixedFaceIds 0 → boundary id < anchor + 1) :
    interfacePolynomial w later boundary = interfacePolynomial w anchor boundary := by
  rw [interfacePolynomial_eq_fold, interfacePolynomial_eq_fold]
  exact fold_eq_on _ _ _ (fun id hid => weightedFacePolynomial_cutoff_eq w hcut boundary id (hb id hid))

end YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection

#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfaceDegreeBound
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfaceDegreeBound_spec
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfaceHeatWeight
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfacePolynomial_eq_weightedInterior
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfacePolynomial_insert_weightedHaar
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfacePolynomial_insert_zero
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection.interfacePolynomial_cutoff_eq
