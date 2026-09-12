/-
# Exact cutoff removal for the full interface at every odd extent

For a fixed supported polynomial insertion, ALL original crossing-face
heat factors vary together with the cutoff. Above the explicit interface
degree bound, every extra label term is exactly zero; retained heat
coefficients are literally unchanged. The pairing therefore stabilizes,
and its CReal limit is a computed rational with an exact modulus.

Scope: the original interface against a FIXED insertion, at each finite
odd extent and arbitrary rational heat parameter. This is not a modulus
uniform in slab size, a common larger-slab GNS carrier, physical time,
stationary vacuum, strict gap, or thermodynamic/continuum passage.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection

namespace YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection
open YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem weighted_fold {A : Type} (weight : A → Q') (factor : A → RatPoly) :
    ∀ xs : List A,
    RatPolyCoeffEqv
      (polynomialProduct (fun a => polySmul (weight a) (factor a)) xs)
      (polySmul (xs.foldr (fun a r => weight a * r) 1) (polynomialProduct factor xs))
  | [] => (RatPolyCoeffEqv.one_smul polyOne).symm
  | _ :: xs =>
    ((weighted_fold weight factor xs).mul_left _).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

/-- Every original heat coefficient is retained, including its parameter. -/
def interfaceWeight (w : Q') (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  (centralFixedFaceIds half).foldr (fun id r => coeffAt (heatKernelPacket K w) (boundary id) * r) 1

theorem interfaceLabel_eq_weightedCharacters (w : Q') (K half : Nat) (boundary : EdgeLabelling) :
    RatPolyCoeffEqv (interfaceLabelPolynomial w K half boundary)
      (polySmul (interfaceWeight w K half boundary) (interfaceCharacters half boundary)) := by
  have h := weighted_fold (fun id => coeffAt (heatKernelPacket K w) (boundary id))
    (fun id => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half)
      (slabPlaquetteAt (centralExtent half) id)).scalar (boundary id)) (centralFixedFaceIds half)
  have he := polynomialProduct_congr
    (fun id => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half)
      (slabPlaquetteAt (centralExtent half) id)).scalar (boundary id))
    (fun id => correctedSlabPlaquetteSpinFactor (centralExtent half) boundary
      (slabPlaquetteAt (centralExtent half) id)) (centralFixedFaceIds half) (fun id hi => by
        dsimp only [correctedSlabPlaquetteSpinFactor]
        rw [idxOf_slabPlaquetteAt (mem_centralFixedFaceIds.mp hi).1])
  rw [he] at h
  have hm : interfaceCharacters half boundary =
      polynomialProduct (fun id => correctedSlabPlaquetteSpinFactor (centralExtent half) boundary
        (slabPlaquetteAt (centralExtent half) id)) (centralFixedFaceIds half) := by
    unfold interfaceCharacters faceProduct fixedFaces polynomialProduct
    rw [List.foldr_map]
  rw [hm]
  exact h

theorem interfaceLabel_insert_weightedHaar (w : Q') (K half : Nat) (boundary : EdgeLabelling) (p : RatPoly) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceLabelPolynomial w K half boundary)) ≈
    interfaceWeight w K half boundary * quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceCharacters half boundary)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    (((interfaceLabel_eq_weightedCharacters w K half boundary).mul_left p).trans
      (RatPolyCoeffEqv.polyMul_smul_right _ _ _))) (quaternionHaar_polySmul _ _ _)

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

theorem interfaceLabel_insert_zero (w : Q') (K half : Nat) (boundary : EdgeLabelling) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hout : labelWithinB (interfaceBound half p) (centralFixedFaceIds half) boundary = false) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceLabelPolynomial w K half boundary)) ≈ 0 := by
  obtain ⟨id, hi, hs⟩ := above_of_not_within _ boundary _ hout
  exact Q'.eqv_trans _ _ _ (interfaceLabel_insert_weightedHaar w K half boundary p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (interfaceCharacters_above_bound_zero hi boundary p hp hs)) (Q'.mul_zero_eqv _))

theorem interfaceLabel_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) (boundary : EdgeLabelling)
    (hb : ∀ id, id ∈ centralFixedFaceIds half → boundary id < anchor + 1) :
    interfaceLabelPolynomial w later half boundary = interfaceLabelPolynomial w anchor half boundary := by
  apply polynomialProduct_congr
  intro id hi
  unfold weightedFacePolynomial
  rw [coeffAt_heatKernelPacket (by have h := hb id hi; omega), coeffAt_heatKernelPacket (hb id hi)]

private theorem mul_sum {A : Type} (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul p (finitePolySum f xs)) (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: xs => (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum p f xs))

private theorem sum_filter {A : Type} (f : A → Q') (test : A → Bool)
    (hz : ∀ a, test a = false → f a ≈ 0) : ∀ xs : List A,
    listQSum f xs ≈ listQSum f (xs.filter test)
  | [] => Q'.eqv_refl _
  | a :: xs => by
    cases ht : test a with
    | false =>
      simp only [List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hz a ht) (sum_filter f test hz xs))
        (Q'.eqv_of_eq (Q'.zero_add' _))
    | true =>
      simp only [List.filter_cons, ht, ↓reduceIte]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_filter f test hz xs)

private theorem sum_congr {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | a :: xs, h => Q'.add_eqv_congr' (h a List.mem_cons_self)
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Pairing with the existing ORIGINAL all-extent interface heat insertion. -/
def interfacePairing (w : Q') (K half : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
    (polyMul p (interfaceHeatInsertion w K half))

theorem interfacePairing_sum (w : Q') (K half : Nat) (p : RatPoly) :
    interfacePairing w K half p ≈ listQSum
      (fun boundary => quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul p (interfaceLabelPolynomial w K half boundary))) (centralBoundaryChannels K half) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (mul_sum p _ _)) (quaternionHaar_finitePolySum _ _ _)

/-- All original crossing heat factors vary together; P alone is fixed. -/
theorem interfacePairing_stable (w : Q') (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hK : interfaceBound half p ≤ K) :
    interfacePairing w K half p ≈ interfacePairing w (interfaceBound half p) half p := by
  have hfilter := sum_filter
    (fun boundary => quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceLabelPolynomial w K half boundary)))
    (labelWithinB (interfaceBound half p) (centralFixedFaceIds half))
    (fun boundary hb => interfaceLabel_insert_zero w K half boundary p hp hb) (centralBoundaryChannels K half)
  rw [centralBoundaryChannels_filter hK half] at hfilter
  refine Q'.eqv_trans _ _ _ (interfacePairing_sum w K half p) ?_
  refine Q'.eqv_trans _ _ _ hfilter ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (interfacePairing_sum w (interfaceBound half p) half p))
  apply sum_congr
  intro boundary hb
  rw [interfaceLabel_cutoff_eq w hK half boundary (boundedEdgeLabellings_sound _ _ boundary hb).1]
  exact Q'.eqv_refl _

/-- The rational value and exact cutoff modulus are computed from the insertion. -/
def interfacePairingLimit (w : Q') (half : Nat) (p : RatPoly) : CReal :=
  CReal.ofQ' (interfacePairing w (interfaceBound half p) half p)

theorem interfacePairingLimit_exact (w : Q') (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hK : interfaceBound half p ≤ K) (precision : Nat) :
    interfacePairing w K half p ≈ (interfacePairingLimit w half p).approx precision :=
  interfacePairing_stable w K half p hp hK

end YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfaceWeight
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfaceLabel_eq_weightedCharacters
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfaceLabel_insert_weightedHaar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfaceLabel_insert_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfaceLabel_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfacePairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfacePairing_sum
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfacePairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfacePairingLimit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit.interfacePairingLimit_exact
