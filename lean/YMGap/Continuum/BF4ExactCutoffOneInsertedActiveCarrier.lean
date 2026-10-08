/-
# Actual inserted cutoff-one Haar reduction to the existing active carrier

Inner-face insertion charge and closed affine parity produce inner support
of the ORIGINAL action mask.  The action mask itself need not be closed.
Every insertion occurrence, including repetitions, remains in the weighted
polynomial.  The original heat coefficient is never replaced by the weight
of the closed affine mask.  The 84 absent normalized Haar variables are
deleted using the existing checked 116-to-32 permutation and trim theorem.

This is an exact carrier reduction, not a charged contraction evaluation,
cutoff accuracy claim, or scaling/survival theorem.
-/

import YMGap.Continuum.BF4ExactCutoffOneInsertedMask

namespace YMGap.Continuum.BF4ExactCutoffOneInsertedActiveCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneInsertedDegree
open YMGap.Continuum.BF4ExactCutoffOneInsertedMask
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabPlaquettes)

local infix:50 " ≈ " => Q'.eqv

private theorem inner_id_lt {id : Nat}
    (hi : id ∈ activeHypercubeSlabFaceIds) : id < 72 :=
  of_decide_eq_true
    (List.all_eq_true.mp activeHypercubeSlabFaceIds_spec.2.2 id hi)

private theorem inner_id_physical {id : Nat}
    (hi : id ∈ activeHypercubeSlabFaceIds) :
    id ∈ slabPhysicalFaceEdges 1 := by
  unfold slabPhysicalFaceEdges
  rw [correctedSlabPlaquettes_extent_one_length]
  exact List.mem_range.mpr (inner_id_lt hi)

/-- XOR insertion charge has no bit outside the literal inner24, even for
repeated insertion occurrences. -/
theorem inner_insertionMask_bit_zero (id : Nat)
    (hout : id ∉ activeHypercubeSlabFaceIds) :
    ∀ ids : List Nat,
      (∀ item, item ∈ ids → item ∈ activeHypercubeSlabFaceIds) →
      (insertionMask ids).testBit id = false
  | [], _ => by simp only [insertionMask, Nat.zero_testBit]
  | item :: rest, hinner => by
      have hne : item ≠ id := by
        intro heq
        exact hout (heq ▸ hinner item List.mem_cons_self)
      have hb : (Nat.xor (2 ^ item) (insertionMask rest)).testBit id =
          ((2 ^ item).testBit id ^^ (insertionMask rest).testBit id) := by
        change ((2 ^ item) ^^^ insertionMask rest).testBit id = _
        exact Nat.testBit_xor _ _ _
      rw [show insertionMask (item :: rest) =
        Nat.xor (2 ^ item) (insertionMask rest) from rfl, hb,
        Nat.testBit_two_pow_of_ne hne,
        inner_insertionMask_bit_zero id hout rest
          (fun other hother => hinner other (List.mem_cons_of_mem item hother))]
      rfl

/-- Closed affine parity plus inner insertion charge PRODUCES inner support
of the original selected action faces; the action need not be closed. -/
theorem affine_action_inner_support (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hinner : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (haffine : affineMask physical ids ∈ embeddedBinarySurfaceMasks)
    (face : Z4Plaq) (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    physical ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 0 ∨
      (boundaryCompleteSlabPlaquettes 1).idxOf face ∈
        activeHypercubeSlabFaceIds := by
  let id := (boundaryCompleteSlabPlaquettes 1).idxOf face
  cases hi : decide (id ∈ activeHypercubeSlabFaceIds) with
  | true => exact Or.inr (of_decide_eq_true hi)
  | false =>
      have hout : id ∉ activeHypercubeSlabFaceIds := of_decide_eq_false hi
      change affineMask physical ids ∈
        binarySurfaceMasks.map embedBinarySurfaceMask at haffine
      obtain ⟨compact, hcompact, heq⟩ := List.mem_map.mp haffine
      have hsupport := of_decide_eq_true
        (List.all_eq_true.mp
          (List.all_eq_true.mp bf4EmbeddedSurfaceActiveFaceSupportCheck_true
            compact hcompact) face hface)
      have hz : embeddedSurfaceLabelling compact id = 0 := by
        rcases hsupport with hz | hi
        · exact hz
        · exact False.elim (hout hi)
      have hzbit : (embedBinarySurfaceMask compact).testBit id = false := by
        cases hb : (embedBinarySurfaceMask compact).testBit id with
        | false => rfl
        | true =>
            simp only [embeddedSurfaceLabelling, hb, if_true] at hz
            omega
      have hqbit := inner_insertionMask_bit_zero id hout ids hinner
      have hxor : (affineMask physical ids).testBit id =
          ((cutoffOneSlabMask physical).testBit id ^^
            (insertionMask ids).testBit id) := by
        change (cutoffOneSlabMask physical ^^^ insertionMask ids).testBit id = _
        exact Nat.testBit_xor _ _ _
      rw [hqbit, Bool.xor_false, ← heq, hzbit] at hxor
      have hid : id < 72 := by
        have h := List.idxOf_lt_length_of_mem hface
        rw [correctedSlabPlaquettes_extent_one_length] at h
        exact h
      have hnot : physical id ≠ 1 := of_decide_eq_false
        ((cutoffOneSlabMask_testBit physical id hid).symm.trans hxor.symm)
      have hsmall : physical id ≤ 1 := hlabel id
      have hzero : physical id = 0 := by omega
      exact Or.inl hzero

private theorem reindex_mul : ∀ (steps : List (QuaternionBlockInvolution 116))
    (p q : RatPoly),
    applyQuaternionBlockSwapChain steps (polyMul p q) =
      polyMul (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q)
  | [], _, _ => rfl
  | step :: rest, p, q => by
      simp only [applyQuaternionBlockSwapChain]
      rw [reindexQuaternionPolynomial_mul, reindex_mul rest]

private theorem reindex_smul : ∀ (steps : List (QuaternionBlockInvolution 116))
    (c : Q') (p : RatPoly),
    applyQuaternionBlockSwapChain steps (polySmul c p) =
      polySmul c (applyQuaternionBlockSwapChain steps p)
  | [], _, _ => rfl
  | step :: rest, c, p => by
      simp only [applyQuaternionBlockSwapChain]
      rw [reindexQuaternionPolynomial_smul, reindex_smul rest]

private theorem tail_smul {p : RatPoly} (hp : QuaternionTailZeroAfter 32 p)
    (c : Q') : QuaternionTailZeroAfter 32 (polySmul c p) := by
  intro term ht
  unfold polySmul at ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

private theorem unit_tail :
    QuaternionTailZeroAfter 32 (reindexBF4SurfaceActiveCarrier polyOne) := by
  have hi : 0 ∈ activeHypercubeSlabFaceIds := by decide
  have hid := inner_id_physical hi
  have hactive : (boundaryCompleteSlabPlaquettes 1).idxOf
      (slabPlaquetteAt 1 0) ∈ activeHypercubeSlabFaceIds := by
    rw [idxOf_slabPlaquetteAt_one hid]
    exact hi
  exact reindexBF4SurfaceActiveSpinFactor_tailZero
    (slabPlaquetteAt 1 0) (slabPlaquetteAt_mem hid) hactive 0 (by decide)

private theorem action_fold_tail (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1)
    (hselected : ∀ face, face ∈ boundaryCompleteSlabPlaquettes 1 →
      physical ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 0 ∨
        (boundaryCompleteSlabPlaquettes 1).idxOf face ∈ activeHypercubeSlabFaceIds) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces → face ∈ boundaryCompleteSlabPlaquettes 1) →
      QuaternionTailZeroAfter 32 (reindexBF4SurfaceActiveCarrier
        (faces.foldr (fun face total =>
          polyMul (correctedSlabPlaquetteSpinFactor 1 physical face) total) polyOne))
  | [], _ => unit_tail
  | face :: rest, hf => by
      have hface := hf face List.mem_cons_self
      have hfactor : QuaternionTailZeroAfter 32
          (reindexBF4SurfaceActiveCarrier
            (correctedSlabPlaquetteSpinFactor 1 physical face)) := by
        rcases hselected face hface with hz | ha
        · unfold correctedSlabPlaquetteSpinFactor
          rw [hz]
          exact unit_tail
        · exact reindexBF4SurfaceActiveSpinFactor_tailZero face hface ha
            (physical ((boundaryCompleteSlabPlaquettes 1).idxOf face)) (hlabel _)
      simp only [List.foldr]
      unfold reindexBF4SurfaceActiveCarrier
      rw [reindex_mul]
      exact QuaternionTailZeroAfter.polyMul hfactor
        (action_fold_tail physical hlabel hselected rest
          (fun other ho => hf other (List.mem_cons_of_mem face ho)))

private theorem insertion_fold_tail : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds) →
    QuaternionTailZeroAfter 32 (reindexBF4SurfaceActiveCarrier
      (insertedFundamentalProduct (insertedFaces ids)))
  | [], _ => unit_tail
  | id :: rest, hinner => by
      have hi := hinner id List.mem_cons_self
      have hid := inner_id_physical hi
      have ha : (boundaryCompleteSlabPlaquettes 1).idxOf
          (slabPlaquetteAt 1 id) ∈ activeHypercubeSlabFaceIds := by
        rw [idxOf_slabPlaquetteAt_one hid]
        exact hi
      have hf := reindexBF4SurfaceActiveSpinFactor_tailZero
        (slabPlaquetteAt 1 id) (slabPlaquetteAt_mem hid) ha 1 (by decide)
      simp only [insertedFaces, List.map_cons, insertedFundamentalProduct, List.foldr]
      unfold reindexBF4SurfaceActiveCarrier
      rw [reindex_mul]
      exact QuaternionTailZeroAfter.polyMul hf
        (insertion_fold_tail rest
          (fun other ho => hinner other (List.mem_cons_of_mem id ho)))

/-- The actual weighted inserted integrand has zero inactive tail.  Its
support is produced from the affine candidate, not assumed for the output. -/
theorem reindex_insertedIntegrand_tailZero (w : Q') (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hinner : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (haffine : affineMask physical ids ∈ embeddedBinarySurfaceMasks) :
    QuaternionTailZeroAfter 32 (reindexBF4SurfaceActiveCarrier
      (exactCutoffOneInsertedIntegrand w physical (insertedFaces ids))) := by
  have haction := action_fold_tail physical hlabel
    (affine_action_inner_support physical hlabel ids hinner haffine)
    (boundaryCompleteSlabPlaquettes 1) (fun _ hf => hf)
  have hinsert := insertion_fold_tail ids hinner
  unfold exactCutoffOneInsertedIntegrand exactCorrectedSlabWeightedIntegrand
    reindexBF4SurfaceActiveCarrier
  rw [reindex_mul, reindex_smul]
  exact QuaternionTailZeroAfter.polyMul
    (tail_smul haction _) hinsert

/-- Exact H116-to-H32 reduction of the SAME original weighted integrand,
without evaluating its signed charged contraction or changing its weight. -/
theorem exactCutoffOneInsertedHaar_eq_active (w : Q') (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hinner : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (haffine : affineMask physical ids ∈ embeddedBinarySurfaceMasks) :
    quaternionHaar 116
        (exactCutoffOneInsertedIntegrand w physical (insertedFaces ids)) ≈
      quaternionHaar 32 (trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier
          (exactCutoffOneInsertedIntegrand w physical (insertedFaces ids)))) := by
  let p := exactCutoffOneInsertedIntegrand w physical (insertedFaces ids)
  have hr := reindexBF4SurfaceActiveCarrier_haar p
    (exactCutoffOneInsertedIntegrand_supported_116 w physical (insertedFaces ids))
  have ht := quaternionHaar_trim_inactive 32 84
    (reindexBF4SurfaceActiveCarrier p)
    (fun term hterm => by
      simpa only [] using reindexBF4SurfaceActiveCarrier_term_length p term hterm)
    (reindex_insertedIntegrand_tailZero w physical hlabel ids hinner haffine)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hr) ht

#print axioms inner_id_lt
#print axioms inner_id_physical
#print axioms inner_insertionMask_bit_zero
#print axioms affine_action_inner_support
#print axioms reindex_mul
#print axioms reindex_smul
#print axioms tail_smul
#print axioms unit_tail
#print axioms action_fold_tail
#print axioms insertion_fold_tail
#print axioms reindex_insertedIntegrand_tailZero
#print axioms exactCutoffOneInsertedHaar_eq_active

end YMGap.Continuum.BF4ExactCutoffOneInsertedActiveCarrier
