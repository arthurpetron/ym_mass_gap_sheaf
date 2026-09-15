/-
# Local cutoff saturation inside the ORIGINAL complete physical face list

Keep cutoff B on faces touching the selected exposed link. Every detached
face has its own unrestricted cutoff. The selected face pairing stabilizes
exactly above the computed insertion/collar degree, independently of those
detached cutoffs. The full action is retained and its diagonal is the old
original numerator. No integration-factor independence is asserted.

The threshold still depends on B and the insertion. This does not remove
the touching bulk cutoff, control the thermodynamic OS norm, construct an
unshifted transfer preimage or close time zero, physical mass, or Clay.
-/

import YMGap.Continuum.BF4ExactSlabLocalBulkSelection
import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

namespace YMGap.Continuum.BF4ExactSlabLocalBulkCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def pairing (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat)
    (extent id : Nat) (ambient : List Nat) (p : RatPoly) (K : Nat) : Q' :=
  quaternionHaar (blocks extent) (polyMul (faceHeatPolynomial (w id) K extent id)
    (polyMul p (profileHeat w (localCutoff extent (slabPlaquetteAt extent id) B farCutoff) extent ambient)))

private theorem sum_insert_zero {A : Type} (count : Nat) (f : A → RatPoly) (p : RatPoly) :
    ∀ xs : List A, (∀ a,a ∈ xs → quaternionHaar count (polyMul (f a) p) ≈ 0) →
      quaternionHaar count (polyMul (finitePolySum f xs) p) ≈ 0
  | [], _ => Q'.eqv_refl _
  | a::xs, h => by
      change quaternionHaar count (polyMul (polyAdd (f a) (finitePolySum f xs)) p) ≈ 0
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append count _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h a List.mem_cons_self)
          (sum_insert_zero count f p xs (fun b hb => h b (List.mem_cons_of_mem a hb))))
          (Q'.eqv_of_eq (Q'.zero_add' _)))

theorem tail_zero {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (ambient : List Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (N L : Nat) (hN : localDegree (slabPlaquetteAt_mem hi) w B ambient p ≤ N) :
    quaternionHaar (blocks extent) (polyMul (faceHeatTail (w id) extent id (N+1) L)
      (polyMul p (profileHeat w (localCutoff extent (slabPlaquetteAt extent id) B farCutoff) extent ambient))) ≈ 0 := by
  apply sum_insert_zero
  intro i _
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff_eqv _ (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (local_character_zero (slabPlaquetteAt_mem hi) w B farCutoff ambient p hp (N+1+i) (by omega)))
        (Q'.mul_zero_eqv _)))

theorem pairing_append {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (ambient : List Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (N L : Nat) (hN : localDegree (slabPlaquetteAt_mem hi) w B ambient p ≤ N) :
    pairing w B farCutoff extent id ambient p (N+L) ≈ pairing w B farCutoff extent id ambient p N := by
  unfold pairing
  rw [faceHeatPolynomial_cutoff_append,polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (tail_zero hi w B farCutoff ambient p hp N L hN)) (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- Exact stabilization, for EVERY profile of detached cutoffs. -/
theorem pairing_stable {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (ambient : List Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (N K : Nat) (hN : localDegree (slabPlaquetteAt_mem hi) w B ambient p ≤ N) (hK : N ≤ K) :
    pairing w B farCutoff extent id ambient p K ≈ pairing w B farCutoff extent id ambient p N := by
  have h := pairing_append hi w B farCutoff ambient p hp N (K-N) hN
  rw [Nat.add_sub_of_le hK] at h
  exact h

/-- Literal deletion of just the selected physical heat factor. -/
def otherFaces (extent id : Nat) : List Nat := (slabPhysicalFaceEdges extent).erase id

private theorem erase_perm (id : Nat) : ∀ {ids : List Nat}, id ∈ ids → ids.Perm (id::ids.erase id)
  | [], h => False.elim (List.not_mem_nil h)
  | head::tail, h => by
      by_cases he : head=id
      · subst head
        rw [List.erase_cons_head]
      · rw [List.erase_cons_tail (a := id) (b := head) (by simp [he])]
        have ht := (List.mem_cons.mp h).resolve_left (fun h => he h.symm)
        exact (List.Perm.cons head (erase_perm id ht)).trans (List.Perm.swap id head _)

def fullCutoff (extent id B : Nat) (farCutoff : Nat → Nat) (K j : Nat) : Nat :=
  if j=id then K else localCutoff extent (slabPlaquetteAt extent id) B farCutoff j

def fullPairing (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (extent id : Nat) (p : RatPoly) (K : Nat) : Q' :=
  quaternionHaar (blocks extent) (polyMul p (profileHeat w (fullCutoff extent id B farCutoff K) extent
    (slabPhysicalFaceEdges extent)))

theorem fullPairing_pin {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (p : RatPoly) (K : Nat) :
    fullPairing w B farCutoff extent id p K ≈ pairing w B farCutoff extent id (otherFaces extent id) p K := by
  have hperm := erase_perm id hi
  have hn := (List.nodup_cons.mp (hperm.nodup (CayleyParentInj.range_nodup _))).1
  have hr : profileHeat w (fullCutoff extent id B farCutoff K) extent (otherFaces extent id) =
      profileHeat w (localCutoff extent (slabPlaquetteAt extent id) B farCutoff) extent (otherFaces extent id) := by
    apply polynomialProduct_congr
    intro j hj
    have hne : j ≠ id := fun h => hn (h ▸ hj)
    simp only [fullCutoff,if_neg hne]
  have h := polynomialProduct_perm (fun j => faceHeatPolynomial (w j)
    (fullCutoff extent id B farCutoff K j) extent j) hperm
  change RatPolyCoeffEqv _ (polyMul (faceHeatPolynomial (w id)
    (fullCutoff extent id B farCutoff K id) extent id)
    (profileHeat w (fullCutoff extent id B farCutoff K) extent (otherFaces extent id))) at h
  simp only [fullCutoff] at h
  rw [hr] at h
  exact haar_of_coeff_eqv _ ((h.mul_left p).trans
    ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      (((RatPolyCoeffEqv.mul_comm _ _).mul_right _).trans (RatPolyCoeffEqv.mul_assoc _ _ _))))

/-- At most FIVE other faces touch the exposed link; the selected face is separate. -/
theorem fullNear_length_le {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    (nearIds extent (slabPlaquetteAt extent id) (otherFaces extent id)).length ≤ 5 := by
  let face := slabPlaquetteAt extent id
  have hd : detachedTest extent [faceLinkA face] [] id = false := by
    cases h : detachedTest extent [faceLinkA face] [] id
    · rfl
    · have hh := (disjointTest_iff _ _).mp h
      exact False.elim (hh (faceLinkA face) (by simp [faceLinks])
        (by simp [faceLinks,face,faceLinkA,edgesOf]))
  have hperm := (erase_perm id hi).filter (fun j => !(detachedTest extent [faceLinkA face] [] j))
  have hl := hperm.length_eq
  change (nearIds extent face (slabPhysicalFaceEdges extent)).length =
    (List.filter (fun j => !(detachedTest extent [faceLinkA face] [] j)) (id::otherFaces extent id)).length at hl
  simp only [List.filter,hd,Bool.not_false,List.length_cons] at hl
  have hc := nearIds_length_le extent face (slabPhysicalFaceEdges extent)
    (CayleyParentInj.range_nodup _) (fun _ h => h)
  change _ = (nearIds extent face (otherFaces extent id)).length+1 at hl
  change (nearIds extent face (otherFaces extent id)).length ≤ 5
  omega

/-- Computed on at most five touching faces; no detached cutoff argument. -/
def fullDegree {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (p : RatPoly) : Nat :=
  localDegree (slabPlaquetteAt_mem hi) w B (otherFaces extent id) p

theorem fullPairing_stable {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (w : Nat → Q') (B : Nat) (farCutoff : Nat → Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (K : Nat) (hK : fullDegree hi w B p ≤ K) :
    fullPairing w B farCutoff extent id p K ≈ fullPairing w B farCutoff extent id p (fullDegree hi w B p) :=
  Q'.eqv_trans _ _ _ (fullPairing_pin hi w B farCutoff p K)
    (Q'.eqv_trans _ _ _ (pairing_stable hi w B farCutoff (otherFaces extent id) p hp _ K (Nat.le_refl _) hK)
      (Q'.eqv_symm (fullPairing_pin hi w B farCutoff p _)))

/-- Equal nomes and cutoffs give the PRE-EXISTING full original numerator. -/
theorem fullPairing_diagonal (w : Q') (K extent id : Nat) (p : RatPoly) :
    fullPairing (fun _ => w) K (fun _ => K) extent id p K =
      numerator w (blocks extent) extent (slabPhysicalFaceEdges extent) p K := by
  have h : profileHeat (fun _ => w) (fullCutoff extent id K (fun _ => K) K) extent
      (slabPhysicalFaceEdges extent) = polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent) := by
    apply polynomialProduct_congr
    intro j _
    simp only [fullCutoff,localCutoff,ite_self]
  unfold fullPairing numerator
  rw [h]

end YMGap.Continuum.BF4ExactSlabLocalBulkCutoff

#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.pairing
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.tail_zero
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.pairing_append
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.pairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.otherFaces
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullCutoff
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullPairing
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullPairing_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullNear_length_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullDegree
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullPairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabLocalBulkCutoff.fullPairing_diagonal
