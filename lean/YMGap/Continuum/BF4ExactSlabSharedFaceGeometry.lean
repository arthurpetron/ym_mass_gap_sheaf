/-
# Shared-face deletion for two original physical links

Partition the literal physical face identifiers into faces containing both
selected links and their exact complement. Partition that complement again
into left-only, right-only and neither faces. Every heat factor remains an
original polynomial on the same shared-link carrier, with exact product
identities and proved exclusions of the opposite selected link.

The geometry is valid for any pair of literal links, hence in particular
for two distinct physical links. It is a polynomial factorization, NOT a
factorization of the full Haar integral, a conditional independence theorem
after integrating the remaining links, or a spatial mixing estimate.
-/

import YMGap.Continuum.BF4ExactSlabLinkStarGeometry

namespace YMGap.Continuum.BF4ExactSlabSharedFaceGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Exactly the original physical faces containing both selected links. -/
def sharedIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (fun id =>
    decide (left ∈ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id)))

/-- The entire original action except for the shared faces. -/
def retainedIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (fun id =>
    !(decide (left ∈ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id))))

theorem mem_sharedIds_iff (extent : Nat) (left right : Z4Link) (id : Nat) :
    id ∈ sharedIds extent left right ↔ id ∈ slabPhysicalFaceEdges extent ∧
      left ∈ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id) := by
  simp only [sharedIds, List.mem_filter, decide_eq_true_eq]

theorem mem_retainedIds_iff (extent : Nat) (left right : Z4Link) (id : Nat) :
    id ∈ retainedIds extent left right ↔ id ∈ slabPhysicalFaceEdges extent ∧
      ¬ (left ∈ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id)) := by
  simp only [retainedIds, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]

theorem sharedIds_physical {extent : Nat} {left right : Z4Link} {id : Nat}
    (hi : id ∈ sharedIds extent left right) : id ∈ slabPhysicalFaceEdges extent :=
  ((mem_sharedIds_iff extent left right id).mp hi).1

theorem retainedIds_physical {extent : Nat} {left right : Z4Link} {id : Nat}
    (hi : id ∈ retainedIds extent left right) : id ∈ slabPhysicalFaceEdges extent :=
  ((mem_retainedIds_iff extent left right id).mp hi).1

theorem shared_retained_partition (extent : Nat) (left right : Z4Link) :
    (sharedIds extent left right ++ retainedIds extent left right).Perm (slabPhysicalFaceEdges extent) :=
  List.filter_append_perm _ _

theorem retained_face_not_both {extent : Nat} {left right : Z4Link} {id : Nat}
    (hi : id ∈ retainedIds extent left right) :
    ¬ (left ∈ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id)) :=
  ((mem_retainedIds_iff extent left right id).mp hi).2

/-- Shared faces form a subset of the actual at-most-six left-link star. -/
theorem sharedIds_length_le_six (extent : Nat) (left right : Z4Link) :
    (sharedIds extent left right).length ≤ 6 := by
  have hn : (sharedIds extent left right).Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup _)
  have hs := CayleyPruferInjection.nodup_subset_length_le
    (sharedIds extent left right) (incidentIds extent left) hn (by
      intro id hi
      have h := (mem_sharedIds_iff extent left right id).mp hi
      exact (mem_incidentIds_iff extent left id).mpr ⟨h.1, h.2.1⟩)
  exact Nat.le_trans hs (incidentIds_length_le_six extent left)

def sharedHeat (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (sharedIds extent left right)

def retainedHeat (w : Q') (K extent : Nat) (left right : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (retainedIds extent left right)

theorem sharedHeat_supported (w : Q') (K extent : Nat) (left right : Z4Link) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (sharedHeat w K extent left right) :=
  heatProduct_supported w K extent _

theorem retainedHeat_supported (w : Q') (K extent : Nat) (left right : Z4Link) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (retainedHeat w K extent left right) :=
  heatProduct_supported w K extent _

/-- No nonshared factor or other shared link is discarded in this identity. -/
theorem heatProduct_shared_partition (w : Q') (K extent : Nat) (left right : Z4Link) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
      (polyMul (sharedHeat w K extent left right) (retainedHeat w K extent left right)) :=
  (polynomialProduct_perm _ (shared_retained_partition extent left right).symm).trans
    (polynomialProduct_append _ _ _)

def leftOnlyIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (retainedIds extent left right).filter (fun id => decide (left ∈ edgesOf (slabPlaquetteAt extent id)))

private def leftAbsentIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (retainedIds extent left right).filter (fun id => !(decide (left ∈ edgesOf (slabPlaquetteAt extent id))))

def rightOnlyIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (leftAbsentIds extent left right).filter (fun id => decide (right ∈ edgesOf (slabPlaquetteAt extent id)))

def neitherIds (extent : Nat) (left right : Z4Link) : List Nat :=
  (leftAbsentIds extent left right).filter (fun id => !(decide (right ∈ edgesOf (slabPlaquetteAt extent id))))

theorem mem_leftOnlyIds_iff (extent : Nat) (left right : Z4Link) (id : Nat) :
    id ∈ leftOnlyIds extent left right ↔
      id ∈ retainedIds extent left right ∧ left ∈ edgesOf (slabPlaquetteAt extent id) := by
  simp only [leftOnlyIds, List.mem_filter, decide_eq_true_eq]

theorem mem_rightOnlyIds_iff (extent : Nat) (left right : Z4Link) (id : Nat) :
    id ∈ rightOnlyIds extent left right ↔ id ∈ retainedIds extent left right ∧
      left ∉ edgesOf (slabPlaquetteAt extent id) ∧ right ∈ edgesOf (slabPlaquetteAt extent id) := by
  simp only [rightOnlyIds, leftAbsentIds, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, and_assoc]

theorem mem_neitherIds_iff (extent : Nat) (left right : Z4Link) (id : Nat) :
    id ∈ neitherIds extent left right ↔ id ∈ retainedIds extent left right ∧
      left ∉ edgesOf (slabPlaquetteAt extent id) ∧ right ∉ edgesOf (slabPlaquetteAt extent id) := by
  simp only [neitherIds, leftAbsentIds, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, and_assoc]

theorem retained_partition (extent : Nat) (left right : Z4Link) :
    (leftOnlyIds extent left right ++ (rightOnlyIds extent left right ++ neitherIds extent left right)).Perm
      (retainedIds extent left right) := by
  have hr : (rightOnlyIds extent left right ++ neitherIds extent left right).Perm
      (leftAbsentIds extent left right) := List.filter_append_perm _ _
  have hl : (leftOnlyIds extent left right ++ leftAbsentIds extent left right).Perm
      (retainedIds extent left right) := List.filter_append_perm _ _
  exact (hr.append_left (leftOnlyIds extent left right)).trans hl

/-- The shared-deleted action has three exact original-factor groups.
These may still share every link other than the two selected ones. -/
theorem retainedHeat_partition (w : Q') (K extent : Nat) (left right : Z4Link) :
    RatPolyCoeffEqv (retainedHeat w K extent left right)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (leftOnlyIds extent left right))
        (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (rightOnlyIds extent left right))
          (polynomialProduct (faceHeatPolynomial w K extent) (neitherIds extent left right)))) :=
  (polynomialProduct_perm _ (retained_partition extent left right).symm).trans
    ((polynomialProduct_append _ _ _).trans ((polynomialProduct_append _ _ _).mul_left _))

private theorem link_not_mem_faceLinks {extent : Nat} {ids : List Nat} (link : Z4Link)
    (h : ∀ id, id ∈ ids → link ∉ edgesOf (slabPlaquetteAt extent id)) : link ∉ faceLinks extent ids := by
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  exact h id hi he

theorem right_not_mem_leftOnly (extent : Nat) (left right : Z4Link) :
    right ∉ faceLinks extent (leftOnlyIds extent left right) := by
  apply link_not_mem_faceLinks
  intro id hi hr
  have h := (mem_leftOnlyIds_iff extent left right id).mp hi
  exact retained_face_not_both h.1 ⟨h.2, hr⟩

theorem left_not_mem_rightOnly (extent : Nat) (left right : Z4Link) :
    left ∉ faceLinks extent (rightOnlyIds extent left right) := by
  apply link_not_mem_faceLinks
  intro id hi
  exact ((mem_rightOnlyIds_iff extent left right id).mp hi).2.1

theorem links_not_mem_neither (extent : Nat) (left right : Z4Link) :
    left ∉ faceLinks extent (neitherIds extent left right) ∧
      right ∉ faceLinks extent (neitherIds extent left right) := by
  constructor
  · exact link_not_mem_faceLinks left (fun id hi => ((mem_neitherIds_iff extent left right id).mp hi).2.1)
  · exact link_not_mem_faceLinks right (fun id hi => ((mem_neitherIds_iff extent left right id).mp hi).2.2)

private theorem local_excluding {extent : Nat} {links : List Z4Link} {p : RatPoly}
    (hlocal : LinkLocal extent links p) (excluded : Z4Link) (hn : excluded ∉ links) :
    LinkLocal extent (links.filter (fun link => decide (link ≠ excluded))) p :=
  hlocal.mono (fun link hi => List.mem_filter.mpr ⟨hi, by
    apply decide_eq_true
    intro he
    subst link
    exact hn hi⟩)

theorem leftOnly_heat_local (w : Q') (K extent : Nat) (left right : Z4Link) :
    LinkLocal extent ((faceLinks extent (leftOnlyIds extent left right)).filter (fun link => decide (link ≠ right)))
      (polynomialProduct (faceHeatPolynomial w K extent) (leftOnlyIds extent left right)) :=
  local_excluding (heatProduct_local w K extent _) right (right_not_mem_leftOnly extent left right)

theorem rightOnly_heat_local (w : Q') (K extent : Nat) (left right : Z4Link) :
    LinkLocal extent ((faceLinks extent (rightOnlyIds extent left right)).filter (fun link => decide (link ≠ left)))
      (polynomialProduct (faceHeatPolynomial w K extent) (rightOnlyIds extent left right)) :=
  local_excluding (heatProduct_local w K extent _) left (left_not_mem_rightOnly extent left right)

theorem neither_heat_local (w : Q') (K extent : Nat) (left right : Z4Link) :
    LinkLocal extent ((faceLinks extent (neitherIds extent left right)).filter
      (fun link => decide (link ≠ left ∧ link ≠ right)))
      (polynomialProduct (faceHeatPolynomial w K extent) (neitherIds extent left right)) := by
  apply (heatProduct_local w K extent (neitherIds extent left right)).mono
  intro link hi
  refine List.mem_filter.mpr ⟨hi, ?_⟩
  apply decide_eq_true
  constructor
  · intro he
    subst link
    exact (links_not_mem_neither extent left right).1 hi
  · intro he
    subst link
    exact (links_not_mem_neither extent left right).2 hi

end YMGap.Continuum.BF4ExactSlabSharedFaceGeometry

#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.sharedIds
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retainedIds
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.mem_sharedIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.mem_retainedIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.sharedIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retainedIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.shared_retained_partition
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retained_face_not_both
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.sharedIds_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.sharedHeat
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retainedHeat
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.sharedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retainedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.heatProduct_shared_partition
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.leftOnlyIds
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.rightOnlyIds
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.neitherIds
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.mem_leftOnlyIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.mem_rightOnlyIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.mem_neitherIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retained_partition
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.retainedHeat_partition
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.right_not_mem_leftOnly
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.left_not_mem_rightOnly
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.links_not_mem_neither
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.leftOnly_heat_local
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.rightOnly_heat_local
#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceGeometry.neither_heat_local
