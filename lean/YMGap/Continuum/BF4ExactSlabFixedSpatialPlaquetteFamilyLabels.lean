/-
# Literal adjacent-time labels for a signed spatial plaquette family

The lower copy has coefficient c and the upper copy has coefficient -c.
Resetting only the time coordinate recovers the original spatial face label.
The two lists are disjoint, are duplicate-free when the source list is, and
lie in the original boundary-complete slab under the displayed containment
guards. Their coefficient square sum is exactly twice the source square sum.

These are finite geometric and rational identities. They supply the label
and coefficient pins for the original adjacent-time energy consumer, not a
spectral-gap or continuum statement.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry (shift_injective)
open YMGap.Continuum.CayleyPruferInjection (nodup_map_of_injOn)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append listQSum_map)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_congr_on)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def doubledLabels (n : Nat) (qs : List Z4Plaq) : List Z4Plaq :=
  qs.map (timeShiftPlaquette n) ++ qs.map (timeShiftPlaquette (n+1))

/-- Spatial coordinates and the oriented plane are unchanged. -/
def resetTime (p : Z4Plaq) : Z4Plaq :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, 0), p.2)

def doubledCoeff (n : Nat) (c : Z4Plaq → Q') (p : Z4Plaq) : Q' :=
  if p.1.2.2.2 = n then c (resetTime p)
  else if p.1.2.2.2 = n+1 then -(c (resetTime p)) else 0

private theorem resetTime_shift (n : Nat) (p : Z4Plaq) :
    resetTime (timeShiftPlaquette n p) = resetTime p := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := p
  rfl

private theorem resetTime_spatial {width : Nat} {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) : resetTime p = p := by
  have ht := ((spatialFaces_mem_iff width p).mp hp).2.2.2.1
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := p
  change t = 0 at ht
  subst t
  rfl

private theorem spatial_shift_time {width : Nat} {p : Z4Plaq}
    (n : Nat) (hp : p ∈ spatialFaces width) :
    (timeShiftPlaquette n p).1.2.2.2 = n := by
  have ht := ((spatialFaces_mem_iff width p).mp hp).2.2.2.1
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := p
  change t = 0 at ht
  change t+n = n
  rw [ht, Nat.zero_add]

theorem doubledCoeff_lower {width : Nat} {p : Z4Plaq}
    (n : Nat) (c : Z4Plaq → Q') (hp : p ∈ spatialFaces width) :
    doubledCoeff n c (timeShiftPlaquette n p) = c p := by
  unfold doubledCoeff
  rw [spatial_shift_time n hp, if_pos rfl, resetTime_shift, resetTime_spatial hp]

theorem doubledCoeff_upper {width : Nat} {p : Z4Plaq}
    (n : Nat) (c : Z4Plaq → Q') (hp : p ∈ spatialFaces width) :
    doubledCoeff n c (timeShiftPlaquette (n+1) p) = -(c p) := by
  unfold doubledCoeff
  rw [spatial_shift_time (n+1) hp, if_neg (show n+1 ≠ n by omega), if_pos rfl,
    resetTime_shift, resetTime_spatial hp]

/-- Distinct original times keep the copies disjoint, independently of the
spatial sharing among the source faces. -/
theorem doubledLabels_nodup {width : Nat} (n : Nat) (qs : List Z4Plaq)
    (hn : qs.Nodup) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    (doubledLabels n qs).Nodup := by
  refine List.nodup_append.mpr
    ⟨nodup_map_of_injOn _ _ hn (fun _ _ _ _ h => shift_injective n h),
      nodup_map_of_injOn _ _ hn (fun _ _ _ _ h => shift_injective (n+1) h), ?_⟩
  intro a ha b hb he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  have ht := congrArg (fun f : Z4Plaq => f.1.2.2.2) he
  change (timeShiftPlaquette n p).1.2.2.2 = (timeShiftPlaquette (n+1) q).1.2.2.2 at ht
  rw [spatial_shift_time n (hqs p hp), spatial_shift_time (n+1) (hqs q hq)] at ht
  omega

theorem doubledLabels_physical {width extent n : Nat}
    (hw : width ≤ extent) (ht : n+1 ≤ extent) (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    {p : Z4Plaq} (hp : p ∈ doubledLabels n qs) :
    p ∈ boundaryCompleteSlabPlaquettes extent := by
  rcases List.mem_append.mp hp with hl | hu
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    exact spatialFaces_shift_physical (by omega) (by omega) (hqs q hq)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
    exact spatialFaces_shift_physical (by omega) ht (hqs q hq)

private theorem neg_square (a : Q') : (-a)*(-a) ≈ a*a :=
  poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
    (.mul (.var 0) (.var 0)) (by decide) (fun _ => a)

/-- All multiplicities and signs remain in the two finite sums. Nodup is
needed for the later face-label theorem, but not for this exact square sum. -/
theorem doubled_square_sum {width : Nat} (n : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    listQSum (fun p => doubledCoeff n c p * doubledCoeff n c p) (doubledLabels n qs) ≈
      2 * listQSum (fun p => c p*c p) qs := by
  have hl : listQSum (fun p => doubledCoeff n c p * doubledCoeff n c p)
      (qs.map (timeShiftPlaquette n)) ≈ listQSum (fun p => c p*c p) qs := by
    rw [listQSum_map]
    apply listQSum_congr_on _ _ qs
    intro p hp
    rw [doubledCoeff_lower n c (hqs p hp)]
    exact Q'.eqv_refl _
  have hu : listQSum (fun p => doubledCoeff n c p * doubledCoeff n c p)
      (qs.map (timeShiftPlaquette (n+1))) ≈ listQSum (fun p => c p*c p) qs := by
    rw [listQSum_map]
    apply listQSum_congr_on _ _ qs
    intro p hp
    rw [doubledCoeff_upper n c (hqs p hp)]
    exact neg_square (c p)
  exact Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hl hu)
      (poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
        (by decide) (fun _ => listQSum (fun p => c p*c p) qs)))

#print axioms doubledLabels
#print axioms resetTime
#print axioms doubledCoeff
#print axioms doubledCoeff_lower
#print axioms doubledCoeff_upper
#print axioms doubledLabels_nodup
#print axioms doubledLabels_physical
#print axioms doubled_square_sum

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels
