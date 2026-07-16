/-
# Exact partition-ratio decomposition for the canonical cutoff-one gas

The cross-volume specification identifies the smaller partition with an
embedded subensemble of the larger gas.  This module splits both a target
event numerator and the target partition into embedded and genuinely new
parts, then proves the division-free cross-difference identity governing the
difference of their normalized ratios.

No smallness claim is made here: the remaining analytic task is precisely to
show that the two boundary terms cancel except for clusters joining the event
support to the finite-volume boundary.
-/

import YMGap.Continuum.Z4CanonicalPolymerSpecification

namespace YMGap.Continuum.Z4CanonicalPolymerPartitionRatio

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Complementary positive finite sums -/

def embeddedFamilyB (n m : Nat) (family : List (List Nat)) : Bool :=
  decide (family ∈ embeddedCompatibleFamilies n m)

def boundaryTargetFamilies (n m : Nat) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies m).filter
    (fun family => !(embeddedFamilyB n m family))

def boundaryAnchorPartition (n m : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    (boundaryTargetFamilies n m)

/-- The part of a target event numerator carried by embedded families.  The
event filter is applied first so that the complementary split is literal. -/
def embeddedTargetEventNumerator (n m : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    (((canonicalCompatibleAmbientFamilies m).filter event).filter
      (embeddedFamilyB n m))

def boundaryTargetEventNumerator (n m : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    (((canonicalCompatibleAmbientFamilies m).filter event).filter
      (fun family => !(embeddedFamilyB n m family)))

private theorem listQSum_filter_partition {A : Type}
    (weight : A → Q') (test : A → Bool) :
    ∀ xs : List A,
      listQSum weight xs ≈
        listQSum weight (xs.filter test) +
          listQSum weight (xs.filter (fun item => !(test item)))
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail => by
      have ih := listQSum_filter_partition weight test tail
      cases hhead : test head with
      | false =>
          simp only [listQSum, List.filter_cons, hhead,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv (weight head)
                (listQSum weight (tail.filter test)))) ?_
          exact Q'.add_assoc_eqv _ _ _
      | true =>
          simp only [listQSum, List.filter_cons, hhead, ↓reduceIte,
            Bool.not_true, Bool.false_eq_true]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight head) _ _ ih) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

theorem boundaryAnchorPartition_nonnegative (n m : Nat) :
    (0 : Q') ≤ boundaryAnchorPartition n m := by
  unfold boundaryAnchorPartition
  exact listQSum_nonnegative _
    (canonicalSurfaceFamilyActivity_nonnegative m) _

theorem embeddedTargetEventNumerator_nonnegative
    (n m : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤ embeddedTargetEventNumerator n m event := by
  unfold embeddedTargetEventNumerator
  exact listQSum_nonnegative _
    (canonicalSurfaceFamilyActivity_nonnegative m) _

theorem boundaryTargetEventNumerator_nonnegative
    (n m : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤ boundaryTargetEventNumerator n m event := by
  unfold boundaryTargetEventNumerator
  exact listQSum_nonnegative _
    (canonicalSurfaceFamilyActivity_nonnegative m) _

/-- Membership in the residual list carries an actual exiting polymer and
plaquette, not merely failure of an abstract image predicate. -/
theorem boundaryTargetFamily_has_outside_witness
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ boundaryTargetFamilies n m) :
    ∃ support, support ∈ family ∧
      ∃ plaquette, plaquette ∈ geometricPolymer m support ∧
        plaquette ∉ boxPlaquettes n := by
  have hparts := List.mem_filter.mp hfamily
  have hnot : family ∉ embeddedCompatibleFamilies n m := by
    unfold embeddedFamilyB at hparts
    simpa using hparts.2
  exact family_not_mem_embedded_has_outside_witness
    hnm hparts.1 hnot

/-! ## 2. Exact numerator and denominator decompositions -/

theorem anchorEventNumerator_eqv_embedded_add_boundary
    (n m : Nat) (event : List (List Nat) → Bool) :
    anchorEventNumerator m event ≈
      embeddedTargetEventNumerator n m event +
        boundaryTargetEventNumerator n m event := by
  unfold anchorEventNumerator embeddedTargetEventNumerator
    boundaryTargetEventNumerator embeddedFamilyB
  exact listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (fun family => decide (family ∈ embeddedCompatibleFamilies n m))
    ((canonicalCompatibleAmbientFamilies m).filter event)

theorem anchorCanonicalPartition_eqv_embedded_add_boundary
    {n m : Nat} (hnm : n ≤ m) :
    anchorCanonicalPartition m ≈
      embeddedAnchorPartition n m + boundaryAnchorPartition n m := by
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
    boundaryAnchorPartition boundaryTargetFamilies embeddedFamilyB
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (fun family => decide (family ∈ embeddedCompatibleFamilies n m))
    (canonicalCompatibleAmbientFamilies m)
  have hembedded := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedCompatibleFamilies_perm_target hnm)
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr'
      (Q'.eqv_symm hembedded) (Q'.eqv_refl _))

/-! ## 3. The division-free partition-ratio bridge -/

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Pure rational cancellation behind the ratio comparison:
`(Ni+Nb)Zi - Ni(Zi+Zb) = Nb Zi - Ni Zb`. -/
theorem crossDifference_split (Ni Nb Zi Zb : Q') :
    (Ni + Nb) * Zi - Ni * (Zi + Zb) ≈
      Nb * Zi - Ni * Zb := by
  let A := Ni * Zi
  let B := Nb * Zi
  let C := Ni * Zb
  change ((Ni + Nb) * Zi + -(Ni * (Zi + Zb))).eqv (B + -C)
  refine Q'.eqv_trans _ ((A + B) + -(A + C)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_mul_eqv Ni Nb Zi)
      (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv Ni Zi Zb))
  refine Q'.eqv_trans _ ((A + B) + ((-A) + (-C))) _
    (Q'.add_eqv_congr_left (A + B) _ _
      (Q'.neg_add_eqv A C)) ?_
  refine Q'.eqv_trans _ ((A + (-A)) + (B + (-C))) _
    (Q'.add_regroup A B (-A) (-C)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + (B + (-C))) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv A)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (B + -C))

/-- Exact numerator of the difference between the full target event ratio and
its embedded-subensemble ratio.  The common embedded contribution cancels;
what remains is the covariance-shaped boundary cross term. -/
theorem normalizedEventCrossDifference_eqv_boundary
    {n m : Nat} (hnm : n ≤ m)
    (event : List (List Nat) → Bool) :
    anchorEventNumerator m event * embeddedAnchorPartition n m -
        embeddedTargetEventNumerator n m event *
          anchorCanonicalPartition m ≈
      boundaryTargetEventNumerator n m event *
          embeddedAnchorPartition n m -
        embeddedTargetEventNumerator n m event *
          boundaryAnchorPartition n m := by
  have hnum := anchorEventNumerator_eqv_embedded_add_boundary
    n m event
  have hden := anchorCanonicalPartition_eqv_embedded_add_boundary hnm
  refine Q'.eqv_trans _
    ((embeddedTargetEventNumerator n m event +
          boundaryTargetEventNumerator n m event) *
        embeddedAnchorPartition n m -
      embeddedTargetEventNumerator n m event *
        (embeddedAnchorPartition n m + boundaryAnchorPartition n m)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (qmul_congr hnum (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _
        (qmul_congr (Q'.eqv_refl _ ) hden))
  · exact crossDifference_split
      (embeddedTargetEventNumerator n m event)
      (boundaryTargetEventNumerator n m event)
      (embeddedAnchorPartition n m)
      (boundaryAnchorPartition n m)

end YMGap.Continuum.Z4CanonicalPolymerPartitionRatio

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerPartitionRatio.anchorEventNumerator_eqv_embedded_add_boundary
#print axioms YMGap.Continuum.Z4CanonicalPolymerPartitionRatio.anchorCanonicalPartition_eqv_embedded_add_boundary
#print axioms YMGap.Continuum.Z4CanonicalPolymerPartitionRatio.boundaryTargetFamily_has_outside_witness
#print axioms YMGap.Continuum.Z4CanonicalPolymerPartitionRatio.crossDifference_split
#print axioms YMGap.Continuum.Z4CanonicalPolymerPartitionRatio.normalizedEventCrossDifference_eqv_boundary
