/-
# Finite-volume strictness from the exact vacuum summand

The arbitrary-coupling paired-support reduction bounds the signed face
covariance by one positive-face marginal.  On every finite corrected slab,
the Boolean complement of that marginal contains the all-zero physical
labelling, whose exact weight is one.  Consequently

  positive-face probability + 1 / physicalPartition <= 1.

This gives a literal strict rational covariance rate at every finite cutoff
and volume, together with the explicit vacuum margin `1 / Z` responsible for
strictness.  The margin depends on the complete finite partition and is not
asserted uniform in cutoff, volume, coupling, or lattice spacing.  Thus the
result diagnoses rather than conceals the remaining uniformity obstruction.

Constructive contract: finite Boolean partition, the exact vacuum summand,
positive rational division, and the previously verified arbitrary-coupling
SU(2) switch only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
import YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration

namespace YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_nonnegative_local {A : Type}
    (value : A -> Q') (hvalue : ∀ x, (0 : Q') <= value x) :
    ∀ xs : List A, (0 : Q') <= listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_local {A : Type}
    (value : A -> Q') (hvalue : ∀ x, (0 : Q') <= value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs ->
      value x <= listQSum value xs
  | [], _, h => absurd h List.not_mem_nil
  | head :: tail, x, h => by
      rcases List.mem_cons.mp h with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail <=
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

private theorem le_sub_of_add_le_local {left margin upper : Q'}
    (h : left + margin <= upper) :
    left <= upper + (-margin) := by
  have hshift := Q'.add_le_add_right
    (left + margin) upper (-margin) h
  have hcollapse : (left + margin) + (-margin) ≈ left := by
    refine Q'.eqv_trans _ (left + (margin + (-margin))) _
      (Q'.add_assoc_eqv left margin (-margin)) ?_
    refine Q'.eqv_trans _ (left + 0) _
      (Q'.add_eqv_congr_left left _ _
        (Q'.add_neg_self_eqv margin)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' left)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hshift

private theorem q_lt_of_lt_of_le_local {a b c : Q'}
    (hab : a < b) (hbc : b <= c) : a < c := by
  have habCross :
      a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have hbcCross :
      b.num * (c.den : Int) <= c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hfirst :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right habCross
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (b.num * (a.den : Int)) * (c.den : Int) <=
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hbcCross
      (by exact_mod_cast Nat.zero_le a.den : (0 : Int) <= (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  have hcombined := Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hcombined
    (by exact_mod_cast Nat.zero_le b.den)

private theorem divPos_lt_one_of_lt_local
    (p q : Q') (hq : (0 : Q') < q) (hpq : p < q) :
    Q'.divPos p q hq < (1 : Q') := by
  unfold Q'.divPos
  have hrecip : (0 : Q') < Q'.recipPos q hq :=
    Q'.recipPos_pos q hq
  have hstep :
      Q'.recipPos q hq * p < Q'.recipPos q hq * q :=
    Q'.mul_lt_mul_of_pos_left hrecip hpq
  have hleft :
      p * Q'.recipPos q hq ≈ Q'.recipPos q hq * p :=
    Q'.mul_comm_eqv p _
  have hright :
      Q'.recipPos q hq * q ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.recipPos q hq) q)
      (Q'.mul_recipPos_eqv q hq)
  exact q_lt_of_lt_of_le_local
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hstep)
    (Q'.le_of_eqv hright)

private theorem lt_add_of_pos_right_local
    (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key :
      (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have efirst :
        a.num * (b.den : Int) * (a.den : Int) =
          a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [efirst]
  rw [hexpand]
  omega

/-! ## 1. The exact finite-volume vacuum margin -/

/-- The complement of the root-positive physical event. -/
def slabPhysicalRootZeroMass
    (D : SlabPhysicalData) (rootFaceId : Nat) : Q' :=
  listQSum D.physicalTerm
    (D.physicalLabellings.filter fun physical =>
      !(slabPhysicalFacePositiveB rootFaceId physical))

/-- The all-zero labelling belongs to every finite physical corrected-slab
carrier and to the complement of every root-positive event. -/
theorem zeroEdgeLabelling_mem_slabPhysicalRootZeroCarrier
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    zeroEdgeLabelling ∈
      D.physicalLabellings.filter (fun physical =>
        !(slabPhysicalFacePositiveB rootFaceId physical)) := by
  apply List.mem_filter.mpr
  constructor
  · unfold SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    apply boundedEdgeLabellings_complete
    · intro _ _
      change 0 < D.cutoff + 1
      omega
    · intro _ _
      rfl
  · rfl

/-- The physical complement mass contains the exact unit-weight vacuum. -/
theorem slabPhysicalRootZeroMass_one_le
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    (1 : Q') <= slabPhysicalRootZeroMass D rootFaceId := by
  have hmember := listQSum_member_le_local D.physicalTerm
    (fun physical =>
      slabParametricKPhysicalTerm_nonnegative
        D.coupling_nonnegative D.cutoff D.extent physical)
    (D.physicalLabellings.filter fun physical =>
      !(slabPhysicalFacePositiveB rootFaceId physical))
    (zeroEdgeLabelling_mem_slabPhysicalRootZeroCarrier
      D rootFaceId)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (slabParametricKPhysicalTerm_zero_eqv_one
          D.coupling D.cutoff D.extent)))
    hmember

/-- The expanded positive-source mass is exactly the positive event mass of
the production physical corrected-slab law. -/
theorem slabObservablePositiveSourceWeight_eqv_physicalEventMass
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservablePositiveSourceWeight D rootFaceId ≈
      finiteWeightedEventMass
        D.physicalLabellings D.physicalTerm
        (slabPhysicalFacePositiveB rootFaceId) := by
  have hevent := slabExpandedPhysicalEventMass_eqv D
    (slabPhysicalFacePositiveB rootFaceId)
  unfold slabObservablePositiveSourceWeight
    slabObservablePositiveExpandedSources
    finiteWeightedEventMass
    slabPhysicalFacePositiveB at *
  exact hevent

/-- Exact Boolean partition of the physical partition into root-positive and
root-zero masses. -/
theorem slabPhysicalPartition_eqv_rootPositive_add_rootZero
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    D.physicalPartition ≈
      finiteWeightedEventMass
          D.physicalLabellings D.physicalTerm
          (slabPhysicalFacePositiveB rootFaceId) +
        slabPhysicalRootZeroMass D rootFaceId := by
  unfold SlabPhysicalData.physicalPartition
    SlabPhysicalData.physicalLabellings
    SlabPhysicalData.physicalTerm
    SlabPhysicalData.faceEdges
    finiteWeightedEventMass
    slabPhysicalRootZeroMass
    SlabPhysicalData.extent
    slabPhysicalFacePositiveB
  exact listQSum_filter_partition
    (slabParametricKPhysicalTerm
      D.coupling D.cutoff (centralExtent D.half))
    (fun physical => decide (0 < physical rootFaceId))
    (boundedEdgeLabellings D.cutoff
      (slabPhysicalFaceEdges (centralExtent D.half)))

/-- The root-positive expanded mass leaves at least the unit vacuum summand
inside the complete finite partition. -/
theorem slabObservablePositiveSourceWeight_add_one_le_partition
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservablePositiveSourceWeight D rootFaceId + 1 <=
      D.physicalPartition := by
  let positivePhysical := finiteWeightedEventMass
    D.physicalLabellings D.physicalTerm
    (slabPhysicalFacePositiveB rootFaceId)
  have hpositive :
      slabObservablePositiveSourceWeight D rootFaceId <= positivePhysical :=
    Q'.le_of_eqv
      (slabObservablePositiveSourceWeight_eqv_physicalEventMass
        D rootFaceId)
  have hzero : (1 : Q') <= slabPhysicalRootZeroMass D rootFaceId :=
    slabPhysicalRootZeroMass_one_le D rootFaceId
  have hsum :
      slabObservablePositiveSourceWeight D rootFaceId + 1 <=
        positivePhysical + slabPhysicalRootZeroMass D rootFaceId :=
    Q'.add_le_add hpositive hzero
  exact Q'.le_trans' _ _ _ hsum
    (Q'.ge_of_eqv
      (slabPhysicalPartition_eqv_rootPositive_add_rootZero
        D rootFaceId))

/-! ## 2. A strict rate with its nonuniformity exposed -/

/-- The literal finite-law root-positive rate.  Its dependence on the full
datum is deliberately visible. -/
def slabObservableFiniteVolumeVacuumRate
    (D : SlabPhysicalData) (rootFaceId : Nat) : Q' :=
  Q'.divPos
    (slabObservablePositiveSourceWeight D rootFaceId)
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- The explicit unit-vacuum margin `1 / Z`.  No lower bound uniform in the
parameters of `D` is claimed. -/
def slabObservableFiniteVolumeVacuumMargin
    (D : SlabPhysicalData) : Q' :=
  Q'.divPos 1 D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

theorem slabObservableFiniteVolumeVacuumMargin_pos
    (D : SlabPhysicalData) :
    (0 : Q') < slabObservableFiniteVolumeVacuumMargin D := by
  unfold slabObservableFiniteVolumeVacuumMargin
  exact Q'.divPos_pos 1 D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (by decide)

/-- The event rate and its explicit vacuum margin fit below one. -/
theorem slabObservableFiniteVolumeVacuumRate_add_margin_le_one
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservableFiniteVolumeVacuumRate D rootFaceId +
        slabObservableFiniteVolumeVacuumMargin D <= 1 := by
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hsource : positive + 1 <= partition :=
    slabObservablePositiveSourceWeight_add_one_le_partition
      D rootFaceId
  have hdiv : Q'.divPos (positive + 1) partition hpartition <= 1 := by
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ hsource
      (Q'.ge_of_eqv (Q'.one_mul_eqv partition))
  have hsum :
      Q'.divPos positive partition hpartition +
          Q'.divPos 1 partition hpartition ≈
        Q'.divPos (positive + 1) partition hpartition := by
    unfold Q'.divPos
    let reciprocal := Q'.recipPos partition hpartition
    exact Q'.eqv_trans _
      (reciprocal * positive + reciprocal * 1) _
      (Q'.add_eqv_congr'
        (Q'.mul_comm_eqv positive reciprocal)
        (Q'.mul_comm_eqv 1 reciprocal))
      (Q'.eqv_trans _ (reciprocal * (positive + 1)) _
        (Q'.eqv_symm
          (Q'.mul_add_eqv reciprocal positive 1))
        (Q'.mul_comm_eqv reciprocal (positive + 1)))
  change Q'.divPos positive partition hpartition +
      Q'.divPos 1 partition hpartition <= 1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) hdiv

/-- The event rate is bounded by `1 - 1/Z`; this records the precise finite
vacuum mechanism and its precise loss of uniformity. -/
theorem slabObservableFiniteVolumeVacuumRate_le_one_sub_margin
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservableFiniteVolumeVacuumRate D rootFaceId <=
      1 + (-slabObservableFiniteVolumeVacuumMargin D) :=
  le_sub_of_add_le_local
    (slabObservableFiniteVolumeVacuumRate_add_margin_le_one
      D rootFaceId)

/-- Every finite corrected slab has a genuinely strict root-positive rate. -/
theorem slabObservableFiniteVolumeVacuumRate_lt_one
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservableFiniteVolumeVacuumRate D rootFaceId < 1 := by
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hsource : positive + 1 <= partition :=
    slabObservablePositiveSourceWeight_add_one_le_partition
      D rootFaceId
  have hpositiveStep : positive < positive + 1 :=
    lt_add_of_pos_right_local positive 1 (by decide)
  have hstrict : positive < partition :=
    q_lt_of_lt_of_le_local hpositiveStep hsource
  change Q'.divPos positive partition hpartition < 1
  exact divPos_lt_one_of_lt_local positive partition
    hpartition hstrict

/-! ## 3. The resulting finite-volume covariance contraction -/

/-- **Finite-volume arbitrary-coupling strict covariance.**  The signed
face covariance is bounded by a literal rational rate strictly below one.
The theorem is finite-law strictness, not a distance-decay, operator-gap, or
parameter-uniform statement. -/
theorem slabObservableFaceBooleanCovariance_le_finiteVolumeVacuumRate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId <=
      slabObservableFiniteVolumeVacuumRate D rootFaceId := by
  exact Q'.le_trans' _ _ _
    (slabObservableFaceBooleanCovariance_le_pairedSupportConnectedMass
      D rootFaceId targetFaceId htarget)
    (slabObservableNormalizedPairedSupportConnectedMass_le_positiveProbability
      D rootFaceId targetFaceId)

#print axioms zeroEdgeLabelling_mem_slabPhysicalRootZeroCarrier
#print axioms slabPhysicalRootZeroMass_one_le
#print axioms slabObservablePositiveSourceWeight_eqv_physicalEventMass
#print axioms slabPhysicalPartition_eqv_rootPositive_add_rootZero
#print axioms slabObservablePositiveSourceWeight_add_one_le_partition
#print axioms slabObservableFiniteVolumeVacuumMargin_pos
#print axioms slabObservableFiniteVolumeVacuumRate_add_margin_le_one
#print axioms slabObservableFiniteVolumeVacuumRate_le_one_sub_margin
#print axioms slabObservableFiniteVolumeVacuumRate_lt_one
#print axioms slabObservableFaceBooleanCovariance_le_finiteVolumeVacuumRate

end YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
