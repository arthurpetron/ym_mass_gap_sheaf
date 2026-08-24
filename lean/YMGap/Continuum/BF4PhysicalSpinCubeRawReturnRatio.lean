/-
# Raw BF4 row formula for the all-spin vacuum return

The finite spin-cube return probability is defined from the partition-
normalised reflected joint law and its stationary row marginal.  Both carry
the same positive global slab-partition reciprocal.  This module cancels that
factor exactly and identifies the return with the unnormalised vacuum entry
divided by the literal unnormalised row mass over the positive carrier.

The zero boundary channel also supplies a concrete positive physical summand
below the vacuum entry.  Consequently the remaining quantitative frontier is
an upper bound on the whole raw row by a cutoff-uniform multiple of that
explicit selected summand.  No such bound, cofinal return floor, full-sector
gap, thermodynamic limit, continuum theory, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior

namespace YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal unnormalised positive-carrier row -/

/-- The raw reflected-kernel mass of one source, summed over the literal
positive physical carrier. -/
def centralPhysicalPositiveRawRowMass
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (centralPhysicalReflectedKernel w K half source)
    (centralPositiveHalfStates w hw K half)

theorem centralPhysicalPositiveRawRowMass_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (source : EdgeLabelling) :
    (0 : Q') ≤ centralPhysicalPositiveRawRowMass w hw K half source := by
  unfold centralPhysicalPositiveRawRowMass
  apply listQSum_nonnegative_on
  intro target _htarget
  exact
    BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
      hw K half source target

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-- Retention of the source implies strict positivity of its raw row mass. -/
theorem centralPhysicalPositiveRawRowMass_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw K half) :
    (0 : Q') < centralPhysicalPositiveRawRowMass w hw K half source := by
  have hrow : (0 : Q') <
      centralPhysicalRowMarginal w hw K half source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  have hfactor :=
    centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := hw) (K := K) (half := half) (source := source)
      (mem_centralPositiveHalfStates_iff.mp hsource).1
  have hproduct : (0 : Q') <
      centralPhysicalPositiveRawRowMass w hw K half source *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w hw K half := by
    exact Q'.pos_of_lt_of_le hrow
      (Q'.le_of_eqv (by
        simpa only [centralPhysicalPositiveRawRowMass] using hfactor))
  exact q_left_pos_of_mul_pos_local
    (Q'.le_of_lt (Q'.recipPos_pos _ _)) hproduct

/-! ## 2. Exact cancellation of the common partition reciprocal -/

private theorem divPos_eqv_divPos_of_cross_local
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul hq hcancel

/-- Dividing a normalized physical joint entry by its positive row marginal
is exactly division of the corresponding raw entry by the raw row mass. -/
theorem centralNormalizedPhysicalReturn_eqv_rawRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw K half)
    (target : EdgeLabelling) :
    Q'.divPos
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source target)
        (centralPhysicalRowMarginal w hw K half source)
        (mem_centralPositiveHalfStates_iff.mp hsource).2 ≈
      Q'.divPos
        (centralPhysicalReflectedKernel w K half source target)
        (centralPhysicalPositiveRawRowMass w hw K half source)
        (centralPhysicalPositiveRawRowMass_pos hsource) := by
  let reciprocal :=
    centralPhysicalFiniteVacuumSectorPartitionReciprocal w hw K half
  have hentry :
      centralNormalizedPhysicalReflectedKernel
          w hw K half source target ≈
        centralPhysicalReflectedKernel w K half source target * reciprocal := by
    exact Q'.eqv_refl _
  have hrow :=
    centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := hw) (K := K) (half := half) (source := source)
      (mem_centralPositiveHalfStates_iff.mp hsource).1
  apply divPos_eqv_divPos_of_cross_local
  refine Q'.eqv_trans _
    ((centralPhysicalReflectedKernel w K half source target * reciprocal) *
      centralPhysicalPositiveRawRowMass w hw K half source) _
    (Q'.mul_eqv_congr_right _ _ _ hentry) ?_
  refine Q'.eqv_trans _
    (centralPhysicalReflectedKernel w K half source target *
      (reciprocal *
        centralPhysicalPositiveRawRowMass w hw K half source)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (centralPhysicalReflectedKernel w K half source target *
      (centralPhysicalPositiveRawRowMass w hw K half source * reciprocal)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv reciprocal
        (centralPhysicalPositiveRawRowMass w hw K half source))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (by
    simpa only [centralPhysicalPositiveRawRowMass] using hrow))

/-! ## 3. The arbitrary-spin return and its selected positive summand -/

/-- Exact raw-row formula for every admitted excited spin-cube return. -/
theorem centralLowerExcitedSpinCubeVacuumReturnProbability_eqv_rawRatio
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset ≈
      Q'.divPos
        (centralPhysicalReflectedKernel w K 0
          (centralLowerSpinCubeState (offset + 1)) zeroEdgeLabelling)
        (centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeState (offset + 1)))
        (centralPhysicalPositiveRawRowMass_pos
          (centralLowerSpinCubeState_mem_centralPositiveHalfStates
            (w := w) (K := K) (spin := offset + 1) hw (by omega))) := by
  have hraw := centralNormalizedPhysicalReturn_eqv_rawRatio
    (centralLowerSpinCubeState_mem_centralPositiveHalfStates
      (w := w) (K := K) (spin := offset + 1) hw (by omega))
    zeroEdgeLabelling
  simpa only [centralLowerExcitedSpinCubeVacuumReturnProbability,
    centralLowerExcitedSpinCubeIndex, centralPhysicalFiniteKernel,
    centralPhysicalFiniteWeight,
    centralPhysicalFiniteStateAt_spinCubeIndex_eq
      (w := w) (K := K) (spin := offset + 1) hw (by omega),
    centralPhysicalFiniteStateAt_zero_eq_vacuum] using hraw

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem zeroEdgeLabelling_mem_bounded_local (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _id _hid
    change 0 < K + 1
    omega
  · intro _id _hid
    rfl

/-- The zero boundary channel is a concrete lower witness for the raw
spin-cube-to-vacuum kernel entry. -/
theorem centralLowerSpinCubePhysicalTerm_le_rawVacuumKernel
    {w : Q'} (hw : (0 : Q') < w)
    (K spin : Nat) :
    slabParametricKPhysicalTerm w K 1
        (centralLowerSpinCubePhysical spin) ≤
      centralPhysicalReflectedKernel w K 0
        (centralLowerSpinCubeState spin) zeroEdgeLabelling := by
  unfold centralPhysicalReflectedKernel
  have hmember := listQSum_member_le_nonnegative_local
    (fun boundary =>
      slabParametricKPhysicalTerm w K 1
        (assembleReflectedSlabLabelling 0
          (centralLowerSpinCubeState spin) boundary zeroEdgeLabelling))
    (fun boundary =>
      slabParametricKPhysicalTerm_nonnegative
        (Q'.le_of_lt hw) K 1
        (assembleReflectedSlabLabelling 0
          (centralLowerSpinCubeState spin) boundary zeroEdgeLabelling))
    (centralBoundaryChannels K 0)
    (zeroEdgeLabelling_mem_bounded_local K (centralFixedFaceIds 0))
  simpa only [centralLowerSpinCubePhysical] using hmember

/-- The raw vacuum entry is itself a nonnegative member of the literal raw
positive-carrier row. -/
theorem centralLowerSpinCubeRawVacuumKernel_le_rawRowMass
    {w : Q'} (hw : (0 : Q') < w)
    (K spin : Nat) :
    centralPhysicalReflectedKernel w K 0
        (centralLowerSpinCubeState spin) zeroEdgeLabelling ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin) := by
  unfold centralPhysicalPositiveRawRowMass
  exact listQSum_member_le_nonnegative_local
    (centralPhysicalReflectedKernel w K 0
      (centralLowerSpinCubeState spin))
    (fun target =>
      BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin) target)
    (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0)
    (zeroEdgeLabelling_mem_centralPositiveHalfStates
      (Q'.le_of_lt hw) K 0)

/-- The explicit zero-boundary spin-foam summand is a positive lower witness
inside the whole raw spin-cube row. -/
theorem centralLowerSpinCubePhysicalTerm_le_rawRowMass
    {w : Q'} (hw : (0 : Q') < w)
    (K spin : Nat) :
    slabParametricKPhysicalTerm w K 1
        (centralLowerSpinCubePhysical spin) ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin) := by
  exact Q'.le_trans' _ _ _
    (centralLowerSpinCubePhysicalTerm_le_rawVacuumKernel hw K spin)
    (centralLowerSpinCubeRawVacuumKernel_le_rawRowMass hw K spin)

/-- For an admitted spin, the selected zero-boundary term is simultaneously
strictly positive and contained in the whole raw source row. -/
theorem centralLowerSpinCubePhysicalTerm_pos_and_le_rawRowMass
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < slabParametricKPhysicalTerm w K 1
        (centralLowerSpinCubePhysical spin) ∧
      slabParametricKPhysicalTerm w K 1
          (centralLowerSpinCubePhysical spin) ≤
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin) :=
  ⟨centralLowerSpinCubePhysicalTerm_pos hw hspin,
    centralLowerSpinCubePhysicalTerm_le_rawRowMass hw K spin⟩

end YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralPhysicalPositiveRawRowMass_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralPhysicalPositiveRawRowMass_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralNormalizedPhysicalReturn_eqv_rawRatio
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralLowerExcitedSpinCubeVacuumReturnProbability_eqv_rawRatio
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralLowerSpinCubePhysicalTerm_le_rawVacuumKernel
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralLowerSpinCubeRawVacuumKernel_le_rawRowMass
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralLowerSpinCubePhysicalTerm_le_rawRowMass
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio.centralLowerSpinCubePhysicalTerm_pos_and_le_rawRowMass
