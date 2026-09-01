/-
# A selected-term row floor for the growing closed-surface grid

The two disjoint closed surfaces provide more than strict row positivity.
Their literal completed physical labelling is a selected summand of the raw
positive-carrier row, and its face factor is exactly the product of the sixth
powers of the two heat-kernel coefficients.  Since the link multiplicity is
at least one, this gives an explicit quantitative lower witness.

At the anchor coupling this witness can be compared with the existing
spin-cube raw-row ceiling.  The resulting floor is honest but may decay with
the replica spin; no effective-multiplicity divergence, ray-tail limit,
continuum theory, or Clay conclusion is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness
import YMGap.Continuum.PinnedCluster

namespace YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.PinnedCluster

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on_local
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl _
  | id :: rest, hagree =>
      qmul_congr_local
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on_local left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem rearrange_pointwise_products_local
    (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num *
      (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem eliminateLinks_pointwise_mul_local
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      eliminateLinks (fun id => left id * right id) ids ≈
        eliminateLinks left ids * eliminateLinks right ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest => by
      unfold eliminateLinks
      refine Q'.eqv_trans _
        ((left id * right id) *
          (eliminateLinks left rest * eliminateLinks right rest)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_pointwise_mul_local left right rest)
      · exact rearrange_pointwise_products_local
          (left id) (right id)
          (eliminateLinks left rest) (eliminateLinks right rest)

private theorem eliminateLinks_indicator_pow_local
    (selected : List Nat) (coefficient : Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id => if id ∈ selected then coefficient else 1)
          ids ≈
        coefficient ^
          (ids.filter
            (fun id => decide (id ∈ selected))).length
  | [] => Q'.eqv_refl _
  | id :: rest => by
      by_cases hselected : id ∈ selected
      · simp only [eliminateLinks, hselected, if_pos,
          List.filter_cons, decide_true, List.length_cons,
          Q'.pow_succ]
        exact qmul_congr_local (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow_local selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow_local
              selected coefficient rest))
          (Q'.one_mul_eqv _)

/-! ## 1. The selected grid term is inside the literal raw row -/

theorem centralGridPhysicalTerm_le_rawRowMass
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    slabParametricKPhysicalTerm w K 1
        (centralGridPhysical firstSpin secondSpin) ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) K 0
        (centralGridRowState firstSpin secondSpin) := by
  have hkernel :
      slabParametricKPhysicalTerm w K 1
          (centralGridPhysical firstSpin secondSpin) ≤
        centralPhysicalReflectedKernel w K 0
          (centralGridRowState firstSpin secondSpin)
          (centralGridTargetState firstSpin secondSpin) := by
    unfold centralPhysicalReflectedKernel
    have hmember := listQSum_member_le_local
      (fun boundary =>
        slabParametricKPhysicalTerm w K 1
          (assembleReflectedSlabLabelling 0
            (centralGridRowState firstSpin secondSpin) boundary
            (centralGridTargetState firstSpin secondSpin)))
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (Q'.le_of_lt hw) K 1
          (assembleReflectedSlabLabelling 0
            (centralGridRowState firstSpin secondSpin) boundary
            (centralGridTargetState firstSpin secondSpin)))
      (centralBoundaryChannels K 0)
      (centralGridBoundary_mem_channels hfirstSpin hsecondSpin)
    simpa only [centralExtent, Nat.zero_add,
      centralGrid_assemble_restrictions hfirstSpin hsecondSpin] using hmember
  unfold centralPhysicalPositiveRawRowMass
  exact Q'.le_trans' _ _ _ hkernel
    (listQSum_member_le_local
      (centralPhysicalReflectedKernel w K 0
        (centralGridRowState firstSpin secondSpin))
      (fun target =>
        BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K 0
          (centralGridRowState firstSpin secondSpin) target)
      (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0)
      (centralGridTargetState_mem_centralPositiveHalfStates
        hw hfirstSpin hsecondSpin))

/-! ## 2. Exact two-surface face activity -/

/-- The two six-face supports contribute exactly one sixth power of each
heat-kernel coefficient; all other physical faces carry the vacuum weight. -/
theorem centralGridPhysicalFaceFactor_eqv
    (w : Q') {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    slabParametricKPhysicalFaceFactor w K 1
        (centralGridPhysical firstSpin secondSpin) ≈
      (coeffW w firstSpin) ^ 6 * (coeffW w secondSpin) ^ 6 := by
  let firstIndicator := fun id : Nat =>
    if id ∈ centralFirstGridClosedSpinSurface.faceIds
    then coeffW w firstSpin else 1
  let secondIndicator := fun id : Nat =>
    if id ∈ centralSecondGridClosedSpinSurface.faceIds
    then coeffW w secondSpin else 1
  unfold slabParametricKPhysicalFaceFactor
  have hcoeff :
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket K w)
            (centralGridPhysical firstSpin secondSpin id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks (fun id => firstIndicator id * secondIndicator id)
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on_local
    intro id _hid
    by_cases hfirst : id ∈ centralFirstGridClosedSpinSurface.faceIds
    · have hnotSecond :
          id ∉ centralSecondGridClosedSpinSurface.faceIds := by
        intro hsecond
        exact centralDisjointGridSurfaces.supports_disjoint
          id hfirst hsecond
      have hlabel : centralGridPhysical firstSpin secondSpin id = firstSpin :=
        centralDisjointGridSurfaces.spinLabelling_eq_firstSpin hfirst
      rw [hlabel, coeffAt_heatKernelPacket
        (Nat.lt_succ_of_le hfirstSpin)]
      simpa [firstIndicator, secondIndicator, hfirst, hnotSecond] using
        Q'.eqv_symm (Q'.mul_one_eqv (coeffW w firstSpin))
    · by_cases hsecond :
          id ∈ centralSecondGridClosedSpinSurface.faceIds
      · have hlabel :
            centralGridPhysical firstSpin secondSpin id = secondSpin :=
          centralDisjointGridSurfaces.spinLabelling_eq_secondSpin hsecond
        rw [hlabel, coeffAt_heatKernelPacket
          (Nat.lt_succ_of_le hsecondSpin)]
        simpa [firstIndicator, secondIndicator, hfirst, hsecond] using
          Q'.eqv_symm (Q'.one_mul_eqv (coeffW w secondSpin))
      · have hlabel : centralGridPhysical firstSpin secondSpin id = 0 := by
          simp [centralGridPhysical,
            DisjointClosedSpinSurfaces.spinLabelling,
            centralDisjointGridSurfaces, hfirst, hsecond]
        rw [hlabel, coeffAt_heatKernelPacket (Nat.zero_lt_succ K),
          coeffW_zero]
        simpa [firstIndicator, secondIndicator, hfirst, hsecond] using
          Q'.eqv_symm (Q'.one_mul_eqv (1 : Q'))
  have hsplit := eliminateLinks_pointwise_mul_local
    firstIndicator secondIndicator (slabPhysicalFaceEdges 1)
  have hfirstPower := eliminateLinks_indicator_pow_local
    centralFirstGridClosedSpinSurface.faceIds (coeffW w firstSpin)
    (slabPhysicalFaceEdges 1)
  have hsecondPower := eliminateLinks_indicator_pow_local
    centralSecondGridClosedSpinSurface.faceIds (coeffW w secondSpin)
    (slabPhysicalFaceEdges 1)
  have hfirstCount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id => decide
          (id ∈ centralFirstGridClosedSpinSurface.faceIds))).length = 6 := by
    decide
  have hsecondCount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id => decide
          (id ∈ centralSecondGridClosedSpinSurface.faceIds))).length = 6 := by
    decide
  rw [hfirstCount] at hfirstPower
  rw [hsecondCount] at hsecondPower
  exact Q'.eqv_trans _ _ _ hcoeff
    (Q'.eqv_trans _ _ _ hsplit
      (qmul_congr_local hfirstPower hsecondPower))

/-- The full selected grid term dominates its exact face activity because
the constructive link-multiplicity product is a positive natural number. -/
theorem centralGridActivity_le_physicalTerm
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (coeffW w firstSpin) ^ 6 * (coeffW w secondSpin) ^ 6 ≤
      slabParametricKPhysicalTerm w K 1
        (centralGridPhysical firstSpin secondSpin) := by
  let face := slabParametricKPhysicalFaceFactor w K 1
    (centralGridPhysical firstSpin secondSpin)
  let multiplicity := slabExplicitLinkMultiplicityProduct K 1
    (centralGridPhysical firstSpin secondSpin)
  have hfaceEq := centralGridPhysicalFaceFactor_eqv
    w hfirstSpin hsecondSpin
  have hactivity0 :
      (0 : Q') ≤
        (coeffW w firstSpin) ^ 6 * (coeffW w secondSpin) ^ 6 :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg _ (coeffW_nonneg (Q'.le_of_lt hw) firstSpin) 6)
      (Q'.pow_nonneg _ (coeffW_nonneg (Q'.le_of_lt hw) secondSpin) 6)
  have hface0 : (0 : Q') ≤ face :=
    Q'.le_trans' _ _ _ hactivity0 (Q'.ge_of_eqv hfaceEq)
  have hmultiplicityPos : 0 < multiplicity := by
    exact centralDisjointGridSurfaces.linkProduct_pos
      hfirstSpin hsecondSpin
  have honeLeMultiplicity : (1 : Q') ≤ Q'.ofNat multiplicity := by
    change Q'.ofNat 1 ≤ Q'.ofNat multiplicity
    exact Q'.ofNat_le_ofNat (Nat.succ_le_iff.mpr hmultiplicityPos)
  have hfaceLe : face ≤ face * Q'.ofNat multiplicity := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv face)))
      (Q'.mul_le_mul_of_nonneg_left
        1 (Q'.ofNat multiplicity) face honeLeMultiplicity hface0)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hfaceEq) (by
    unfold face multiplicity at hfaceLe
    simpa only [slabParametricKPhysicalTerm] using hfaceLe)

/-- Combining the exact activity factor with literal row membership yields a
fully explicit selected-term lower bound for every admitted grid row. -/
theorem centralGridActivity_le_rawRowMass
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (coeffW w firstSpin) ^ 6 * (coeffW w secondSpin) ^ 6 ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) K 0
        (centralGridRowState firstSpin secondSpin) := by
  exact Q'.le_trans' _ _ _
    (centralGridActivity_le_physicalTerm hw hfirstSpin hsecondSpin)
    (centralGridPhysicalTerm_le_rawRowMass hw hfirstSpin hsecondSpin)

/-! ## 3. Anchor-coupling comparison with the spin-cube row ceiling -/

private theorem qpow_pos_local {value : Q'} (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

private theorem qpow_le_qpow_of_le_local
    {left right : Q'} (hleft0 : (0 : Q') ≤ left)
    (hle : left ≤ right) :
    ∀ exponent : Nat, left ^ exponent ≤ right ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      have hleftPow0 : (0 : Q') ≤ left ^ exponent :=
        Q'.pow_nonneg left hleft0 exponent
      have hright0 : (0 : Q') ≤ right :=
        Q'.le_trans' _ _ _ hleft0 hle
      have hfirst : left * left ^ exponent ≤ right * left ^ exponent :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hle hleftPow0
      have hsecond : right * left ^ exponent ≤ right * right ^ exponent :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (qpow_le_qpow_of_le_local hleft0 hle exponent) hright0
      exact Q'.le_trans' _ _ _ hfirst hsecond

theorem centralSpinCubeResidualCarrierCeiling_pos :
    (0 : Q') < centralSpinCubeResidualCarrierCeiling := by
  unfold centralSpinCubeResidualCarrierCeiling
  exact qpow_pos_local
    (Q'.pos_add_nonneg (by decide)
      anchorDecoratedFaceEnvelope_nonnegative) 66

/-- The selected-term ratio obtained by cancelling the six source-spin face
activities against the existing uniform residual-carrier ceiling. -/
def gridReplicaSelectedFloor (replica : Nat) : Q' :=
  Q'.divPos
    ((coeffW anchorCoupling replica) ^ 6)
    centralSpinCubeResidualCarrierCeiling
    centralSpinCubeResidualCarrierCeiling_pos

theorem gridReplicaSelectedFloor_pos (replica : Nat) :
    (0 : Q') < gridReplicaSelectedFloor replica := by
  unfold gridReplicaSelectedFloor
  exact Q'.divPos_pos _ _ centralSpinCubeResidualCarrierCeiling_pos
    (qpow_pos_local (coeffW_pos (by decide) replica) 6)

/-- For every admitted pair, the selected closed-surface summand gives a
literal row comparison at the replica-dependent floor. -/
theorem centralSpinCubeRawRow_mul_gridReplicaSelectedFloor_le_gridRawRow
    {K firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ K) (hreplica : replica ≤ K) :
    centralPhysicalPositiveRawRowMass
          anchorCoupling (by decide) K 0
          (centralLowerSpinCubeState firstSpin) *
        gridReplicaSelectedFloor replica ≤
      centralPhysicalPositiveRawRowMass
          anchorCoupling (by decide) K 0
          (centralGridRowState firstSpin replica) := by
  let firstActivity := (coeffW anchorCoupling firstSpin) ^ 6
  let replicaActivity := (coeffW anchorCoupling replica) ^ 6
  let ceiling := centralSpinCubeResidualCarrierCeiling
  have hsource :=
    centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling hfirstSpin
  have hfloor0 : (0 : Q') ≤ gridReplicaSelectedFloor replica :=
    Q'.le_of_lt (gridReplicaSelectedFloor_pos replica)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hsource hfloor0
  have hcancel :
      (firstActivity * ceiling) * gridReplicaSelectedFloor replica ≈
        firstActivity * replicaActivity := by
    unfold gridReplicaSelectedFloor ceiling replicaActivity
    refine Q'.eqv_trans _
      (firstActivity *
        (centralSpinCubeResidualCarrierCeiling *
          Q'.divPos ((coeffW anchorCoupling replica) ^ 6)
            centralSpinCubeResidualCarrierCeiling
            centralSpinCubeResidualCarrierCeiling_pos)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (firstActivity *
        (Q'.divPos ((coeffW anchorCoupling replica) ^ 6)
            centralSpinCubeResidualCarrierCeiling
            centralSpinCubeResidualCarrierCeiling_pos *
          centralSpinCubeResidualCarrierCeiling)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.divPos_mul_eqv _ _ centralSpinCubeResidualCarrierCeiling_pos)
  have htarget := centralGridActivity_le_rawRowMass
    (by decide : (0 : Q') < anchorCoupling) hfirstSpin hreplica
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel) (by
      unfold firstActivity replicaActivity
      exact htarget))

private theorem anchorCoeff_succ_le (spin : Nat) :
    coeffW anchorCoupling (spin + 1) ≤ coeffW anchorCoupling spin := by
  cases spin with
  | zero =>
      rw [coeffW_zero]
      decide
  | succ predecessor =>
      exact coeffW_succ_le (by decide) (by decide)
        (predecessor + 1) (by omega)

private theorem anchorCoeff_add_le (spin : Nat) :
    ∀ extra : Nat,
      coeffW anchorCoupling (spin + extra) ≤ coeffW anchorCoupling spin
  | 0 => by
      simpa using Q'.le_refl' (coeffW anchorCoupling spin)
  | extra + 1 => by
      have hstep := anchorCoeff_succ_le (spin + extra)
      have ih := anchorCoeff_add_le spin extra
      rw [Nat.add_assoc] at hstep
      exact Q'.le_trans' _ _ _ hstep ih

theorem gridReplicaSelectedFloor_antitone
    {left right : Nat} (hle : left ≤ right) :
    gridReplicaSelectedFloor right ≤ gridReplicaSelectedFloor left := by
  have hcoeff :
      coeffW anchorCoupling right ≤ coeffW anchorCoupling left := by
    have hadd := anchorCoeff_add_le left (right - left)
    rwa [Nat.add_sub_of_le hle] at hadd
  have hactivity := qpow_le_qpow_of_le_local
    (coeffW_nonneg (by decide) right) hcoeff 6
  unfold gridReplicaSelectedFloor
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hactivity
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv _ _ centralSpinCubeResidualCarrierCeiling_pos))

/-- A capped common floor for every replica at cutoff `K`.  The antitone
coefficient estimate makes the highest admitted replica the selected-term
worst case. -/
def growingGridSelectedCommonFloor (K : Nat) : Q' :=
  Q'.min' 1 (gridReplicaSelectedFloor K)

theorem growingGridSelectedCommonFloor_pos (K : Nat) :
    (0 : Q') < growingGridSelectedCommonFloor K := by
  unfold growingGridSelectedCommonFloor
  exact CReal.min_pos (by decide) (gridReplicaSelectedFloor_pos K)

theorem growingGridSelectedCommonFloor_le_one (K : Nat) :
    growingGridSelectedCommonFloor K ≤ 1 :=
  Q'.min_le_left' _ _

theorem growingGridSelectedCommonFloor_le_computedFloor (K : Nat) :
    growingGridSelectedCommonFloor K ≤
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) K).rawRowRatioFloor := by
  apply growingGrid_lower_le_rawRowRatioFloor_of_scaledRawRow_le
  · exact growingGridSelectedCommonFloor_le_one K
  · intro offset replica hoffset hreplica
    have hsource0 := centralPhysicalPositiveRawRowMass_nonnegative
      (by decide : (0 : Q') ≤ anchorCoupling) K 0
      (centralLowerSpinCubeState (offset + 1))
    have hcommonLeReplica :
        growingGridSelectedCommonFloor K ≤
          gridReplicaSelectedFloor replica :=
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (gridReplicaSelectedFloor_antitone (by omega))
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
      hcommonLeReplica hsource0
    exact Q'.le_trans' _ _ _ hscaled
      (centralSpinCubeRawRow_mul_gridReplicaSelectedFloor_le_gridRawRow
        (by omega) (by omega))

/-- The growing-replica compiler therefore has an entirely explicit
selected-term effective-multiplicity lower bound.  Whether this particular
quantity diverges remains a separate asymptotic question. -/
theorem growingGrid_selectedEffectiveMultiplicityLowerBound (K : Nat) :
    Q'.ofNat (K + 1) * growingGridSelectedCommonFloor K ≤
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) K).toWeighted.effectiveMultiplicity := by
  change Q'.ofNat (K + 1) * growingGridSelectedCommonFloor K ≤
    Q'.ofNat (K + 1) *
      (growingGridPositiveRawReplication
        anchorCoupling (by decide) K).rawRowRatioFloor
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (growingGridSelectedCommonFloor_le_computedFloor K)
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat (K + 1))

end YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor

#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.centralGridPhysicalTerm_le_rawRowMass
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.centralGridPhysicalFaceFactor_eqv
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.centralGridActivity_le_physicalTerm
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.centralGridActivity_le_rawRowMass
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.centralSpinCubeRawRow_mul_gridReplicaSelectedFloor_le_gridRawRow
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.gridReplicaSelectedFloor_antitone
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.growingGridSelectedCommonFloor_le_computedFloor
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor.growingGrid_selectedEffectiveMultiplicityLowerBound
