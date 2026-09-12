/-
# The single central-cube inward-mate family does not cover all observables

The all-vector Poincare compiler isolates a cutoff-uniform endpoint-coverage
field for the selected six-face inward-mate paths.  This module proves that
the field is uninhabited for that path family.

The obstruction is the XOR parity of central-cube faces `0` and `39`.
Every selected mate flips both parities, so this observable is constant on
every selected endpoint pair.  It is nevertheless nonconstant on the
positive physical carrier already at cutoff one: the vacuum has value zero,
while the proved transverse single-face state at face `39` has value one.
After exact stationary centering, its selected endpoint energy is therefore
zero while its physical norm is strictly positive.

This result invalidates only the proposed coverage input for one fixed-root
path family.  It does not obstruct an enlarged family of translated/local
moves, and it is not a spectral-gap, continuum, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A simultaneous-flip invariant -/

/-- XOR parity of two selected faces of the central lower cube. -/
def centralCubePairParityCoefficient (state : EdgeLabelling) : Q' :=
  Q'.ofNat ((state 0 % 2 + state 39 % 2) % 2)

private theorem binaryPairParity_eq_of_both_ne
    (leftZero leftThirtyNine rightZero rightThirtyNine : Nat)
    (hleftZero : leftZero < 2)
    (hleftThirtyNine : leftThirtyNine < 2)
    (hrightZero : rightZero < 2)
    (hrightThirtyNine : rightThirtyNine < 2)
    (hzero : leftZero ≠ rightZero)
    (hthirtyNine : leftThirtyNine ≠ rightThirtyNine) :
    (leftZero + leftThirtyNine) % 2 =
      (rightZero + rightThirtyNine) % 2 := by
  omega

/-- The pair-parity observable is unchanged by every selected inward mate. -/
theorem inwardMatePath_pairParityCoefficient_eq
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    centralCubePairParityCoefficient (sourceLower source) =
      centralCubePairParityCoefficient (targetLower source) := by
  have hzeroCube : 0 ∈ centralLowerCubeFaceIds := by decide
  have hthirtyNineCube : 39 ∈ centralLowerCubeFaceIds := by decide
  have hzeroLower : 0 ∈ centralLowerFaceIds 0 :=
    centralLowerCubeFaceIds_subset_lower 0 hzeroCube
  have hthirtyNineLower : 39 ∈ centralLowerFaceIds 0 :=
    centralLowerCubeFaceIds_subset_lower 39 hthirtyNineCube
  have hzeroTarget := targetPhysical_parity_ne source hzeroCube
  have hthirtyNineTarget :=
    targetPhysical_parity_ne source hthirtyNineCube
  have hzero : sourceLower source 0 % 2 ≠ targetLower source 0 % 2 := by
    unfold sourceLower targetLower centralLowerRestriction
    simp only [if_pos hzeroLower]
    exact fun heq => hzeroTarget heq.symm
  have hthirtyNine :
      sourceLower source 39 % 2 ≠ targetLower source 39 % 2 := by
    unfold sourceLower targetLower centralLowerRestriction
    simp only [if_pos hthirtyNineLower]
    exact fun heq => hthirtyNineTarget heq.symm
  unfold centralCubePairParityCoefficient
  rw [binaryPairParity_eq_of_both_ne
    (sourceLower source 0 % 2) (sourceLower source 39 % 2)
    (targetLower source 0 % 2) (targetLower source 39 % 2)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    hzero hthirtyNine]

/-! ## 2. Exact vanishing of the selected endpoint energy -/

private theorem listQSum_eqv_zero_of_all_local
    {A : Type} (value : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> value item ≈ 0) ->
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_all_local value tail
            (fun item hitem => hzero item
              (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem selectedEndpointEnergy_eqv_zero_of_equal_on_endpoints
    (K : Nat) (hK : 1 <= K) (coefficient : EdgeLabelling -> Q')
    (hequal : forall
      source : GlobalCubeInwardMateCertifiedTargetFullSource K hK,
      coefficient (sourceLower source) = coefficient (targetLower source)) :
    globalInwardMateSelectedEndpointObservableEnergy K hK coefficient ≈ 0 := by
  unfold globalInwardMateSelectedEndpointObservableEnergy
  apply listQSum_eqv_zero_of_all_local
  intro source _hsource
  unfold globalInwardMateSelectedEndpointObservableEnergyTerm
    observableSquaredDifference
  rw [hequal source]
  let value := coefficient (targetLower source)
  have hdifference : value + -value ≈ 0 := Q'.add_neg_self_eqv value
  have hsquare : (value + -value) * (value + -value) ≈ 0 :=
    Q'.eqv_trans _ (0 * (value + -value)) _
      (Q'.mul_eqv_congr_right _ _ _ hdifference)
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _
    (globalInwardMateSourceTraffic source * 0) _
    (Q'.mul_eqv_congr_left _ _ _ hsquare)
    (Q'.mul_zero_eqv _)

theorem centralCubePairParityEndpointEnergy_eqv_zero
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateSelectedEndpointObservableEnergy K hK
        centralCubePairParityCoefficient ≈ 0 := by
  exact selectedEndpointEnergy_eqv_zero_of_equal_on_endpoints
    K hK centralCubePairParityCoefficient
    inwardMatePath_pairParityCoefficient_eq

/-! ## 3. Centering preserves the invisible mode -/

def globalInwardMateCenteredPairParity (K : Nat) :
    EdgeLabelling -> Q' :=
  centralPhysicalCenteredObservable anchorCoupling (by decide) K 0
    centralCubePairParityCoefficient

theorem globalInwardMateCenteredPairParity_meanZero (K : Nat) :
    CentralPhysicalMeanZero anchorCoupling (by decide) K 0
      (globalInwardMateCenteredPairParity K) := by
  exact centralPhysicalCenteredObservable_meanZero
    anchorCoupling (by decide) K 0 centralCubePairParityCoefficient

theorem inwardMatePath_centeredPairParity_eq
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateCenteredPairParity K (sourceLower source) =
      globalInwardMateCenteredPairParity K (targetLower source) := by
  unfold globalInwardMateCenteredPairParity
    centralPhysicalCenteredObservable
  rw [inwardMatePath_pairParityCoefficient_eq source]

theorem centeredPairParityEndpointEnergy_eqv_zero
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateSelectedEndpointObservableEnergy K hK
        (globalInwardMateCenteredPairParity K) ≈ 0 := by
  exact selectedEndpointEnergy_eqv_zero_of_equal_on_endpoints
    K hK (globalInwardMateCenteredPairParity K)
    inwardMatePath_centeredPairParity_eq

/-! ## 4. The invisible centered mode has positive physical norm -/

theorem centralCubePairParityCoefficient_vacuum_eq_zero :
    centralCubePairParityCoefficient zeroEdgeLabelling = 0 := by
  rfl

theorem centralCubePairParityCoefficient_transverse_one_eq_one :
    centralCubePairParityCoefficient
        (centralTransverseSpinSingleFaceState 1) = 1 := by
  decide

private theorem eqv_zero_iff_num_zero (x : Q') :
    x ≈ 0 ↔ x.num = 0 := by
  constructor
  · intro h
    have h' : x.num * (1 : Int) = (0 : Int) * (x.den : Int) := h
    simpa only [Int.mul_one, Int.zero_mul] using h'
  · intro h
    unfold Q'.eqv
    change x.num * (1 : Int) = (0 : Int) * (x.den : Int)
    rw [h]
    simp only [Int.zero_mul]

private theorem self_mul_pos_of_not_eqv_zero (x : Q')
    (hx : ¬ x ≈ 0) :
    (0 : Q') < x * x := by
  apply CReal.pos_of_num_pos
  rw [Q'.mul_num_cast]
  have hn : x.num ≠ 0 :=
    fun h => hx ((eqv_zero_iff_num_zero x).mpr h)
  rcases Int.lt_or_gt_of_ne hn with hneg | hpos
  · have hp : 0 < (-x.num) * (-x.num) :=
      Int.mul_pos (Int.neg_pos.mpr hneg) (Int.neg_pos.mpr hneg)
    simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hp
  · exact Int.mul_pos hpos hpos

private theorem listQSum_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall items : List A, (0 : Q') <= listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall (items : List A) {selected : A}, selected ∈ items ->
      value selected <= listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have hmono : listQSum value tail <=
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

private theorem anchorWeightedInner_pos_of_mem_ne_zero
    (observable : EdgeLabelling -> Q') {selected : EdgeLabelling}
    (hselected : selected ∈
      centralPositiveHalfStates anchorCoupling (by decide) 1 0)
    (hselectedValue : ¬ observable selected ≈ 0) :
    (0 : Q') <
      centralPhysicalWeightedInner anchorCoupling (by decide) 1 0
        observable observable := by
  let term : EdgeLabelling -> Q' := fun state =>
    centralPhysicalRowMarginal anchorCoupling (by decide) 1 0 state *
      (observable state * observable state)
  have htermNonnegative : forall state, (0 : Q') <= term state := by
    intro state
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative
        (by decide) 1 0 state)
      (q_mul_self_nonneg (observable state))
  have htermPositive : (0 : Q') < term selected :=
    Q'.mul_pos
      (mem_centralPositiveHalfStates_iff.mp hselected).2
      (self_mul_pos_of_not_eqv_zero
        (observable selected) hselectedValue)
  unfold centralPhysicalWeightedInner
  exact Q'.pos_of_lt_of_le htermPositive
    (listQSum_member_le_nonnegative_local term htermNonnegative
      (centralPositiveHalfStates anchorCoupling (by decide) 1 0) hselected)

theorem centeredPairParity_transverse_eqv_one_add_vacuum :
    globalInwardMateCenteredPairParity 1
        (centralTransverseSpinSingleFaceState 1) ≈
      1 + globalInwardMateCenteredPairParity 1 zeroEdgeLabelling := by
  unfold globalInwardMateCenteredPairParity
    centralPhysicalCenteredObservable
  rw [centralCubePairParityCoefficient_transverse_one_eq_one,
    centralCubePairParityCoefficient_vacuum_eq_zero]
  exact Q'.add_eqv_congr' (Q'.eqv_refl 1)
    (Q'.eqv_symm
      (Q'.eqv_of_eq
        (Q'.zero_add'
          (-centralPhysicalStationaryMean anchorCoupling
            (by decide) 1 0 centralCubePairParityCoefficient))))

theorem globalInwardMateCenteredPairParity_norm_pos :
    (0 : Q') <
      centralPhysicalWeightedInner anchorCoupling (by decide) 1 0
        (globalInwardMateCenteredPairParity 1)
        (globalInwardMateCenteredPairParity 1) := by
  have hvacuum := zeroEdgeLabelling_mem_centralPositiveHalfStates
    (w := anchorCoupling) (by decide) 1 0
  have htransverse :=
    centralTransverseSpinSingleFaceState_mem_centralPositiveHalfStates
      (w := anchorCoupling) (by decide) (K := 1) (spin := 1) (by decide)
  let vacuumValue :=
    globalInwardMateCenteredPairParity 1 zeroEdgeLabelling
  have hdecidable : Decidable (vacuumValue ≈ 0) := by
    unfold Q'.eqv
    infer_instance
  cases hdecidable with
  | isFalse hvacuumNonzero =>
      exact anchorWeightedInner_pos_of_mem_ne_zero
        (globalInwardMateCenteredPairParity 1) hvacuum hvacuumNonzero
  | isTrue hvacuumZero =>
      have htransverseNonzero :
          ¬ globalInwardMateCenteredPairParity 1
              (centralTransverseSpinSingleFaceState 1) ≈ 0 := by
        intro htransverseZero
        have hzeroOne : (0 : Q') ≈ 1 :=
          Q'.eqv_trans _
            (globalInwardMateCenteredPairParity 1
              (centralTransverseSpinSingleFaceState 1)) _
            (Q'.eqv_symm htransverseZero)
            (Q'.eqv_trans _
              (1 + globalInwardMateCenteredPairParity 1 zeroEdgeLabelling) _
              centeredPairParity_transverse_eqv_one_add_vacuum
              (Q'.eqv_trans _ (1 + 0) _
                (Q'.add_eqv_congr' (Q'.eqv_refl 1) hvacuumZero)
                (Q'.eqv_of_eq (Q'.add_zero' 1))))
        exact (by decide : ¬ (0 : Q') ≈ 1) hzeroOne
      exact anchorWeightedInner_pos_of_mem_ne_zero
        (globalInwardMateCenteredPairParity 1) htransverse
        htransverseNonzero

/-! ## 5. Refutation of the fixed-root all-vector coverage field -/

/-- No positive floor can compare the full centered norm with endpoint
oscillation along only the simultaneous six-face central-cube mates. -/
theorem no_globalInwardMateUniformEndpointCoverage :
    GlobalInwardMateUniformEndpointCoverage -> False := by
  intro coverage
  let centered := globalInwardMateCenteredPairParity 1
  let norm := centralPhysicalWeightedInner anchorCoupling (by decide) 1 0
    centered centered
  have hbound := coverage.floor_mul_norm_le_endpoint
    1 (by decide) centered
    (globalInwardMateCenteredPairParity_meanZero 1)
  have hzero := centeredPairParityEndpointEnergy_eqv_zero 1 (by decide)
  have hleZero : coverage.floor * norm <= 0 :=
    Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hzero)
  have hpositive : (0 : Q') < coverage.floor * norm :=
    Q'.mul_pos coverage.floor_positive
      globalInwardMateCenteredPairParity_norm_pos
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      hpositive hleZero)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.inwardMatePath_pairParityCoefficient_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.centeredPairParityEndpointEnergy_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.globalInwardMateCenteredPairParity_norm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.no_globalInwardMateUniformEndpointCoverage
