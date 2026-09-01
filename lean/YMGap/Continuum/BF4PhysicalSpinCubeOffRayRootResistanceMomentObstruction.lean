/-
# Cardinality obstruction for the BF4 off-ray resistance moment

The first stationary resistance moment is a sufficient upper bound for every
local off-ray edge congestion, but summing that load over all starting states
can be much stronger than a local congestion estimate.  This module exposes
the exact obstruction.

For every non-vacuum off-ray state, the selected positive path starts with an
edge of joint conductance `K(x,y)`.  The finite-sector row identity and
nonnegativity give `K(x,y) <= pi(x)`.  Hence

    1 <= pi(x) / K(x,y) <= pi(x) * pathResistance(x,0).

Consequently the global first resistance moment is at least the number of
nonzero off-ray states.  Any cutoff-uniform moment bound therefore forces a
cutoff-uniform cardinality bound on that residual carrier.  This does not by
itself prove that the residual cardinality diverges, so it is an obstruction
theorem rather than a no-go theorem.  It shows that the local edge-congestion
target must not be replaced uncritically by a global state sum.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih :=
          listQSum_member_le_nonnegative_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hscaled := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hscaled
        exact Q'.le_trans' _ _ _ ih hmono

private theorem listQSum_filter_le_local {A : Type}
    (value : A → Q') (predicate : A → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      listQSum value (items.filter predicate) ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local value predicate hvalue tail
      cases hhead : predicate head with
      | false =>
          simp only [List.filter, hhead, listQSum]
          have hmono : listQSum value tail ≤
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail) (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter, hhead, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

private theorem ofNat_length_le_listQSum_of_one_le_local {A : Type}
    (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (1 : Q') ≤ value item) →
        Q'.ofNat items.length ≤ listQSum value items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hone => by
      have hhead : (1 : Q') ≤ value head :=
        hone head List.mem_cons_self
      have htail : Q'.ofNat tail.length ≤ listQSum value tail :=
        ofNat_length_le_listQSum_of_one_le_local value tail
          (fun item hitem => hone item (List.mem_cons_of_mem head hitem))
      have hsum : (1 : Q') + Q'.ofNat tail.length ≤
          value head + listQSum value tail :=
        Q'.add_le_add hhead htail
      have hcount : Q'.ofNat (head :: tail).length ≈
          (1 : Q') + Q'.ofNat tail.length := by
        simp only [List.length_cons]
        exact Q'.eqv_trans _ (Q'.ofNat tail.length + 1) _
          (Q'.ofNat_add_eqv tail.length 1)
          (Q'.add_comm_eqv _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcount) hsum

private theorem sourceWeight_mul_resistance_ge_one
    {State : Type} {kernel : State → State → Q'} {support : List State}
    {first last : State}
    (weight : State → Q')
    (hne : first ≠ last)
    (hkernel0 : ∀ source target, (0 : Q') ≤ kernel source target)
    (hrow : listQSum (kernel first) support ≈ weight first)
    (path : PositiveKernelChainIn kernel support first last) :
    (1 : Q') ≤ weight first * PositiveKernelChainIn.resistance path := by
  cases path with
  | refl state => exact False.elim (hne rfl)
  | @step first next last positive next_mem rest =>
      have hedgeLeSum : kernel first next ≤
          listQSum (kernel first) support :=
        listQSum_member_le_nonnegative_local
          (kernel first)
          (hkernel0 first)
          support next_mem
      have hedgeLeWeight : kernel first next ≤ weight first :=
        Q'.le_trans' _ _ _ hedgeLeSum (Q'.le_of_eqv hrow)
      have hrecip0 : (0 : Q') ≤ Q'.recipPos
          (kernel first next) positive :=
        Q'.le_of_lt (Q'.recipPos_pos _ positive)
      have honeLeFirst : (1 : Q') ≤
          weight first * Q'.recipPos (kernel first next) positive := by
        have hscaled := Q'.mul_le_mul_of_nonneg_right
          (kernel first next) (weight first)
          (Q'.recipPos (kernel first next) positive)
          hedgeLeWeight hrecip0
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.eqv_symm (Q'.mul_recipPos_eqv _ positive)))
          hscaled
      have hweight0 : (0 : Q') ≤ weight first :=
        Q'.le_trans' _ _ _ (Q'.le_of_lt positive) hedgeLeWeight
      have hresistanceTail0 : (0 : Q') ≤
          PositiveKernelChainIn.resistance rest :=
        PositiveKernelChainIn.resistance_nonnegative rest
      have hfirstLeResistance :
          Q'.recipPos (kernel first next) positive ≤
            Q'.recipPos (kernel first next) positive +
              PositiveKernelChainIn.resistance rest :=
        Q'.add_le_self_of_nonneg _ _ hresistanceTail0
      have hweighted := Q'.mul_le_mul_of_nonneg_left _ _
        (weight first) hfirstLeResistance hweight0
      exact Q'.le_trans' _ _ _ honeLeFirst hweighted

/-! ## 1. Every non-vacuum state costs at least one unit -/

theorem one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K)
    (hne : state ≠ 0) :
    (1 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
  rw [dif_pos hstate]
  exact sourceWeight_mul_resistance_ge_one
    (centralPhysicalFiniteWeight w hw K 0)
    hne
    (fun source target => by
      unfold centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        hw K 0
        (centralPhysicalFiniteStateAt w hw K 0 source)
        (centralPhysicalFiniteStateAt w hw K 0 target))
    (centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight
      (List.mem_filter.mp hstate).1)
    (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)

/-! ## 2. The global moment dominates residual cardinality -/

def centralLowerExcitedSpinCubeNonzeroOffRayIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralLowerExcitedSpinCubeOffRayIndices w hw K).filter
    (fun state => decide (state ≠ 0))

theorem nonzeroOffRay_cardinality_le_resistanceMoment
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeNonzeroOffRayIndices w hw K).length ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceMoment w hw K := by
  let value :=
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K
  have hcount : Q'.ofNat
        (centralLowerExcitedSpinCubeNonzeroOffRayIndices w hw K).length ≤
      listQSum value
        (centralLowerExcitedSpinCubeNonzeroOffRayIndices w hw K) := by
    apply ofNat_length_le_listQSum_of_one_le_local
    intro state hstate
    have hparts := List.mem_filter.mp hstate
    exact one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w hw K state hparts.1 (of_decide_eq_true hparts.2)
  have hfilter : listQSum value
        (centralLowerExcitedSpinCubeNonzeroOffRayIndices w hw K) ≤
      listQSum value
        (centralLowerExcitedSpinCubeOffRayIndices w hw K) := by
    unfold centralLowerExcitedSpinCubeNonzeroOffRayIndices
    exact listQSum_filter_le_local value _
      (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_nonnegative
        w hw K)
      (centralLowerExcitedSpinCubeOffRayIndices w hw K)
  exact Q'.le_trans' _ _ _ hcount hfilter

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound

/-- Any cofinal bound on the global first resistance moment also bounds the
number of nonzero off-ray states by the same rational constant. -/
theorem nonzeroOffRay_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeNonzeroOffRayIndices
          w (Q'.le_of_lt hw) K).length ≤ family.bound := by
  exact Q'.le_trans' _ _ _
    (nonzeroOffRay_cardinality_le_resistanceMoment
      w (Q'.le_of_lt hw) K)
    (family.moment_le K hK)

end FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound

#print axioms one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
#print axioms nonzeroOffRay_cardinality_le_resistanceMoment
#print axioms
  FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound.nonzeroOffRay_cardinality_le_bound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
