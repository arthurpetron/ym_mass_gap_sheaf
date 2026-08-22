/-
# Positive-kernel connectivity of every finite BF4 vacuum sector

The canonical vacuum sector was constructed as the connected component of a
Boolean graph obtained by symmetrizing nonzero unnormalized reflected-kernel
entries.  This module closes the semantic gap between that graph and the
actual normalized physical kernel.

On the positive carrier the reflected kernel is nonnegative and symmetric.
Consequently every true support edge is a strictly positive normalized-kernel
edge in the forward orientation.  The existing Type-level graph chains can
therefore be compiled, without choice, into Type-level chains carrying a
strictly positive physical kernel witness at every step.

This proves constructive irreducibility of each finite canonical vacuum
sector.  A quantitative path/Poincare estimate is still required to turn it
into an explicit strict finite form rate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
import YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Type-level chains carrying positive physical edges -/

/-- A finite chain whose every step carries a strictly positive kernel entry.
As with `ChainIn`, the chain is `Type`-level data rather than propositional
reachability. -/
inductive PositiveKernelChainIn {State : Type}
    (kernel : State → State → Q') (support : List State) :
    State → State → Type
  | refl (state : State) :
      PositiveKernelChainIn kernel support state state
  | step {first next last : State}
      (positive : (0 : Q') < kernel first next)
      (next_mem : next ∈ support)
      (rest : PositiveKernelChainIn kernel support next last) :
      PositiveKernelChainIn kernel support first last

namespace PositiveKernelChainIn

def trans {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first middle last : State} →
      PositiveKernelChainIn kernel support first middle →
      PositiveKernelChainIn kernel support middle last →
      PositiveKernelChainIn kernel support first last
  | _, _, _, PositiveKernelChainIn.refl _, right => right
  | _, _, _, PositiveKernelChainIn.step hpositive hmem rest, right =>
      PositiveKernelChainIn.step hpositive hmem (trans rest right)

/-- Compile an ordinary Boolean support chain into a positive-kernel chain
when every in-support true edge has a supplied positivity proof. -/
def ofChainIn {State : Type}
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true →
      (0 : Q') < kernel first next) :
    {first last : State} → first ∈ support →
      ChainIn adjacent support first last →
      PositiveKernelChainIn kernel support first last
  | first, _, _hfirst, ChainIn.refl _ =>
      PositiveKernelChainIn.refl first
  | first, _last, hfirst,
      ChainIn.step (b := next) hnext hnextMem rest =>
      PositiveKernelChainIn.step
        (edgePositive first next hfirst hnextMem hnext)
        hnextMem
        (ofChainIn adjacent kernel support edgePositive hnextMem rest)

end PositiveKernelChainIn

/-! ## 2. A true BF4 support edge is exactly a positive kernel edge -/

private theorem q_pos_of_nonnegative_not_eqv_zero
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hqne : ¬ q ≈ 0) :
    (0 : Q') < q := by
  have hnum0 : (0 : Int) ≤ q.num :=
    (Q'.zero_le_iff_num_nonneg q).mp hq0
  have hnumne : q.num ≠ 0 := by
    intro hnum
    apply hqne
    show q.num * (1 : Int) = (0 : Int) * (q.den : Int)
    simp [hnum]
  show (0 : Int) * (q.den : Int) < q.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

private theorem finiteStateAt_mem_halfStates_of_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteStateAt w hw cutoff half index ∈
      centralHalfStates cutoff half := by
  have hpositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw cutoff half hindex)
  exact (mem_centralPositiveHalfStates_iff.mp hpositive).1

/-- A sector index has a strictly positive stationary weight because the
canonical component lies inside the literal positive-row carrier. -/
theorem centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    (0 : Q') < centralPhysicalFiniteWeight w hw cutoff half index := by
  have hpositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw cutoff half hindex)
  exact (mem_centralPositiveHalfStates_iff.mp hpositive).2

/-- A true symmetrized support edge between sector indices has a positive
unnormalized kernel entry in the requested forward orientation. -/
theorem centralPhysicalFiniteRawKernel_pos_of_supportAdjacent
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hadjacent :
      centralPhysicalFiniteSupportAdjacentB
        w hw cutoff half left right = true) :
    (0 : Q') <
      centralPhysicalFiniteRawKernel w hw cutoff half left right := by
  have hleftHalf := finiteStateAt_mem_halfStates_of_sector hleft
  have hrightHalf := finiteStateAt_mem_halfStates_of_sector hright
  have hraw0 : (0 : Q') ≤
      centralPhysicalFiniteRawKernel w hw cutoff half left right := by
    unfold centralPhysicalFiniteRawKernel
    exact centralPhysicalReflectedKernel_nonnegative
      hw cutoff half _ _
  cases hforward :
      centralPhysicalFiniteKernelNonzeroB
        w hw cutoff half left right with
  | true =>
      have hne : ¬
          centralPhysicalFiniteRawKernel w hw cutoff half left right ≈ 0 := by
        unfold centralPhysicalFiniteKernelNonzeroB at hforward
        simpa only [decide_eq_true_eq] using hforward
      exact q_pos_of_nonnegative_not_eqv_zero hraw0 hne
  | false =>
      have hreverse :
          centralPhysicalFiniteKernelNonzeroB
            w hw cutoff half right left = true := by
        unfold centralPhysicalFiniteSupportAdjacentB at hadjacent
        simpa only [hforward, Bool.false_or] using hadjacent
      have hreverseNe : ¬
          centralPhysicalFiniteRawKernel w hw cutoff half right left ≈ 0 := by
        unfold centralPhysicalFiniteKernelNonzeroB at hreverse
        simpa only [decide_eq_true_eq] using hreverse
      have hsymm :
          centralPhysicalFiniteRawKernel w hw cutoff half left right ≈
            centralPhysicalFiniteRawKernel w hw cutoff half right left := by
        unfold centralPhysicalFiniteRawKernel
        exact centralPhysicalReflectedKernel_symm w hleftHalf hrightHalf
      have hforwardNe : ¬
          centralPhysicalFiniteRawKernel w hw cutoff half left right ≈ 0 := by
        intro hzero
        apply hreverseNe
        exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsymm) hzero
      exact q_pos_of_nonnegative_not_eqv_zero hraw0 hforwardNe

/-- The same support edge is strictly positive in the actual normalized
finite physical kernel. -/
theorem centralPhysicalFiniteKernel_pos_of_supportAdjacent
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hadjacent :
      centralPhysicalFiniteSupportAdjacentB
        w hw cutoff half left right = true) :
    (0 : Q') <
      centralPhysicalFiniteKernel w hw cutoff half left right := by
  unfold centralPhysicalFiniteKernel
    centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralPhysicalFiniteRawKernel_pos_of_supportAdjacent
      hleft hright hadjacent)
    (Q'.recipPos_pos _
      (slabParametricKPhysicalPartition_pos
        hw cutoff (centralExtent half)))

/-- Conversely, a positive normalized entry is detected by the support graph.
Thus, on the canonical sector, Boolean adjacency and physical positivity are
extensionally equivalent. -/
theorem centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteSupportAdjacentB
        w hw cutoff half left right = true ↔
      (0 : Q') <
        centralPhysicalFiniteKernel w hw cutoff half left right := by
  constructor
  · exact centralPhysicalFiniteKernel_pos_of_supportAdjacent hleft hright
  · intro hnormalized
    let partition :=
      slabParametricKPhysicalPartition w cutoff (centralExtent half)
    have hpartition : (0 : Q') < partition :=
      slabParametricKPhysicalPartition_pos
        hw cutoff (centralExtent half)
    have hproduct : (0 : Q') <
        centralPhysicalFiniteKernel w hw cutoff half left right *
          partition :=
      Q'.mul_pos hnormalized hpartition
    have hcollapse :
        centralPhysicalFiniteKernel w hw cutoff half left right *
            partition ≈
          centralPhysicalFiniteRawKernel w hw cutoff half left right := by
      unfold centralPhysicalFiniteKernel centralPhysicalFiniteRawKernel
        centralNormalizedPhysicalReflectedKernel partition
      exact Q'.divPos_mul_eqv _ _ hpartition
    have hraw : (0 : Q') <
        centralPhysicalFiniteRawKernel w hw cutoff half left right :=
      Q'.pos_of_lt_of_le hproduct (Q'.le_of_eqv hcollapse)
    exact centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
      w hw cutoff half (source :=
        centralPhysicalFiniteStateAt w hw cutoff half left)
      (target := centralPhysicalFiniteStateAt w hw cutoff half right)
      rfl rfl hraw

/-! ## 3. Constructive irreducibility of the canonical vacuum sector -/

/-- Every two indices in the canonical vacuum sector are joined by explicit
Type-level data whose every edge has strictly positive normalized physical
kernel weight. -/
def centralPhysicalFiniteVacuumSector_positiveKernelConnected
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    ∀ left right,
      left ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      right ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        left right := by
  intro left right hleft hright
  exact PositiveKernelChainIn.ofChainIn
    (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (fun first next hfirst hnext hedge =>
      centralPhysicalFiniteKernel_pos_of_supportAdjacent
        hfirst hnext hedge)
    hleft
    (centralPhysicalFiniteVacuumSector_connected
      w hw cutoff half left right hleft hright)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteRawKernel_pos_of_supportAdjacent
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteKernel_pos_of_supportAdjacent
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteVacuumSector_positiveKernelConnected
