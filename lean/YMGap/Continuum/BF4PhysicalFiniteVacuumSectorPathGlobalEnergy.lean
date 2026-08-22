/-
# Canonical BF4 path energy is bounded by global Dirichlet energy

The local path theorem uses a recursively doubled edge-energy budget.  This
module assigns the same chain a recursively computed rational scale and proves
that the amplified path budget is at most that scale times the full directed
Dirichlet energy of the finite carrier.

At a path step, the actual edge term is one nonnegative summand of the global
double sum.  If the remaining path costs at most `scale * globalEnergy`, then
doubling the edge-plus-tail budget costs at most
`((1 + scale) + (1 + scale)) * globalEnergy`.  This deliberately crude scale
is sufficient because every canonical sector path is explicit and finite.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem square_nonnegative (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

/-! ## 1. One nonnegative edge is below the full double sum -/

theorem listQSum_member_le_nonnegative
    {State : Type} (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ (states : List State) {state : State},
      state ∈ states → value state ≤ listQSum value states
  | [], _, hstate => False.elim (List.not_mem_nil hstate)
  | first :: rest, state, hstate => by
      rcases List.mem_cons.mp hstate with hfirst | hrest
      · subst state
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value rest
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative
          value hvalue rest hrest
        have htailLe : listQSum value rest ≤
            value first + listQSum value rest := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value first) (listQSum value rest)
            (hvalue first)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

/-- One displayed nonnegative joint-kernel square is at most the full directed
finite Dirichlet energy. -/
theorem finiteJointDirichletEnergy_term_le
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q')
    (hjoint : ∀ left right, (0 : Q') ≤ joint left right)
    (left right : State)
    (hleft : left ∈ states) (hright : right ∈ states) :
    joint left right *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      finiteJointDirichletEnergy states coefficient joint := by
  let term : State → State → Q' := fun source target =>
    joint source target *
      ((coefficient source + -coefficient target) *
        (coefficient source + -coefficient target))
  have hterm : ∀ source target, (0 : Q') ≤ term source target := by
    intro source target
    exact Q'.mul_nonneg _ _ (hjoint source target)
      (square_nonnegative _)
  have hrowNonnegative : ∀ source,
      (0 : Q') ≤ listQSum (term source) states := by
    intro source
    exact listQSum_nonnegative_on (term source) states
      (fun target _ => hterm source target)
  have hwithinRow : term left right ≤
      listQSum (term left) states :=
    listQSum_member_le_nonnegative
      (term left) (hterm left) states hright
  have hrowWithinGlobal : listQSum (term left) states ≤
      listQSum (fun source => listQSum (term source) states) states :=
    listQSum_member_le_nonnegative
      (fun source => listQSum (term source) states)
      hrowNonnegative states hleft
  exact Q'.le_trans' _ _ _ hwithinRow hrowWithinGlobal

/-! ## 2. A recursively computed amplification scale -/

namespace PositiveKernelChainIn

/-- A rational ceiling for the number of copies of the global energy needed
by the recursively amplified chain energy. -/
def amplificationScale
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State} :
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
      kernel support first last → Q'
  | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => 0
  | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
      _ _ rest =>
      (1 + amplificationScale rest) +
        (1 + amplificationScale rest)

theorem amplificationScale_nonnegative
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State} :
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last) →
      (0 : Q') ≤ amplificationScale path
  | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      Q'.le_refl' 0
  | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
      _ _ rest => by
      apply Q'.zero_le_add
      · exact Q'.zero_le_add _ _ (by decide)
          (amplificationScale_nonnegative rest)
      · exact Q'.zero_le_add _ _ (by decide)
          (amplificationScale_nonnegative rest)

/-- The recursive path energy is bounded by its recursive scale times the
full finite directed Dirichlet energy. -/
theorem amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (hkernel : ∀ left right, (0 : Q') ≤ kernel left right) :
    {first last : State} → first ∈ support →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient path ≤
        amplificationScale path *
          finiteJointDirichletEnergy support coefficient kernel
  | first, _, _hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv
            (finiteJointDirichletEnergy support coefficient kernel)))
  | first, last, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) _positive hnext rest => by
      let globalEnergy :=
        finiteJointDirichletEnergy support coefficient kernel
      let edgeEnergy := kernel first next *
        ((coefficient first + -coefficient next) *
          (coefficient first + -coefficient next))
      let restEnergy :=
        BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient rest
      let restScale := amplificationScale rest
      have hedge : edgeEnergy ≤ globalEnergy := by
        exact finiteJointDirichletEnergy_term_le
          support coefficient kernel hkernel first next hfirst hnext
      have hrest : restEnergy ≤ restScale * globalEnergy := by
        exact amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
          coefficient hkernel hnext rest
      have hone : edgeEnergy + restEnergy ≤
          globalEnergy + restScale * globalEnergy :=
        Q'.add_le_add hedge hrest
      have htwice :
          (edgeEnergy + restEnergy) + (edgeEnergy + restEnergy) ≤
            (globalEnergy + restScale * globalEnergy) +
              (globalEnergy + restScale * globalEnergy) :=
        Q'.add_le_add hone hone
      have hscale :
          ((1 + restScale) + (1 + restScale)) * globalEnergy ≈
            (globalEnergy + restScale * globalEnergy) +
              (globalEnergy + restScale * globalEnergy) := by
        refine Q'.eqv_trans _
          ((1 + restScale) * globalEnergy +
            (1 + restScale) * globalEnergy) _
          (Q'.add_mul_eqv _ _ _) ?_
        exact Q'.add_eqv_congr'
          (Q'.eqv_trans _
            (1 * globalEnergy + restScale * globalEnergy) _
            (Q'.add_mul_eqv _ _ _)
            (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)))
          (Q'.eqv_trans _
            (1 * globalEnergy + restScale * globalEnergy) _
            (Q'.add_mul_eqv _ _ _)
            (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)))
      exact Q'.le_trans' _ _ _ htwice
        (Q'.le_of_eqv (Q'.eqv_symm hscale))

end PositiveKernelChainIn

/-! ## 3. Specialization to every canonical BF4 sector path -/

theorem centralPhysicalFiniteVacuumSector_pathEnergy_le_scale_mul_Dirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
        coefficient
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) ≤
      PositiveKernelChainIn.amplificationScale
          (centralPhysicalFiniteVacuumSectorPositivePath
            w hw cutoff half left right hleft hright) *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  apply PositiveKernelChainIn.amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
  · intro source target
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      hw cutoff half _ _
  · exact hleft

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.finiteJointDirichletEnergy_term_le
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.centralPhysicalFiniteVacuumSector_pathEnergy_le_scale_mul_Dirichlet
