/-
# Literal directed-edge occurrences of finite BF4 vacuum paths

The polynomial path-energy compiler is recursive data.  Congestion estimates
need the same information as a literal list of directed edge occurrences so
that repeated use of one physical edge can be counted explicitly.

This module extracts that list from every positive-kernel chain and proves:

* its length is the existing path length;
* every displayed edge has both endpoints in the declared support; and
* the existing linear path energy is exactly the sum of the physical
  kernel-weighted squared differences over the occurrence list.

No congestion bound, uniform edge floor, completed gap, continuum limit, or
Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

namespace PositiveKernelChainIn

/-- The literal vertex sequence of a positive-kernel chain, including both
endpoints.  This is the vertex-level companion to `directedEdges`. -/
def vertices
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last → List State
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      [first]
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ _ rest =>
      first :: vertices rest

/-- The literal directed edges traversed by a positive-kernel chain, retaining
duplicates and orientation. -/
def directedEdges
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last → List (State × State)
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      []
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) _ _ rest =>
      (first, next) :: directedEdges rest

/-- Source vertex of the final directed edge.  On a reflexive path the
fallback is its sole vertex; every nontrivial path returns the literal source
of its terminal step. -/
def terminalSource
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last → State
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      first
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ _ rest =>
      match rest with
      | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
          first
      | BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
          positive next_mem tail =>
          terminalSource
            (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
              positive next_mem tail)

/-- The extracted terminal source really supplies the final directed edge of
every nontrivial positive-kernel chain. -/
theorem terminalSource_mem_directedEdges_of_step
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first next last : State}
      (positive : (0 : Q') < kernel first next)
      (next_mem : next ∈ support)
      (rest :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support next last),
      (terminalSource
          (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
            positive next_mem rest), last) ∈
        directedEdges
          (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
            positive next_mem rest)
  | _, _, _, positive, next_mem,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      List.mem_cons_self
  | first, next, last, positive, next_mem,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        next_positive after_next_mem tail => by
      simp only [terminalSource, directedEdges]
      exact List.mem_cons_of_mem (first, next)
        (terminalSource_mem_directedEdges_of_step
          next_positive after_next_mem tail)

theorem terminalSource_mem_directedEdges
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last)
    (hne : first ≠ last) :
    (terminalSource path, last) ∈ directedEdges path := by
  cases path with
  | refl state => exact False.elim (hne rfl)
  | step positive next_mem rest =>
      exact terminalSource_mem_directedEdges_of_step positive next_mem rest

theorem directedEdges_length_eq_edgeLength
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      (directedEdges path).length =
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      rfl
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ _ rest => by
      simp only [directedEdges, List.length_cons,
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength]
      exact congrArg (fun length => length + 1)
        (directedEdges_length_eq_edgeLength rest)

/-- The source of every traversed edge occurs in the literal vertex list. -/
theorem directedEdges_source_mem_vertices
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first last : State}
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last)
      (edge : State × State),
      edge ∈ directedEdges path → edge.1 ∈ vertices path
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      edge, hedge => by
      cases hedge
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) _ _ rest,
      edge, hedge => by
      rcases List.mem_cons.mp hedge with hhead | htail
      · rw [hhead]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem first
          (directedEdges_source_mem_vertices rest edge htail)

/-- A vertex-simple positive path cannot repeat a directed edge. -/
theorem directedEdges_nodup_of_vertices_nodup
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first last : State}
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last),
      (vertices path).Nodup → (directedEdges path).Nodup
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      _ => List.nodup_nil
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive next_mem rest,
      hvertices => by
      have hparts := List.nodup_cons.mp hvertices
      apply List.nodup_cons.mpr
      constructor
      · intro hhead
        exact hparts.1
          (directedEdges_source_mem_vertices rest (first, next) hhead)
      · exact directedEdges_nodup_of_vertices_nodup rest hparts.2

/-- Every literal occurrence has both endpoints in the chain support. -/
theorem directedEdges_mem_support
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} → (hfirst : first ∈ support) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      ∀ edge, edge ∈ directedEdges path →
        edge.1 ∈ support ∧ edge.2 ∈ support
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      edge, hedge => by
      cases hedge
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) _ hnext rest,
      edge, hedge => by
      rcases List.mem_cons.mp hedge with hhead | htail
      · subst edge
        exact ⟨hfirst, hnext⟩
      · exact directedEdges_mem_support hnext rest edge htail

/-- Every literal directed edge remembers the strict kernel positivity carried
by the corresponding step of the positive-kernel chain. -/
theorem directedEdges_kernel_pos
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      ∀ edge, edge ∈ directedEdges path →
        (0 : Q') < kernel edge.1 edge.2
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      edge, hedge => by
      cases hedge
  | first, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive _ rest,
      edge, hedge => by
      rcases List.mem_cons.mp hedge with hhead | htail
      · subst edge
        exact positive
      · exact directedEdges_kernel_pos rest edge htail

/-- The final source of every nontrivial chain carries the strict kernel
positivity of its literal terminal edge.  Keeping this generic avoids forcing
large concrete kernels through definitional normalization at use sites. -/
theorem terminalSource_kernel_pos
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last)
    (hne : first ≠ last) :
    (0 : Q') < kernel (terminalSource path) last :=
  directedEdges_kernel_pos path _
    (terminalSource_mem_directedEdges path hne)

/-- The recursive linear energy is exactly the sum over the literal directed
edge-occurrence list. -/
theorem linearEnergy_eqv_directedEdges_sum
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path ≈
        listQSum
          (fun edge =>
            kernel edge.1 edge.2 *
              ((coefficient edge.1 + -coefficient edge.2) *
                (coefficient edge.1 + -coefficient edge.2)))
          (directedEdges path)
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      Q'.eqv_refl 0
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ _ rest => by
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (linearEnergy_eqv_directedEdges_sum coefficient rest)

/-- The unweighted squared increments can equivalently be summed over the
literal directed-edge list.  This is the exact reindexing needed by
floor-free weighted-flow estimates. -/
theorem edgeSquareSum_eqv_edgeDifferences
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      listQSum
          (fun edge =>
            (coefficient edge.1 + -coefficient edge.2) *
              (coefficient edge.1 + -coefficient edge.2))
          (directedEdges path) ≈
        listQSum (fun value => value * value)
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeDifferences
            coefficient path)
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      Q'.eqv_refl 0
  | _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ _ rest => by
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (edgeSquareSum_eqv_edgeDifferences coefficient rest)

/-- Multiplying by path length preserves the literal occurrence identity. -/
theorem length_mul_linearEnergy_eqv_directedEdges_sum
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    {first last : State}
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last) :
    Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path) *
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path ≈
      Q'.ofNat (directedEdges path).length *
        listQSum
          (fun edge =>
            kernel edge.1 edge.2 *
              ((coefficient edge.1 + -coefficient edge.2) *
                (coefficient edge.1 + -coefficient edge.2)))
          (directedEdges path) := by
  exact Q'.eqv_trans _
    (Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path) *
      listQSum
        (fun edge =>
          kernel edge.1 edge.2 *
            ((coefficient edge.1 + -coefficient edge.2) *
              (coefficient edge.1 + -coefficient edge.2)))
        (directedEdges path)) _
    (Q'.mul_eqv_congr_left _ _ _
      (linearEnergy_eqv_directedEdges_sum coefficient path))
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq
        (congrArg Q'.ofNat
          (directedEdges_length_eq_edgeLength path).symm)))

end PositiveKernelChainIn

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_length_eq_edgeLength
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.terminalSource_mem_directedEdges
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_nodup_of_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.terminalSource_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.linearEnergy_eqv_directedEdges_sum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.length_mul_linearEnergy_eqv_directedEdges_sum
