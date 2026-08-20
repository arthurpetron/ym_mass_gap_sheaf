/-
# Constructive finite positive floors for boundary-message kernels

A strictly positive function on explicit nonempty finite source and target
lists has an exact positive rational minimum.  This file packages the simple
source-product-target enumeration needed by the physical terminal-smoothed
BF4 kernel.  The result is computational: the floor is obtained by list
recursion using rational minimum, with no compactness or choice.
-/

import YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint

namespace YMGap.Continuum.BF4BoundaryMessageFinitePositiveFloor

open YMGap.Constructive
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint

/-- An exact positive lower bound for every entry of one displayed finite
kernel matrix. -/
structure FinitePositiveKernelFloor
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (kernel : Source -> Target -> Q') : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_le : forall source, source ∈ sources ->
    forall target, target ∈ targets -> floor <= kernel source target

/-- Enumerating the Cartesian product and taking its recursive rational
minimum constructs the finite positive kernel floor. -/
def finitePositiveKernelFloorOfNonempty
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (kernel : Source -> Target -> Q')
    (sourceWitness : Source) (sourceWitness_mem : sourceWitness ∈ sources)
    (targetWitness : Target) (targetWitness_mem : targetWitness ∈ targets)
    (kernel_pos : forall source, source ∈ sources ->
      forall target, target ∈ targets -> (0 : Q') < kernel source target) :
    FinitePositiveKernelFloor sources targets kernel := by
  let pairs : List (Source × Target) :=
    sources.flatMap fun source => targets.map fun target => (source, target)
  let value : Source × Target -> Q' := fun pair => kernel pair.1 pair.2
  have witness_mem : (sourceWitness, targetWitness) ∈ pairs := by
    apply List.mem_flatMap.mpr
    exact ⟨sourceWitness, sourceWitness_mem,
      List.mem_map.mpr ⟨targetWitness, targetWitness_mem, rfl⟩⟩
  have pairs_nonempty : pairs ≠ [] :=
    List.ne_nil_of_mem witness_mem
  have value_pos : forall pair, pair ∈ pairs -> (0 : Q') < value pair := by
    intro pair pair_mem
    obtain ⟨source, source_mem, pair_mem⟩ :=
      List.mem_flatMap.mp pair_mem
    obtain ⟨target, target_mem, rfl⟩ := List.mem_map.mp pair_mem
    exact kernel_pos source source_mem target target_mem
  let pairFloor :=
    positiveFiniteFloorOfNonempty pairs value pairs_nonempty value_pos
  exact
    { floor := pairFloor.floor
      floor_pos := pairFloor.floor_pos
      floor_le := by
        intro source source_mem target target_mem
        apply pairFloor.floor_le (source, target)
        apply List.mem_flatMap.mpr
        exact ⟨source, source_mem,
          List.mem_map.mpr ⟨target, target_mem, rfl⟩⟩ }

end YMGap.Continuum.BF4BoundaryMessageFinitePositiveFloor

#print axioms YMGap.Continuum.BF4BoundaryMessageFinitePositiveFloor.finitePositiveKernelFloorOfNonempty
