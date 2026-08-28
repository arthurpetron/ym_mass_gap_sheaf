/-
# A reflected positive channel contracts one same-object OS moment

The retained-fraction construction accepts arbitrary marked faces, whereas
the physical same-object transfer moment requires the target to be the exact
half-time reflection of a lower-half root.  Package precisely that missing
geometry together with one successful positive connected channel.

The resulting compiler constructs an explicit rational retained fraction and
a nonnegative contraction factor strictly below one, then applies the
existing Osterwalder--Schrader bridge to the genuine same-object connected
physical Markov moment.

Constructive contract: explicit finite witnesses and existing exact rational
inequalities only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction

namespace YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The exact finite witness needed to turn a positive recoupling channel
into a same-object physical OS contraction. -/
structure SlabObservableReflectedPositiveChannel
    (D : SlabPhysicalData) : Type where
  rootFaceId : Nat
  root_lower : rootFaceId ∈ centralLowerFaceIds D.half
  coupling_pos : (0 : Q') < D.coupling
  channel : SlabObservablePairedConnectedPositiveChannelWitness
    D rootFaceId (slabFaceReflectId D.extent rootFaceId)

namespace SlabObservableReflectedPositiveChannel

theorem target_physical
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    slabFaceReflectId D.extent data.rootFaceId ∈
      slabPhysicalFaceEdges D.extent :=
  slabFaceReflectId_physical
    (mem_centralLowerFaceIds.mp data.root_lower).1

def contraction
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    SlabObservablePairedSplitRetainedContraction
      D data.rootFaceId
        (slabFaceReflectId D.extent data.rootFaceId) :=
  slabObservablePairedSplitRetainedContraction
    D data.coupling_pos data.rootFaceId
    (slabFaceReflectId D.extent data.rootFaceId)
    data.target_physical data.channel

def fraction
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) : Q' :=
  data.contraction.fraction

def factor
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) : Q' :=
  (1 : Q') + -data.fraction

theorem fraction_pos
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    (0 : Q') < data.fraction :=
  data.contraction.fraction_pos

theorem factor_nonnegative
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    (0 : Q') ≤ data.factor :=
  data.contraction.complement_nonnegative

theorem factor_lt_one
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    data.factor < (1 : Q') :=
  data.contraction.complement_lt_one

theorem sameObjectConnectedMarkovMoment_le_factor
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        D data.rootFaceId ≤ data.factor :=
  data.contraction.sameObjectConnectedMarkovMoment_le_complement
    data.root_lower

theorem sameObjectConnectedMarkovMoment_lt_one
    {D : SlabPhysicalData}
    (data : SlabObservableReflectedPositiveChannel D) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        D data.rootFaceId < (1 : Q') :=
  data.contraction.sameObjectConnectedMarkovMoment_lt_one
    data.root_lower

end SlabObservableReflectedPositiveChannel

#print axioms SlabObservableReflectedPositiveChannel.target_physical
#print axioms SlabObservableReflectedPositiveChannel.contraction
#print axioms SlabObservableReflectedPositiveChannel.factor_lt_one
#print axioms SlabObservableReflectedPositiveChannel.sameObjectConnectedMarkovMoment_le_factor
#print axioms SlabObservableReflectedPositiveChannel.sameObjectConnectedMarkovMoment_lt_one

end YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction
