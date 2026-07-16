/-
# The old full-box face coordinates cannot carry an exact RP block kernel

An exact facewise reflection intertwiner needs a deterministic action of the
geometric half-time reflection on the finite face coordinates before any
kernel equation can be stated.  The existing full-box enumeration omits the
reflected top/bottom boundary partner of a spatial face.  Consequently the
required face reindex does not exist on any nonempty box.

This file records the obstruction at the intended positive Markov-kernel
interface.  Positivity and row normalization do not repair the missing
geometry.  The boundary-complete slab from `Z4HalfTimeReflectionGeometry` is
therefore a necessary change of state space for a genuine reflection-positive
block construction.
-/

import YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.Z4OldBoxReflectionKernelFence

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The minimum old-box interface required by a geometry-respecting exact
facewise reflection kernel.  The `faceReflection` field is not an auxiliary
assumption: it is the coordinate action needed to form reflected source and
target labellings in an exact kernel-intertwining identity. -/
structure OldBoxFacewiseReflectionKernel (K n : Nat) where
  kernel : EdgeLabelling → EdgeLabelling → Q'
  nonnegative : ∀ source target, (0 : Q') ≤ kernel source target
  row_normalized : ∀ source,
    listQSum (kernel source) (explicitPhysicalLabellings K n) ≈ 1
  faceReflection : PhysicalFaceReflectionReindex n

/-- No positive row-normalized kernel can satisfy the old-box exact facewise
reflection interface on a nonempty box, because its required coordinate
reflection is geometrically impossible. -/
theorem no_oldBoxFacewiseReflectionKernel
    {K n : Nat} (hn : 0 < n) :
    OldBoxFacewiseReflectionKernel K n → False := by
  intro candidate
  exact no_physicalFaceReflectionReindex hn candidate.faceReflection

/-- The obstruction already applies to the cutoff-one target used by the
dyadic SU(2)-parity pushforward. -/
theorem no_cutoffOne_oldBoxFacewiseReflectionKernel
    {n : Nat} (hn : 0 < n) :
    OldBoxFacewiseReflectionKernel 1 n → False :=
  no_oldBoxFacewiseReflectionKernel hn

#print axioms no_oldBoxFacewiseReflectionKernel
#print axioms no_cutoffOne_oldBoxFacewiseReflectionKernel

end YMGap.Continuum.Z4OldBoxReflectionKernelFence
