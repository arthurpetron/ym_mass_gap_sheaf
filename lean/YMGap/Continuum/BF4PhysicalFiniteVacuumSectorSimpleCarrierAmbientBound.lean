/-
# An explicit ambient-enumeration bound for the BF4 simple-path scale

The simple-path Poincare scale is indexed by the cardinality of the connected
vacuum sector.  This module removes that root-component/filter opacity.  The
sector is bounded by the positive physical carrier, the positive carrier is a
filter of all bounded lower-face labellings, and that ambient enumeration has
the exact cardinality

  (cutoff + 1) ^ (# lower-face coordinates).

Consequently the simple-path scale is bounded by one plus the square of this
explicit ambient count.  The bound exposes cutoff growth; it does not claim a
uniform spectral gap or a lower estimate on the persistent edge floor.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. Exact ambient enumeration and nested carrier bounds -/

/-- Exact cardinality of the Cartesian bounded-labelling enumeration. -/
theorem boundedEdgeLabellings_length (cutoff : Nat) :
    forall ids : List Nat,
      (boundedEdgeLabellings cutoff ids).length =
        (cutoff + 1) ^ ids.length
  | [] => rfl
  | head :: tail => by
      unfold boundedEdgeLabellings
      have hflat :=
        YMGap.Continuum.Z4FiniteBoxTrivalentResolution.length_flatMap_fixed
          (List.range (cutoff + 1))
          (fun spin =>
            (boundedEdgeLabellings cutoff tail).map
              (fun label => setEdgeLabel label head spin))
          ((cutoff + 1) ^ tail.length)
          (fun _ => by simp [boundedEdgeLabellings_length cutoff tail])
      rw [hflat, List.length_range, List.length_cons, Nat.pow_succ]
      exact Nat.mul_comm _ _

/-- The complete lower-half state list has an exact power-law cardinality. -/
theorem centralHalfStates_length (cutoff half : Nat) :
    (centralHalfStates cutoff half).length =
      (cutoff + 1) ^ (centralLowerFaceIds half).length := by
  unfold centralHalfStates
  exact boundedEdgeLabellings_length cutoff (centralLowerFaceIds half)

/-- At the smallest central slab, the lower half has the 24 explicit BF4
face coordinates already used by the cutoff pilots. -/
theorem centralLowerFaceIds_zero_length :
    (centralLowerFaceIds 0).length = 24 := by
  decide

/-- The connected vacuum-sector index list is no longer than the whole
positive-row physical carrier. -/
theorem centralPhysicalFiniteVacuumSectorIndices_length_le_carrierSize
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length ≤
      centralPhysicalFiniteCarrierSize w hw cutoff half := by
  have hbound := FiniteListBound.nodup_subset_length_le
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw cutoff half)
    (fun index hindex => List.mem_range.mpr
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw cutoff half hindex))
  simpa [centralPhysicalFiniteIndexCarrier] using hbound

/-- The positive-row physical carrier is a filter of the complete lower-half
Cartesian enumeration. -/
theorem centralPhysicalFiniteCarrierSize_le_ambient
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteCarrierSize w hw cutoff half ≤
      (cutoff + 1) ^ (centralLowerFaceIds half).length := by
  unfold centralPhysicalFiniteCarrierSize centralPositiveHalfStates
  exact Nat.le_trans
    (List.length_filter_le _ _)
    (Nat.le_of_eq (centralHalfStates_length cutoff half))

/-- The explicit ambient carrier count used below. -/
def centralPhysicalFiniteVacuumSectorAmbientCarrierSize
    (cutoff half : Nat) : Nat :=
  (cutoff + 1) ^ (centralLowerFaceIds half).length

/-- The root-component cardinality is bounded by the exact ambient
Cartesian count. -/
theorem centralPhysicalFiniteVacuumSectorIndices_length_le_ambient
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length ≤
      centralPhysicalFiniteVacuumSectorAmbientCarrierSize cutoff half := by
  exact Nat.le_trans
    (centralPhysicalFiniteVacuumSectorIndices_length_le_carrierSize
      w hw cutoff half)
    (centralPhysicalFiniteCarrierSize_le_ambient w hw cutoff half)

/-- Extent one therefore has the completely explicit ambient count
`(cutoff + 1)^24`. -/
theorem centralPhysicalFiniteVacuumSectorIndices_length_le_ambient_zero
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff : Nat) :
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff 0).length ≤
      (cutoff + 1) ^ 24 := by
  simpa [centralPhysicalFiniteVacuumSectorAmbientCarrierSize,
    centralLowerFaceIds_zero_length] using
      (centralPhysicalFiniteVacuumSectorIndices_length_le_ambient
        w hw cutoff 0)

/-! ## 2. Explicit ambient square scale -/

/-- One plus the square of the full lower-face Cartesian carrier. -/
def centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
    (cutoff half : Nat) : Q' :=
  let size := centralPhysicalFiniteVacuumSectorAmbientCarrierSize cutoff half
  1 + Q'.ofNat (size * size)

theorem centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale_pos
    (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
        cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
  exact Q'.pos_add_nonneg (by decide)
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

/-- The loop-erased simple-path scale is bounded by the explicit full
Cartesian carrier-square scale. -/
theorem centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
        cutoff half := by
  let sectorSize :=
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length
  let ambientSize :=
    centralPhysicalFiniteVacuumSectorAmbientCarrierSize cutoff half
  have hsize : sectorSize ≤ ambientSize :=
    centralPhysicalFiniteVacuumSectorIndices_length_le_ambient
      w hw cutoff half
  have hsquare : sectorSize * sectorSize ≤ ambientSize * ambientSize :=
    Nat.mul_le_mul hsize hsize
  have hcast : Q'.ofNat (sectorSize * sectorSize) ≤
      Q'.ofNat (ambientSize * ambientSize) :=
    Q'.ofNat_le_ofNat hsquare
  unfold centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
  exact Q'.add_le_add_left 1 _ _ hcast

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.boundedEdgeLabellings_length
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralHalfStates_length
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralLowerFaceIds_zero_length
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralPhysicalFiniteVacuumSectorIndices_length_le_carrierSize
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralPhysicalFiniteCarrierSize_le_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralPhysicalFiniteVacuumSectorIndices_length_le_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralPhysicalFiniteVacuumSectorIndices_length_le_ambient_zero
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
