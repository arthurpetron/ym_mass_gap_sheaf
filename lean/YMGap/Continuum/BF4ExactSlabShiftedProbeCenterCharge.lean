/-
# Charge filters for all four ORIGINAL shifted-probe moments

Both observables are the existing lower/upper enlargements of shiftedProbe.
At every volume margin the two Boolean flags select partition, lower mean,
upper mean or mixed moment, against the COMPLETE selected original action.
The incidence-only checker rejects an exactly zero moment at every spin.

The four moments have DIFFERENT charge tests. In particular the partition
test must not be applied unchanged to the two probe insertions. No bound or
sign of surviving connected terms, accepted response certificate, or
continuum conclusion is claimed.
-/

import YMGap.Continuum.BF4ExactSlabCenterCharge
import YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockCenterCharge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

def insertion (margin : Nat) (lo hi : Bool) : RatPoly :=
  polyMul (if lo then lower (enlarge margin shiftedProbe) else polyOne)
    (if hi then upper (enlarge margin shiftedProbe) else polyOne)

def charges (margin : Nat) (lo hi : Bool) (block : Nat) : Nat :=
  (if lo then faceDegree (responseExtent margin) block (sliceFace margin 0) else 0) +
    (if hi then faceDegree (responseExtent margin) block (sliceFace margin 3) else 0)

theorem insertion_charge (margin : Nat) (lo hi : Bool) (block : Nat) :
    HasCharge block (charges margin lo hi block) (insertion margin lo hi) := by
  have hl : HasCharge block (faceDegree (responseExtent margin) block (sliceFace margin 0))
      (lower (enlarge margin shiftedProbe)) := by
    rw [lower_shifted_probe_pin]
    simpa only [Nat.one_mul] using face_character_charge (responseExtent margin) block (sliceFace margin 0)
      (slice_physical margin ⟨0,by decide⟩) 1
  have hu : HasCharge block (faceDegree (responseExtent margin) block (sliceFace margin 3))
      (upper (enlarge margin shiftedProbe)) := by
    rw [upper_shifted_probe_pin]
    simpa only [Nat.one_mul] using face_character_charge (responseExtent margin) block (sliceFace margin 3)
      (slice_physical margin ⟨3,by decide⟩) 1
  cases lo <;> cases hi
  · exact (HasCharge.one block).mul (HasCharge.one block)
  · exact (HasCharge.one block).mul hu
  · exact hl.mul (HasCharge.one block)
  · exact hl.mul hu

/-- The actual partition/one-point/two-point Haar moment, not a tube sub-action. -/
def moment (margin : Nat) (lo hi : Bool) (labels : EdgeLabelling) : Q' :=
  quaternionHaar (N margin) (polyMul (insertion margin lo hi)
    (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) labels))

def momentCheck (margin : Nat) (lo hi : Bool) (labels : EdgeLabelling) : Bool :=
  insertionCheck (responseExtent margin) labels (charges margin lo hi)

theorem moment_rejected (margin : Nat) (lo hi : Bool) (labels : EdgeLabelling)
    (h : momentCheck margin lo hi labels = false) : moment margin lo hi labels ≈ 0 :=
  inserted_rejected_zero (responseExtent margin) labels (charges margin lo hi) (insertion margin lo hi)
    (insertion_charge margin lo hi) h

theorem moment_filter (margin : Nat) (lo hi : Bool) (labels : EdgeLabelling) :
    moment margin lo hi labels ≈ (if momentCheck margin lo hi labels then moment margin lo hi labels else 0) := by
  cases h : momentCheck margin lo hi labels with
  | false => exact moment_rejected margin lo hi labels h
  | true => exact Q'.eqv_refl _

end YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge.insertion_charge
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge.moment
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge.momentCheck
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge.moment_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge.moment_filter
