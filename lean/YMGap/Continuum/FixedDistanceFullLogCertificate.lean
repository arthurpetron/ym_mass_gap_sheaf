/-
M2k -- a fixed-distance contraction gives a full-range exact logarithmic
physical mass floor.

`FixedDistancePhysicalSeparator` already proves the rational estimate

    c <= (1 - q_j) / a_j

from one grouped contraction of the same physical separator over a uniformly
bounded physical distance.  The global comparison in
`PhysicalSeparatorFullLogComparison` upgrades it, without a half-window, to

    c <= -log(q_j) / a_j.

Thus the grouped producer supplies the exact lower half of the full-range M2
certificate.  A finite upper bound for the exact logarithmic rate remains an
independent input and is kept explicit below.
-/

import YMGap.Continuum.FixedDistancePhysicalSeparator
import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.FixedDistancePhysicalSeparator

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
namespace FixedDistanceContraction

variable {P : PhysicalSeparator} {A : PhysicalSpacing}

/-- The canonical full-range exact logarithmic rate family attached to the
same physical separator and spacing as the fixed-distance contraction. -/
def fullRangeRateFamily (_D : FixedDistanceContraction P A) :
    FullRangeExactPhysicalLogRateFamily P :=
  fullRangeRateFamilyOfPhysicalData P A.spacing A.spacing_pos

/-- **Full-range fixed-distance floor.**  The positive grouped-contraction
floor bounds the exact logarithmic mass rate at every scale, with no
`q_j >= 1/2` assumption. -/
def fullRangeExactFloor (D : FixedDistanceContraction P A) :
    UniformFullRangeLogRateFloor D.fullRangeRateFamily where
  floor := D.floorRate
  floor_pos := D.floorRate_pos
  floor_bound := fun j => by
    have hproxy :
        CReal.leEv (CReal.ofQ' D.floorRate)
          (CReal.ofQ' (marginRate P A j)) :=
      CReal.leEv_ofQ'_of_approx_ge (fun _ => D.floorRate_le_marginRate j)
    exact CReal.leEv_trans hproxy (marginRate_le_fullMassRate P A j)

/-- The independent exact upper-rate obligation for the canonical full-range
family of a fixed-distance contraction. -/
abbrev FullRangeExactCeiling (D : FixedDistanceContraction P A) : Type :=
  FullRangeLogRateCeiling D.fullRangeRateFamily

/-- A fixed-distance contraction and an independent finite exact upper bound
package the complete full-range physical-separator certificate. -/
def fullRangeExactCertificate
    (D : FixedDistanceContraction P A)
    (U : D.FullRangeExactCeiling) :
    FullRangeExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := D.fullRangeRateFamily
  uniformFloor := D.fullRangeExactFloor
  finiteCeiling := U

@[simp] theorem fullRangeExactFloor_floor
    (D : FixedDistanceContraction P A) :
    D.fullRangeExactFloor.floor = D.floorRate := rfl

@[simp] theorem fullRangeExactCertificate_separator
    (D : FixedDistanceContraction P A)
    (U : D.FullRangeExactCeiling) :
    (D.fullRangeExactCertificate U).separator = P := rfl

@[simp] theorem fullRangeExactCertificate_floor
    (D : FixedDistanceContraction P A)
    (U : D.FullRangeExactCeiling) :
    (D.fullRangeExactCertificate U).uniformFloor.floor = D.floorRate := rfl

@[simp] theorem fullRangeExactCertificate_ceiling
    (D : FixedDistanceContraction P A)
    (U : D.FullRangeExactCeiling) :
    (D.fullRangeExactCertificate U).finiteCeiling.ceiling = U.ceiling := rfl

end FixedDistanceContraction

end YMGap.Continuum.FixedDistancePhysicalSeparator

#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.fullRangeExactFloor
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.fullRangeExactCertificate
