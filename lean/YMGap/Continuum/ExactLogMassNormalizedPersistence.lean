/-
M3a -- typed handoff from mass-normalized RG persistence to the exact
constructive logarithmic rate family.

`MassNormalizedGapPersistence` propagates rational lower certificates through
a one-step normalized loss budget.  `PhysicalSeparatorFullLogComparison`
carries the exact constructive-real rates.  This file ties the two layers to
the same physical spacing and requires an explicit proof that each rational
certificate lies below the corresponding exact rate.

The result is a uniform exact-log floor, and, with an independent exact upper
ceiling, a complete exact physical-separator certificate.  The RG step,
summable loss budget, spacing identification, and rational-to-exact comparison
remain named inputs.  No BF4 producer or continuum reconstruction is supplied.
-/

import YMGap.Continuum.MassNormalizedGapPersistence
import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.ExactLogMassNormalizedPersistence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.MassNormalizedGapPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-! ## 1. Same-spacing rational certificates for exact rates -/

/-- A mass-normalized rational RG flow certified below one exact logarithmic
rate family.  The pointwise spacing equivalence prevents a flow on an auxiliary
scale from being silently substituted for the physical separator's spacing. -/
structure ExactLogMassNormalizedFlow (P : PhysicalSeparator) : Type 1 where
  exactRate : FullRangeExactPhysicalLogRateFamily P
  rationalFlow : MassNormalizedBlockFlow
  spacing_identification : forall k : Nat,
    (rationalFlow.spacing k).eqv
      (exactRate.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (rationalFlow.mass k)) (exactRate.rate k)

namespace ExactLogMassNormalizedFlow

variable {P : PhysicalSeparator}

/-! ## 2. Persistence transports to the exact family -/

/-- A summably persistent rational lower flow supplies a uniform floor for the
same exact logarithmic rates. -/
def uniformExactFloor
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow) :
    UniformFullRangeLogRateFloor flow.exactRate where
  floor := persistence.floorWitness
  floor_pos := persistence.floorWitness_pos
  floor_bound := fun k => by
    have hrational :
        CReal.leEv (CReal.ofQ' persistence.floorWitness)
          (CReal.ofQ' (flow.rationalFlow.mass k)) :=
      CReal.leEv_ofQ'_of_approx_ge
        (fun _ => persistence.floorWitness_le_mass k)
    exact CReal.leEv_trans hrational (flow.mass_certificate k)

@[simp] theorem uniformExactFloor_floor
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow) :
    (flow.uniformExactFloor persistence).floor =
      persistence.floorWitness := rfl

theorem uniformExactFloor_floor_pos
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow) :
    (0 : Q') < (flow.uniformExactFloor persistence).floor :=
  persistence.floorWitness_pos

/-! ## 3. Add the independently proved exact upper ceiling -/

/-- Package the RG-derived exact lower floor with an exact upper ceiling.
The ceiling is deliberately separate: mass persistence protects positivity but
does not prove finiteness of the continuum-scaled rate. -/
def exactPhysicalSeparatorCertificate
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    FullRangeExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := flow.exactRate
  uniformFloor := flow.uniformExactFloor persistence
  finiteCeiling := ceiling

@[simp] theorem exactPhysicalSeparatorCertificate_separator
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).separator =
      P := rfl

@[simp] theorem exactPhysicalSeparatorCertificate_floor
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor =
      persistence.floorWitness := rfl

theorem exactPhysicalSeparatorCertificate_floor_pos
    (flow : ExactLogMassNormalizedFlow P)
    (persistence : MassNormalizedPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (0 : Q') <
      (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor :=
  persistence.floorWitness_pos

end ExactLogMassNormalizedFlow

end YMGap.Continuum.ExactLogMassNormalizedPersistence

#print axioms YMGap.Continuum.ExactLogMassNormalizedPersistence.ExactLogMassNormalizedFlow.uniformExactFloor
#print axioms YMGap.Continuum.ExactLogMassNormalizedPersistence.ExactLogMassNormalizedFlow.exactPhysicalSeparatorCertificate
#print axioms YMGap.Continuum.ExactLogMassNormalizedPersistence.ExactLogMassNormalizedFlow.exactPhysicalSeparatorCertificate_floor_pos
