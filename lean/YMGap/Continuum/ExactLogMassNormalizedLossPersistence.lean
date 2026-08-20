/-
M3f -- exact-log handoff for direction-neutral normalized-loss persistence.

Unlike the coarse-block and refinement-specific handoffs, this interface asks
for no exact natural-number relation between adjacent physical spacings.  It
identifies one rational normalized-loss flow pointwise with one exact physical
log-rate family and transports a constructive persistent rational floor to
that same family.

The one-step loss theorem, its summable budget, and the rational-to-exact mass
certificate remain explicit analytic inputs.  No BF4 producer or continuum
reconstruction is supplied here.
-/

import YMGap.Continuum.MassNormalizedLossPersistence
import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.ExactLogMassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-- A direction-neutral rational loss flow certified below one exact physical
log-rate family on pointwise identical spacings. -/
structure ExactLogMassNormalizedLossFlow
    (P : PhysicalSeparator) : Type 1 where
  exactRate : FullRangeExactPhysicalLogRateFamily P
  rationalFlow : MassNormalizedLossFlow
  spacing_identification : forall k : Nat,
    (rationalFlow.spacing k).eqv
      (exactRate.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (rationalFlow.mass k)) (exactRate.rate k)

namespace ExactLogMassNormalizedLossFlow

variable {P : PhysicalSeparator}

/-- A persistent direction-neutral rational flow gives a uniform exact floor
for the same logarithmic rate family. -/
def uniformExactFloor
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
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
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
    (flow.uniformExactFloor persistence).floor =
      persistence.floorWitness := rfl

theorem uniformExactFloor_floor_pos
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
    (0 : Q') < (flow.uniformExactFloor persistence).floor :=
  persistence.floorWitness_pos

/-- An independent exact ceiling completes the same-family rate band. -/
def exactPhysicalSeparatorCertificate
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    FullRangeExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := flow.exactRate
  uniformFloor := flow.uniformExactFloor persistence
  finiteCeiling := ceiling

@[simp] theorem exactPhysicalSeparatorCertificate_separator
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).separator =
      P := rfl

@[simp] theorem exactPhysicalSeparatorCertificate_floor
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor =
      persistence.floorWitness := rfl

theorem exactPhysicalSeparatorCertificate_floor_pos
    (flow : ExactLogMassNormalizedLossFlow P)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (0 : Q') <
      (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor :=
  persistence.floorWitness_pos

end ExactLogMassNormalizedLossFlow

end YMGap.Continuum.ExactLogMassNormalizedLossPersistence

#print axioms YMGap.Continuum.ExactLogMassNormalizedLossPersistence.ExactLogMassNormalizedLossFlow.uniformExactFloor
#print axioms YMGap.Continuum.ExactLogMassNormalizedLossPersistence.ExactLogMassNormalizedLossFlow.exactPhysicalSeparatorCertificate
#print axioms YMGap.Continuum.ExactLogMassNormalizedLossPersistence.ExactLogMassNormalizedLossFlow.exactPhysicalSeparatorCertificate_floor_pos
