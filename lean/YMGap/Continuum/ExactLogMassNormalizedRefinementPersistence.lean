/-
M3c -- exact-log handoff for a refinement-indexed mass-normalized flow.

This is the AF-oriented companion to `ExactLogMassNormalizedPersistence`.
Increasing scale indices now move toward finer spacings, as recorded by

  a_k = b_k a_(k+1).

The structure identifies those spacings pointwise with one exact constructive
log-rate family and requires each rational mass certificate to lie below the
corresponding exact rate.  A constructive summable-loss persistence witness
therefore transports to a uniform exact-log floor.  An independently proved
upper ceiling then gives the full exact physical separator certificate.

The refinement step, normalized loss budget, and rational-to-exact comparison
remain named inputs.  No BF4 producer or continuum reconstruction is supplied.
-/

import YMGap.Continuum.MassNormalizedRefinementPersistence
import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.MassNormalizedRefinementPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-- A refinement-indexed rational RG flow certified below one exact physical
log-rate family.  The spacing identification rules out an auxiliary-scale
substitution. -/
structure ExactLogMassNormalizedRefinementFlow
    (P : PhysicalSeparator) : Type 1 where
  exactRate : FullRangeExactPhysicalLogRateFamily P
  rationalFlow : MassNormalizedRefinementFlow
  spacing_identification : forall k : Nat,
    (rationalFlow.spacing k).eqv
      (exactRate.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (rationalFlow.mass k)) (exactRate.rate k)

namespace ExactLogMassNormalizedRefinementFlow

variable {P : PhysicalSeparator}

/-- A persistent rational refinement flow supplies a uniform lower floor for
the same exact logarithmic rates. -/
def uniformExactFloor
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
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
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
    (flow.uniformExactFloor persistence).floor =
      persistence.floorWitness := rfl

theorem uniformExactFloor_floor_pos
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
    (0 : Q') < (flow.uniformExactFloor persistence).floor :=
  persistence.floorWitness_pos

/-- Add an independent exact upper ceiling to the RG-derived exact floor. -/
def exactPhysicalSeparatorCertificate
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    FullRangeExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := flow.exactRate
  uniformFloor := flow.uniformExactFloor persistence
  finiteCeiling := ceiling

@[simp] theorem exactPhysicalSeparatorCertificate_separator
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).separator =
      P := rfl

@[simp] theorem exactPhysicalSeparatorCertificate_floor
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor =
      persistence.floorWitness := rfl

theorem exactPhysicalSeparatorCertificate_floor_pos
    (flow : ExactLogMassNormalizedRefinementFlow P)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (ceiling : FullRangeLogRateCeiling flow.exactRate) :
    (0 : Q') <
      (flow.exactPhysicalSeparatorCertificate persistence ceiling).uniformFloor.floor :=
  persistence.floorWitness_pos

end ExactLogMassNormalizedRefinementFlow

end YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence

#print axioms YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence.ExactLogMassNormalizedRefinementFlow.uniformExactFloor
#print axioms YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence.ExactLogMassNormalizedRefinementFlow.exactPhysicalSeparatorCertificate
#print axioms YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence.ExactLogMassNormalizedRefinementFlow.exactPhysicalSeparatorCertificate_floor_pos
