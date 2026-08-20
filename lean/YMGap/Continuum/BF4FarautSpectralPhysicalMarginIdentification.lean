/-
M4c -- isolate the exact physical/spectral same-object seam.

The wired `SpectralMarginInput` defines its rational rate from the cluster
floor stored in `input.atSpacing`.  The BF4 continuum route defines its
rational proxy from the physical separator `P`.  Equality of those two
numerators is not a consequence of spacing identification, the one-sided
spectral recursion, or the BF4 lower-floor certificate.

This file names that remaining same-object statement and proves that, together
with the already-wired spacing identification, it gives the exact equality of
the two rational proxy rates.  It separately names the eventual reverse drift
needed for Cauchy control.  Neither analytic input is constructed here.
-/

import YMGap.Continuum.BF4FarautSpectralMarginInputExactCertificate

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}

namespace BF4FarautSpectralMarginInputExactFlow

private theorem qeqv_of_le_of_ge {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a.eqv b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

/-- Positive rational division respects semantic equivalence in both inputs. -/
private theorem divPos_eqv_congr {a a' d d' : Q'}
    (hd : (0 : Q') < d) (hd' : (0 : Q') < d')
    (ha : a.eqv a') (hden : d.eqv d') :
    (Q'.divPos a d hd).eqv (Q'.divPos a' d' hd') := by
  apply qeqv_of_le_of_ge
  · apply Q'.le_divPos_of_mul_le a' d' hd'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a d hd) d' d
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a d hd) ha))
  · apply Q'.le_divPos_of_mul_le a d hd
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' d' hd') d d' hden)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' d' hd')
          (Q'.eqv_symm ha)))

/-- The cluster floor carried by `SpectralMarginInput` is the physical margin
of the same separator used by the BF4/Faraut exact-rate family. -/
structure PhysicalMarginIdentification
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀) : Type 1 where
  floorRate_eq_physMargin : forall k : Nat,
    ((flow.input.atSpacing k).floorRate).eqv (P.physMargin k)

namespace PhysicalMarginIdentification

/-- The physical separator proxy and the spectral cluster-floor rate coincide.
The numerator identity is the explicit same-object input; the denominator
identity is already part of the exact BF4/Faraut flow. -/
theorem marginRate_eqv_input
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀}
    (identification : PhysicalMarginIdentification flow) (k : Nat) :
    (marginRate P producer.fullRangeRateFamily.physicalSpacing k).eqv
      (flow.input.g k) := by
  unfold marginRate SpectralMarginInput.g
  exact divPos_eqv_congr
    (producer.fullRangeRateFamily.physicalSpacing.spacing_pos k)
    (flow.input.spacing_pos k)
    (Q'.eqv_symm (identification.floorRate_eq_physMargin k))
    (Q'.eqv_symm (flow.spacing_identification k))

end PhysicalMarginIdentification

/-- A symmetric companion to `SpectralMarginInput.hadd`.  The existing field
proves that the next rate cannot fall by more than `shift`; this field says
that it cannot rise by more than the same shift.  Analytically, it is the
missing lower half of a two-sided eigenvalue perturbation estimate. -/
structure SymmetricSpectralShift
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀) : Type 1 where
  reverseHadd : forall k : Nat,
    flow.input.g (k + 1) - flow.input.shift k ≤ flow.input.g k

namespace SymmetricSpectralShift

private theorem le_add_of_sub_le {a b c : Q'} (h : a - c ≤ b) :
    a ≤ b + c := by
  have hstep : (a + -c) + c ≤ b + c :=
    Q'.add_le_add_right (a + -c) b c h
  have hcollapse : ((a + -c) + c).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-c) c) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (-c + c) 0 (Q'.neg_add_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hstep

/-- The symmetric spectral shift and the existing `hbridge` imply the upper
additive drift by the already-defined normalized loss. -/
theorem reverseStep
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀}
    (symmetric : SymmetricSpectralShift flow) (k : Nat) :
    flow.input.g (k + 1) ≤
      flow.input.g k + flow.input.toMassNormalizedLossFlow.rateLoss k := by
  have hshift : flow.input.shift k ≤ flow.input.normalizedLoss k :=
    flow.input.hbridge k
  have hbase : flow.input.g (k + 1) ≤
      flow.input.g k + flow.input.shift k :=
    le_add_of_sub_le (symmetric.reverseHadd k)
  have hloss : (flow.input.toMassNormalizedLossFlow.rateLoss k).eqv
      (flow.input.normalizedLoss k) :=
    flow.input.rateLoss_eqv_normalizedLoss k
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_add_left _ _ _
      (Q'.le_trans' _ _ _ hshift (Q'.ge_of_eqv hloss)))

end SymmetricSpectralShift

/-- The still-missing upper drift of the rational spectral rate, named only on
the tail where the exact logarithmic comparison will use it.  The existing
`SpectralMarginInput` recursion proves the opposite additive direction. -/
structure EventualUpperMarginDrift
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (start : Nat) : Type 1 where
  reverseStep : forall j : Nat, start ≤ j ->
    flow.input.g (j + 1) ≤
      flow.input.g j + flow.input.toMassNormalizedLossFlow.rateLoss j

namespace SymmetricSpectralShift

/-- A symmetric shift estimate supplies the eventual upper drift from any
chosen start; no additional tail argument is required. -/
def toEventualUpperMarginDrift
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀}
    (symmetric : SymmetricSpectralShift flow) (start : Nat) :
    EventualUpperMarginDrift flow start where
  reverseStep := fun j _ => symmetric.reverseStep j

end SymmetricSpectralShift

end BF4FarautSpectralMarginInputExactFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.PhysicalMarginIdentification.marginRate_eqv_input
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.SymmetricSpectralShift.reverseStep
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.SymmetricSpectralShift.toEventualUpperMarginDrift
