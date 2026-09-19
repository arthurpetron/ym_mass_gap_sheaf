/-
# An observable-connected path out of the dynamic completed BF4 sector

The dynamic completed-family interface retains the actual completed transfer,
vacuum complement, and same-object autocorrelation at every physical scale.
`PhysicalSeparator`, however, is phrased in terms of rational magnitudes of
connected correlations for one cutoff-independent observable type.  This file
gives the missing compiler between those two currencies.

`DynamicVacuumSectorObservablePin` is the honest semantic input.  It chooses
one observable type, sends every observable into the definitionally same
completed vacuum complement at every scale, and identifies rational squared
connected correlators with the literal squared completed autocorrelations.
Rational norm-square pins and a scale-uniform fourth-power amplitude then let
the already-proved completed contraction control those correlators.  A named
nonzero local observable prevents the interface from being inhabited by an
empty or zero channel.

The resulting separator uses the actual completed norm rate `q_j`.  The
completed theorem gives the sharper squared rate `(q_j*q_j)^n`; monotonicity on
`0 <= q_j < 1` weakens this to `q_j^n`, so an existing two-sided physical rate
band transfers without changing its mass currency.  Spacing-to-zero also
constructs the required scheduled physical-time sampling.

No observable pin, dynamic family, physical rate band, projective continuum
measure, OS identification, continuum Yang--Mills theory, or Clay conclusion
is inhabited here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealLog
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.SpectralDiffBoundClose

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.SpectralDiffBoundClose
open YMGap.Constructive.RegularCReal

/-! ## 1. The same-object observable pin -/

/-- A non-vacuous, cutoff-connected interpretation of one observable type in
the actual completed BF4 vacuum sectors.

The two equality fields are the load-bearing same-object pins.  They state
that the rational correlation and norm data are not unrelated numerical
majorants: after embedding into `RC`, they are exactly the squared completed
autocorrelation and completed norm of `vectorAt scale O`.  The uniform
fourth-power amplitude is an observable normalization bound, not a decay
hypothesis; time decay is derived below from `family.completedGap`.

Strict positivity of the completed rates is named separately because the
source-independent completed-family interface only needs nonnegativity,
whereas `PhysicalSeparator` deliberately excludes the zero separator. -/
structure DynamicVacuumSectorObservablePin
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  Obs : Type
  GaugeInvariantLocal : Obs -> Prop
  vectorAt : (scale : Nat) -> Obs ->
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) half
  connectedCorrSq : Nat -> Obs -> Nat -> Q'
  connectedCorrSq_nonnegative : forall scale O n,
    (0 : Q') <= connectedCorrSq scale O n
  normSq : Nat -> Obs -> Q'
  normSq_nonnegative : forall scale O, (0 : Q') <= normSq scale O
  normSq_pin : forall scale O,
    Quotient.mk CReal.crealSetoid (CReal.ofQ' (normSq scale O)) =
      centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (vectorAt scale O).1 (vectorAt scale O).1
  connectedCorrSq_pin : forall scale O n,
    Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (connectedCorrSq scale O n)) =
      CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (family.nome_pos scale) (family.nome_lt_one scale)
          half n (vectorAt scale O).1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (family.nome_pos scale) (family.nome_lt_one scale)
          half n (vectorAt scale O).1)
  amplitude : Obs -> Q'
  amplitude_pos : forall O, GaugeInvariantLocal O ->
    (0 : Q') < amplitude O
  normFourth_le_amplitude : forall scale O, GaugeInvariantLocal O ->
    normSq scale O * normSq scale O <= amplitude O
  rate_pos : forall scale,
    (0 : Q') < (family.completedGap scale).rate
  gapObservable : Obs
  gapObservable_local : GaugeInvariantLocal gapObservable
  gapObservable_zero_pos : forall scale,
    (0 : Q') < connectedCorrSq scale gapObservable 0

namespace DynamicVacuumSectorObservablePin

private theorem RCmul_ofQ'
    (left right : Q') :
    CReal.RCmul
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' left))
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' right)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (left * right)) := by
  rw [CReal.RCmul_mk]
  exact Quotient.sound
    (CReal.Equiv.symm (CRealAlg.ofQ'_mul left right))

/-! ## 2. Compile the literal completed moment estimate -/

/-- Reflection of the completed `RC` estimate back to the pinned rational
correlator.  The right side is still the sharper squared-rate bound. -/
theorem connectedCorrSq_le_rateSq_normFourth
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (scale : Nat) (O : pin.Obs) (n : Nat) :
    pin.connectedCorrSq scale O n <=
      ((((family.completedGap scale).rate *
          (family.completedGap scale).rate) ^ n) * pin.normSq scale O) *
        pin.normSq scale O := by
  have hdecay := family.completedAutocorrelation_sq_decay
    scale n (pin.vectorAt scale O)
  rw [<- pin.connectedCorrSq_pin scale O n,
      <- pin.normSq_pin scale O,
      RCscale_ofQ', RCmul_ofQ'] at hdecay
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hdecay

/-- On a nonnegative subunit completed rate, the sharper squared base is at
most the original rate. -/
theorem rateSq_le_rate
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (_pin : DynamicVacuumSectorObservablePin family)
    (scale : Nat) :
    (family.completedGap scale).rate *
        (family.completedGap scale).rate <=
      (family.completedGap scale).rate := by
  let rate := (family.completedGap scale).rate
  have hscaled : rate * rate <= rate * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left rate 1 rate
      (Q'.le_of_lt (family.completedGap scale).rate_lt_one)
      (family.completedGap scale).rate_nonnegative
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.mul_one_eqv rate))

/-- The literal pinned squared connected correlator is controlled by the
actual completed norm rate and the supplied uniform observable amplitude. -/
theorem connectedCorrSq_control
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (O : pin.Obs) (hO : pin.GaugeInvariantLocal O)
    (scale n : Nat) :
    pin.connectedCorrSq scale O n <=
      pin.amplitude O * ((family.completedGap scale).rate ^ n) := by
  let rate := (family.completedGap scale).rate
  let norm := pin.normSq scale O
  have hraw := pin.connectedCorrSq_le_rateSq_normFourth scale O n
  have hreassociate :
      ((((rate * rate) ^ n) * norm) * norm) <=
        ((rate * rate) ^ n) * (norm * norm) :=
    Q'.le_of_eqv (Q'.mul_assoc_eqv ((rate * rate) ^ n) norm norm)
  have hrateSqNonnegative : (0 : Q') <= rate * rate :=
    Q'.mul_nonneg rate rate
      (family.completedGap scale).rate_nonnegative
      (family.completedGap scale).rate_nonnegative
  have hpow : (rate * rate) ^ n <= rate ^ n :=
    CRealLog.pow_le_pow_base (rate * rate) rate
      hrateSqNonnegative (pin.rateSq_le_rate scale) n
  have hnormFourthNonnegative : (0 : Q') <= norm * norm :=
    Q'.mul_nonneg norm norm
      (pin.normSq_nonnegative scale O)
      (pin.normSq_nonnegative scale O)
  have hratePowerNonnegative : (0 : Q') <= rate ^ n :=
    Q'.pow_nonneg rate
      (family.completedGap scale).rate_nonnegative n
  have hpowerScaled :
      ((rate * rate) ^ n) * (norm * norm) <=
        (rate ^ n) * (norm * norm) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hnormFourthNonnegative
  have hamplitudeScaled :
      (rate ^ n) * (norm * norm) <=
        (rate ^ n) * pin.amplitude O :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (pin.normFourth_le_amplitude scale O hO)
      hratePowerNonnegative
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hreassociate
      (Q'.le_trans' _ _ _ hpowerScaled
        (Q'.le_trans' _ _ _ hamplitudeScaled
          (Q'.le_of_eqv
            (Q'.mul_comm_eqv (rate ^ n) (pin.amplitude O))))))

/-! ## 3. The physical separator and its dimensional rate band -/

/-- The rational squared completed autocorrelations, controlled by the
definitionally same completed norm rate, form a genuine physical separator. -/
def toPhysicalSeparator
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family) :
    PhysicalSeparator where
  corrIface := {
    Obs := pin.Obs
    GaugeInvariantLocal := pin.GaugeInvariantLocal
    connectedCorr := pin.connectedCorrSq
    connectedCorr_nonneg := pin.connectedCorrSq_nonnegative
  }
  sep := fun scale => (family.completedGap scale).rate
  sep_pos := pin.rate_pos
  sep_lt_one := fun scale => (family.completedGap scale).rate_lt_one
  controlsGaugeInvariantCorr := fun O hO =>
    ⟨pin.amplitude O, pin.amplitude_pos O hO,
      pin.connectedCorrSq_control O hO⟩

/-- A two-sided band for the same completed rate becomes the genuine
two-sided `PhysicalGapFloor` of the observable-connected separator. -/
def toPhysicalGapFloor
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    PhysicalGapFloor pin.toPhysicalSeparator
      family.transferSpacing.spacing
      family.transferSpacing.spacing_pos where
  c := band.floor
  c_pos := band.floor_pos
  floor := fun scale => by
    change band.floor <= family.physicalGap scale
    exact band.floor_le_physicalGap scale
  ceil := band.ceiling
  finiteness := fun scale => by
    change family.physicalGap scale <= band.ceiling
    exact band.physicalGap_le_ceiling scale

/-! ## 4. Forward/backward meet at the regular scaling band -/

/-- The same observable-connected physical rate band feeds the regular-real
continuum pipeline through the physical separator.  The per-spacing cluster
bound is `physClusterBound pin.toPhysicalSeparator scale`; no bare heat-kernel
separator is substituted. -/
def toRegScalingBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    RegScalingBand :=
  RGGapPersistence.toScalingBand
    (PhysicalSeparator.toRGGapPersistence
      (pin.toPhysicalGapFloor band))

@[simp] theorem toRegScalingBand_physGapMin
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    (pin.toRegScalingBand band).physGapMin = band.floor := rfl

/-- The forward completed estimate and the backward regular-real compiler
meet in a strictly positive uniform physical floor. -/
theorem toRegScalingBand_physGapMin_pos
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    (0 : Q') < (pin.toRegScalingBand band).physGapMin :=
  RGGapPersistence.physGapMin_pos_of_persistence
    (PhysicalSeparator.toRGGapPersistence
      (pin.toPhysicalGapFloor band))

/-- The resulting regular-real gap is uniformly bounded below at every
spacing index, still for the same separator and same completed transfer. -/
theorem toRegScalingBand_gap_survives
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (scale : Nat) :
    ofQ' (pin.toRegScalingBand band).physGapMin ≤
      ofQ' ((pin.toRegScalingBand band).physGap scale) :=
  RGGapPersistence.continuum_gap_of_RGGapPersistence
    (PhysicalSeparator.toRGGapPersistence
      (pin.toPhysicalGapFloor band)) scale

/-- The regular-real compiler also preserves the finite physical-rate ceiling. -/
theorem toRegScalingBand_gap_le_ceiling
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (scale : Nat) :
    ofQ' ((pin.toRegScalingBand band).physGap scale) ≤
      ofQ' (pin.toRegScalingBand band).physGapMax :=
  RGGapPersistence.continuum_gap_le_ceiling_of_RGGapPersistence
    (PhysicalSeparator.toRGGapPersistence
      (pin.toPhysicalGapFloor band)) scale

/-- The already-available spacing-to-zero modulus constructs the correct
scheduled powers `n_j(t)` with `a_j n_j(t) -> t`; no fixed-one-step limit is
used. -/
def physicalSampling
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (_pin : DynamicVacuumSectorObservablePin family) :
    PhysicalSeparationSampling family.transferSpacing :=
  physicalSeparationSamplingOfSpacingToZero
    family.transferSpacing family.transferSpacingToZero

/-- The distinguished local channel remains visibly nonzero in the generated
physical-separator correlator interface at every cutoff. -/
theorem physicalSeparator_gapObservable_zero_pos
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (scale : Nat) :
    (0 : Q') <
      pin.toPhysicalSeparator.corrIface.connectedCorr
        scale pin.gapObservable 0 :=
  pin.gapObservable_zero_pos scale

end DynamicVacuumSectorObservablePin

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.connectedCorrSq_le_rateSq_normFourth
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.rateSq_le_rate
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.connectedCorrSq_control
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toPhysicalSeparator
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toPhysicalGapFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toRegScalingBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toRegScalingBand_physGapMin_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toRegScalingBand_gap_survives
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.toRegScalingBand_gap_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.physicalSampling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath.DynamicVacuumSectorObservablePin.physicalSeparator_gapObservable_zero_pos
