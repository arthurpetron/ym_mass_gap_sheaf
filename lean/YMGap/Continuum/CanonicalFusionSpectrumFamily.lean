/-
Track 11.7-fusion / R3s -- arbitrary-positive-exponent spectrum family.

# Result

`FusionSpectrumBlockingDictionary` already accepts a scale-dependent physical
fusion exponent `pGamma k >= 2`, but its generic interface repeats three pins.
The later p=2 specialization proved that two of them are structural once the
physical separator is defined by the selected fusion spectrum:

* `finePin` is reflexivity;
* `imagePin` is the symmetric form of `BlockingStep.step`.

This module performs that reduction for an arbitrary all-cutoff family of
completed `CanonicalBulkControl (pGamma k)` values.  Its only cross-scale
spectral input is the genuine fusion-power equality.  A second compiler moves
that equality to the exact `QPowerCell` integer cross product, uniformly in
the varying positive exponent.

The resulting carrier has a proved refinement to the existing canonical
`FusionSpectrumBlockingDictionary`; it is not a parallel frontier.  This file
does not construct the still-open analytic `CanonicalBulkControl` family.

# Constructivity

Pure structure compilation, `Q'` cross multiplication, and the existing
constructive-real rational embedding.  No `Classical`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2RetunedFusionPowerCertificate

namespace YMGap.Continuum.CanonicalFusionSpectrumFamily

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionSpectrumBlockingIdentification
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux

/-! ## 1. The all-cutoff positive-exponent canonical family -/

/-- Completed canonical physical fusion controls at every scale, with the
physical bond-moving exponent allowed to vary but remaining at least two.
The analytic content is exactly the existing `CanonicalBulkControl`; this
wrapper introduces no new estimate. -/
structure CanonicalBulkControlFamily : Type where
  N : Nat -> Nat
  w : Nat -> Q'
  pGamma : Nat -> Nat
  pGamma_ge_two : forall k, 2 <= pGamma k
  control : (k : Nat) -> CanonicalBulkControl (N k) (w k) (pGamma k)

/-- The selected normalized fusion eigenvalue before its constructive-real
embedding. -/
def canonicalFusionModeQ (F : CanonicalBulkControlFamily)
    (mode : Nat -> Nat) (k : Nat) : Q' :=
  fusionEig (F.N k) (F.w k) (F.pGamma k) (mode k)
    ((F.control k).denomPos (mode k))

/-- Canonical physical separator obtained directly from the selected mode of
the completed positive-exponent fusion spectrum. -/
def canonicalFusionSeparator (F : CanonicalBulkControlFamily)
    (mode : Nat -> Nat) (k : Nat) : CReal :=
  fusionModeCReal (F.control k) (mode k)

/-- On the spectrum-defined trajectory the fine pin is definitional, for an
arbitrary scale-dependent `pGamma >= 2`. -/
theorem canonicalFusionSeparator_finePin
    (F : CanonicalBulkControlFamily) (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv (canonicalFusionSeparator F mode (k + 1))
      (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) := by
  unfold canonicalFusionSeparator
  exact equivRefl _

/-- The map-image pin is already the symmetric physical blocking-step law;
it is not independent analytic data. -/
theorem canonicalFusionSeparator_imagePin
    (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator F mode)) (k : Nat) :
    CReal.Equiv (B.Φ (canonicalFusionSeparator F mode (k + 1)))
      (fusionModeCReal (F.control k) (mode k)) := by
  simpa only [canonicalFusionSeparator] using (B.step k).symm

/-! ## 2. One genuine fusion-power pin and the canonical dictionary -/

/-- Minimal positive-exponent physical spectrum interface.  Support and bulk
membership remain explicit; `finePin` and `imagePin` have been eliminated.
The sole equality field is the actual adjacent-scale fusion-power law. -/
structure CanonicalSpectrumFusionPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  modeSupport : forall k, mode k <= 2 * F.N k
  modeBulk : forall k,
    BulkModeCrux.q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  fusionPower : forall k,
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (cpow (fusionModeCReal (F.control (k + 1)) (mode (k + 1)))
        (b + 1))

/-- Refinement to the reviewed generic dictionary.  Both former map pins are
filled by theorems about the same spectrum-defined physical separator. -/
def CanonicalSpectrumFusionPowerData.toDictionary
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumFusionPowerData b F mode B) :
    FusionSpectrumBlockingDictionary b
      (canonicalFusionSeparator F mode) B where
  N := F.N
  w := F.w
  pGamma := F.pGamma
  pGamma_ge_two := F.pGamma_ge_two
  control := F.control
  mode := mode
  modeBulk := D.modeBulk
  finePin := canonicalFusionSeparator_finePin F mode
  imagePin := canonicalFusionSeparator_imagePin F mode B
  fusionPower := D.fusionPower

/-- The one-pin positive-exponent family reaches the genuine physical
trajectory power law through the canonical dictionary. -/
theorem CanonicalSpectrumFusionPowerData.blockPowerOnTrajectory
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumFusionPowerData b F mode B) :
    IsBlockPowerOnTrajectory b (canonicalFusionSeparator F mode) B.Φ :=
  D.toDictionary.blockPowerOnTrajectory

/-- Every selected coarse mode is localized by its same-scale completed
canonical control. -/
theorem CanonicalSpectrumFusionPowerData.coarseLocalized
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumFusionPowerData b F mode B) (k : Nat) :
    fusionEig (F.N k) (F.w k) (F.pGamma k) (mode k)
        ((F.control k).denomPos (mode k)) <= eigA (F.w k) 1 :=
  D.toDictionary.coarseLocalized k

/-! ## 3. Exact cross-multiplied fusion-power certificates -/

/-- A generic rational power cell lifts to the exact constructive-real
fusion-power field, independently of the value of `pGamma k`. -/
theorem canonicalFusionPower_of_cell
    {b : Nat} {F : CanonicalBulkControlFamily}
    {mode : Nat -> Nat} {k : Nat}
    (C : QPowerCell (canonicalFusionModeQ F mode k)
      (canonicalFusionModeQ F mode (k + 1)) (b + 1)) :
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (cpow (fusionModeCReal (F.control (k + 1)) (mode (k + 1)))
        (b + 1)) := by
  have hlift :
      CReal.Equiv (CReal.ofQ' (canonicalFusionModeQ F mode k))
        (CReal.ofQ'
          (qpow (canonicalFusionModeQ F mode (k + 1)) (b + 1))) :=
    CReal.ofQ'_equiv_of_eqv C.eqv
  exact CReal.Equiv.trans
    (by simpa only [fusionModeCReal, canonicalFusionModeQ] using hlift)
    (CReal.Equiv.symm (by
      simpa only [fusionModeCReal, canonicalFusionModeQ] using
        (cpow_ofQ' (canonicalFusionModeQ F mode (k + 1)) (b + 1))))

/-- Preferred proof-about-computation carrier for a varying physical
`pGamma >= 2` family.  Each fusion-power equality is represented by its exact
integer cross product. -/
structure CanonicalSpectrumCrossMulPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  modeSupport : forall k, mode k <= 2 * F.N k
  modeBulk : forall k,
    BulkModeCrux.q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  fusionPowerCell : forall k,
    QPowerCell (canonicalFusionModeQ F mode k)
      (canonicalFusionModeQ F mode (k + 1)) (b + 1)

/-- Exact integer cells supply the only remaining fusion-power field. -/
def CanonicalSpectrumCrossMulPowerData.toFusionPowerData
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumCrossMulPowerData b F mode B) :
    CanonicalSpectrumFusionPowerData b F mode B where
  modeSupport := D.modeSupport
  modeBulk := D.modeBulk
  fusionPower := fun k => canonicalFusionPower_of_cell (D.fusionPowerCell k)

/-- Cross-multiplied arbitrary-positive-exponent cells refine all the way to
the reviewed fusion-spectrum dictionary. -/
def CanonicalSpectrumCrossMulPowerData.toDictionary
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumCrossMulPowerData b F mode B) :
    FusionSpectrumBlockingDictionary b
      (canonicalFusionSeparator F mode) B :=
  D.toFusionPowerData.toDictionary

/-- The reflected integer cells reach the genuine `BlockingStep.Phi`
trajectory identification with no separately supplied fine or image pin. -/
theorem CanonicalSpectrumCrossMulPowerData.blockPowerOnTrajectory
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumCrossMulPowerData b F mode B) :
    IsBlockPowerOnTrajectory b (canonicalFusionSeparator F mode) B.Φ :=
  D.toFusionPowerData.blockPowerOnTrajectory

/-! ## 4. The existing p=2 family is a literal specialization -/

/-- Embed the current retuned p=2 control family into the general
positive-exponent family. -/
def CanonicalBulkControlFamily.ofP2Retuned
    (F : P2RetunedControlFamily) : CanonicalBulkControlFamily where
  N := F.N
  w := F.w
  pGamma := fun _ => 2
  pGamma_ge_two := fun _ => by decide
  control := F.control

/-- The generic rational mode is definitionally the existing p=2 mode. -/
theorem canonicalFusionModeQ_ofP2Retuned
    (F : P2RetunedControlFamily) (mode : Nat -> Nat) (k : Nat) :
    canonicalFusionModeQ (CanonicalBulkControlFamily.ofP2Retuned F) mode k =
      fusionModeQ F mode k := rfl

/-- The generic spectrum separator is definitionally the reviewed p=2
separator, so this generalization does not create a second physical object. -/
theorem canonicalFusionSeparator_ofP2Retuned
    (F : P2RetunedControlFamily) (mode : Nat -> Nat) (k : Nat) :
    canonicalFusionSeparator (CanonicalBulkControlFamily.ofP2Retuned F)
        mode k =
      fusionSeparator F mode k := rfl

end YMGap.Continuum.CanonicalFusionSpectrumFamily

#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.canonicalFusionSeparator_finePin
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.canonicalFusionSeparator_imagePin
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.CanonicalSpectrumFusionPowerData.toDictionary
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.CanonicalSpectrumFusionPowerData.blockPowerOnTrajectory
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.canonicalFusionPower_of_cell
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.CanonicalSpectrumCrossMulPowerData.toDictionary
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.CanonicalSpectrumCrossMulPowerData.blockPowerOnTrajectory
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.canonicalFusionModeQ_ofP2Retuned
#print axioms YMGap.Continuum.CanonicalFusionSpectrumFamily.canonicalFusionSeparator_ofP2Retuned
