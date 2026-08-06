/-
Track 11.7-fusion / R2g -- the genuine fusion-spectrum-to-blocking-map dictionary.

# Statement repair

The earlier conditional transport asked one single-scale localization inequality
to imply a global identity

```text
forall x : CReal, blockingStep.Phi x ~= x^(b+1).
```

That implication cannot be obtained from finite rational spectrum data: the
premise neither defines `Phi` nor constrains it away from the physical separator
trajectory.  This module records the actual cross-scale dictionary required by
the proof:

1. at every scale, a genuine positive-exponent `CanonicalBulkControl`;
2. a selected effective-bulk fusion mode;
3. the next physical separator pinned to the next-scale fusion eigenvalue;
4. `blockingStep.Phi` on that separator pinned to the coarse fusion eigenvalue;
5. the exact power identity between that coarse fusion value and the physical
   next-scale separator.

The last two fields compose to the trajectory-only power law, which is proved in
`BlockingStepFrontier` to be sufficient for the continuum consumer.  Thus this
is a genuine identification interface: it names the exact equalities that must
be proved for the physical block map, instead of pretending a localization
inequality determines an arbitrary global function.

# Honesty boundary

The dictionary is not inhabited here for four-dimensional Yang--Mills.  The
new `PhysicalP2FiniteCertificate` closes one single-scale `pGamma=2` control
cell; constructing the all-scale controls and the two exact map pins remains
the physical RG problem.  The final transport below is a proved refinement to
the existing physical continuum-floor consumer.

# Constructivity

Pure `Q'`/`CReal` composition.  No `Classical`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.PhysicalP2FiniteCertificate
import YMGap.Continuum.CanonicalBulkBlockPowerTransport

namespace YMGap.Continuum.FusionSpectrumBlockingIdentification

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CodynamicCRealFlow

/-- A selected mode of one canonical fusion certificate, embedded as a
constructive real. -/
def fusionModeCReal {N : Nat} {w : Q'} {p : Nat}
    (C : CanonicalBulkControl N w p) (s : Nat) : CReal :=
  CReal.ofQ' (fusionEig N w p s (C.denomPos s))

/-- Natural powers respect constructive-real equivalence.  This small
congruence makes the fine fusion pin load-bearing in the exact cross-scale
power identity below. -/
theorem cpow_equiv {x y : CReal} (h : CReal.Equiv x y) :
    forall n : Nat, CReal.Equiv (cpow x n) (cpow y n)
  | 0 => BlockingStepFrontier.equivRefl CReal.cone
  | n + 1 =>
      CReal.Equiv.trans (CReal.mul_congr_left (cpow_equiv h n))
        (CReal.Equiv.trans
          (CRealAlg.cmul_comm (cpow y n) x)
          (CReal.Equiv.trans (CReal.mul_congr_left h)
            (CRealAlg.cmul_comm y (cpow y n))))

/-- **The genuine cross-scale fusion-spectrum/blocking-map dictionary.**

Every scale carries its own cutoff, bare heat weight, positive physical fusion
exponent, and completed canonical finite certificate.  The three equality fields
pin the next physical separator, the image of the actual blocking map, and the
exact power law to the same adjacent pair of fusion spectra. -/
structure FusionSpectrumBlockingDictionary
    (b : Nat) (physSep : Nat -> CReal)
    (blockingStep : BlockingStep physSep) : Type where
  /-- Cutoff at every RG scale. -/
  N : Nat -> Nat
  /-- Bare heat weight at every RG scale. -/
  w : Nat -> Q'
  /-- Physical bond-moving exponent at every RG scale. -/
  pGamma : Nat -> Nat
  /-- The physical branch stays beyond the unperturbed `pGamma=1` anchor. -/
  pGamma_ge_two : forall k, 2 <= pGamma k
  /-- Completed physical canonical fusion control at every scale. -/
  control : (k : Nat) -> CanonicalBulkControl (N k) (w k) (pGamma k)
  /-- The fusion mode representing the physical gap separator at each scale. -/
  mode : Nat -> Nat
  /-- The selected coarse mode is in the effective bulk, so its localization
  verdict is a theorem of the same canonical certificate. -/
  modeBulk : forall k,
    q12 <= Q'.ofNat (c4 (mode k)) * ((1 : Q') - (control k).weff)
  /-- **Fine pin.**  The physical next-scale separator is the selected
  next-scale normalized fusion eigenvalue. -/
  finePin : forall k,
    CReal.Equiv (physSep (k + 1))
      (fusionModeCReal (control (k + 1)) (mode (k + 1)))
  /-- **Map pin.**  Applying the genuine physical blocking map to the fine
  separator gives the selected coarse normalized fusion eigenvalue. -/
  imagePin : forall k,
    CReal.Equiv (blockingStep.Φ (physSep (k + 1)))
      (fusionModeCReal (control k) (mode k))
  /-- **Exact fusion power identity.**  The selected coarse fusion eigenvalue
  is the `(b+1)`-power of the selected next-scale fusion eigenvalue.  The
  `finePin` then transports this to the physical fine separator.  This is an
  equality, not the localization inequality supplied by `control`. -/
  fusionPower : forall k,
    CReal.Equiv (fusionModeCReal (control k) (mode k))
      (cpow (fusionModeCReal (control (k + 1)) (mode (k + 1))) (b + 1))

/-- The dictionary's selected coarse fusion mode is genuinely localized below
the original heat-kernel gap edge at every scale. -/
theorem FusionSpectrumBlockingDictionary.coarseLocalized
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    (D : FusionSpectrumBlockingDictionary b physSep B) (k : Nat) :
    fusionEig (D.N k) (D.w k) (D.pGamma k) (D.mode k)
        ((D.control k).denomPos (D.mode k)) <= eigA (D.w k) 1 :=
  (D.control k).bulk_below_gapEdge (D.mode k) (D.modeBulk k)

/-- **Genuine identification to the sharp power law.**  The map pin and exact
fusion power identity compose at each physical separator input. -/
theorem FusionSpectrumBlockingDictionary.blockPowerOnTrajectory
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    (D : FusionSpectrumBlockingDictionary b physSep B) :
    IsBlockPowerOnTrajectory b physSep B.Φ :=
  fun k => CReal.Equiv.trans (D.imagePin k)
    (CReal.Equiv.trans (D.fusionPower k) (cpow_equiv (D.finePin k).symm (b + 1)))

/-- The genuine dictionary closes the full self-similar separator law. -/
theorem FusionSpectrumBlockingDictionary.selfSimilar
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    (D : FusionSpectrumBlockingDictionary b physSep B) :
    selfSimilarC b physSep :=
  selfSimilarC_of_blockingPowerOnTrajectory B D.blockPowerOnTrajectory

/-- Physical continuum transport whose sole map-identification input is the
genuine cross-scale fusion dictionary above. -/
structure FusionSpectrumBlockingTransport (b : Nat) : Type where
  hb : 1 <= b
  physSep : Nat -> CReal
  blockingStep : BlockingStep physSep
  dictionary : FusionSpectrumBlockingDictionary b physSep blockingStep
  sepNonneg : forall k, ExpPos.geRat (physSep k) 0
  sepLeOne : forall k, CReal.leRat (physSep k) 1
  floor0 : Q'
  floor0_pos : (0 : Q') < floor0
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (CodynamicPhysFloor.physGapC b physSep (RateMatchFloor.geomSpacing b) 0)

/-- The genuine fusion-spectrum dictionary builds the existing physical RG
input through the trajectory-level green consumer. -/
def FusionSpectrumBlockingTransport.physicalRGInput {b : Nat}
    (T : FusionSpectrumBlockingTransport b) : PhysicalRGInput :=
  physicalRGInput_of_blockingPowerOnTrajectory T.hb T.physSep T.blockingStep
    T.dictionary.blockPowerOnTrajectory T.sepNonneg T.sepLeOne T.floor0
    T.floor0_pos T.hbase0

/-- The genuine fusion-spectrum dictionary reaches the spacing-uniform
constructive-real continuum floor. -/
def FusionSpectrumBlockingTransport.continuumGap {b : Nat}
    (T : FusionSpectrumBlockingTransport b) :
    UnifiedContinuumFloor.CRealFloor
      (CodynamicPhysFloor.physGapC b T.physSep (RateMatchFloor.geomSpacing b)) :=
  physicalGap_of_blockingPowerOnTrajectory T.hb T.physSep T.blockingStep
    T.dictionary.blockPowerOnTrajectory T.sepNonneg T.sepLeOne T.floor0
    T.floor0_pos T.hbase0

end YMGap.Continuum.FusionSpectrumBlockingIdentification

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.FusionSpectrumBlockingDictionary.coarseLocalized
#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.cpow_equiv
#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.FusionSpectrumBlockingDictionary.blockPowerOnTrajectory
#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.FusionSpectrumBlockingDictionary.selfSimilar
#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.FusionSpectrumBlockingTransport.physicalRGInput
#print axioms YMGap.Continuum.FusionSpectrumBlockingIdentification.FusionSpectrumBlockingTransport.continuumGap
