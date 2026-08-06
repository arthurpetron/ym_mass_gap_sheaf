/-
Track 11.7-fusion / R2f -- a genuine positive-exponent finite certificate.

# Result

This module supplies the first closed physical `pGamma >= 2` data point for the
reviewed canonical bulk carrier:

```text
N = 3,  w = 11/12,  pGamma = 2,  weff = 23/25.
```

All seven modes in the exact support window `s <= 2*N` are checked by Lean's
kernel evaluator.  The witness is not the vacuous `weff = 1` endpoint: mode
`s = 2` satisfies the effective-bulk premise, so the proved canonical consumer
has a concrete physical mode on which to act.

The computation is deliberately small and transparent.  It uses `decide`, not
`native_decide`, and it does not claim an all-cutoff or all-weight theorem.  It
closes one exact near-continuum fence cell and demonstrates that the reviewed
`CanonicalBulkControl` is genuinely inhabitable at positive bond-moving
exponent.

# Constructivity

Pure `Nat`/`Q'` kernel computation.  No `Classical`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.RebasedBulkLocalizationBridge

namespace YMGap.Continuum.PhysicalP2FiniteCertificate

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkShift
open YMGap.Continuum.RebasedExpShiftSupportReduction
open YMGap.Continuum.RebasedBulkLocalizationBridge

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The exact rational effective heat weight selected for the physical fence
cell.  It is high enough for every re-based shift check, but remains below
`15/16`, leaving the effective bulk nonempty at mode `s = 2`. -/
def fenceWeff : Q' := Q'.mkPos 23 25 (by decide)

theorem fenceWeff_nonneg : (0 : Q') <= fenceWeff := by decide

theorem fenceWeff_le_one : fenceWeff <= (1 : Q') := by decide

/-- **The seven exact rational certificate atoms.**  At the physical
near-continuum fence `(N,w,pGamma) = (3,11/12,2)`, the actual normalized fusion
eigenvalue stays within `1/12` above the re-based heat rate on every mode in its
full support window. -/
theorem fenceFiniteShift_atom (s : Nat) (hs : s <= 2 * 3) :
    fusionEig 3 fenceW 2 s (fenceDenomPos s) - rateP fenceWeff s <= q112 := by
  cases s with
  | zero => decide
  | succ s =>
      cases s with
      | zero => decide
      | succ s =>
          cases s with
          | zero => decide
          | succ s =>
              cases s with
              | zero => decide
              | succ s =>
                  cases s with
                  | zero => decide
                  | succ s =>
                      cases s with
                      | zero => decide
                      | succ s =>
                          cases s with
                          | zero => decide
                          | succ s => omega

/-- The genuine `pGamma = 2` finite exponential-shift certificate data. -/
def fenceFiniteShift :
    FiniteExpShiftBridge 3 fenceW 2 fenceWeff fenceDenomPos where
  rebasedBulkShift := fenceFiniteShift_atom

/-- **First closed positive-exponent canonical bulk-control cell.**  Every field
is physical data at the same cutoff, heat weight, and bond-moving exponent; no
abstract saddle or exponential residual remains at this cell. -/
def fenceCanonicalBulkControl : CanonicalBulkControl 3 fenceW 2 where
  hN := by decide
  hp := by decide
  hw0 := fenceW_nonneg
  hw1 := fenceW_le_one
  hnc := fenceW_near_continuum
  denomPos := fenceDenomPos
  weff := fenceWeff
  hweff0 := fenceWeff_nonneg
  hweff1 := fenceWeff_le_one
  finiteShift := fenceFiniteShift

/-- **Anti-vacuity witness.**  Mode two is genuinely in the effective bulk for
`weff = 23/25`; hence the canonical localization consumer is not protected by
an empty bulk premise at this positive-exponent cell. -/
theorem fenceModeTwo_isBulk :
    q12 <= Q'.ofNat (c4 2) * ((1 : Q') - fenceWeff) := by decide

/-- Concrete output of the canonical physical localization theorem at the
nonempty mode-two bulk witness. -/
theorem fenceFusionEig_two_below_gapEdge :
    fusionEig 3 fenceW 2 2 (fenceDenomPos 2) <= eigA fenceW 1 :=
  fenceCanonicalBulkControl.bulk_below_gapEdge 2 fenceModeTwo_isBulk

end YMGap.Continuum.PhysicalP2FiniteCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.PhysicalP2FiniteCertificate.fenceFiniteShift_atom
#print axioms YMGap.Continuum.PhysicalP2FiniteCertificate.fenceCanonicalBulkControl
#print axioms YMGap.Continuum.PhysicalP2FiniteCertificate.fenceModeTwo_isBulk
#print axioms YMGap.Continuum.PhysicalP2FiniteCertificate.fenceFusionEig_two_below_gapEdge
