/-
# Cutoff-one reflected local-face projective certificate

The corrected-slab local face kernel sends a four-spin packet to a retained
coarse spin after summing its two pair channels.  Fusion zeros prevent this
one-step rectangular matrix from being strictly positive on either full
centre-parity sector.

This file passes to the smallest reflection-compatible square primitive:

    G(s,t) = sum_packet K(packet,s) K(packet,t).

At cutoff one and coupling one, exact reduction gives

    G =
      [11  0  36  0  10
        0  80  0  64  0
       36  0 135  0  45
        0  64  0  64  0
       10  0  45  0  25].

Consequently both parity blocks are strictly positive.  Their exact maximal
cross-ratios are 11/4 and 5/4; the conservative common spread 11/4 gives the
rational Birkhoff candidate 7/15.

This is a fixed-cutoff local certificate.  It does not identify the Gram
primitive with an iterated physical RG step, prove the analytic
Birkhoff--Hopf contraction theorem, or supply a cutoff-uniform diameter.

## Axiom gate

Finite exact-rational reduction only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.CompactDualCutoffOneLocalFaceGramCertificate

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

local infix:50 " ≈ " => Q'.eqv

/-- The literal cutoff-one face weight at the projectively convenient
coupling `w = 1`.  Changing positive `w` only rescales target columns. -/
def cutoffOneFaceWeight
    (packet : FaceSpinPacket) (retainedSpin : Nat) : Q' :=
  fixedFinalFaceRawWeight 1 packet retainedSpin

/-- The reflection/SOS Gram primitive of the exact local face matrix. -/
def cutoffOneReflectedFaceGram (left right : Nat) : Q' :=
  listQSum
    (fun packet =>
      cutoffOneFaceWeight packet left *
        cutoffOneFaceWeight packet right)
    (faceSpinPacketStateSpace 1)

def cutoffOneEvenSpins : List Nat := [0, 2, 4]

def cutoffOneOddSpins : List Nat := [1, 3]

/-- Exact evaluation of the complete five-by-five Gram matrix. -/
theorem cutoffOneReflectedFaceGram_table :
    (List.range 5).map
        (fun left =>
          (List.range 5).map
            (fun right => cutoffOneReflectedFaceGram left right)) =
      [[11, 0, 36, 0, 10],
       [0, 80, 0, 64, 0],
       [36, 0, 135, 0, 45],
       [0, 64, 0, 64, 0],
       [10, 0, 45, 0, 25]] := by
  decide

/-- The even centre-parity block has exact conservative spread `11/4`. -/
def cutoffOneEvenGramCertificate :
    FiniteCrossRatioDiameterCertificate
      cutoffOneReflectedFaceGram
      cutoffOneEvenSpins cutoffOneEvenSpins where
  spread := Q'.mkPos 11 4 (by decide)
  one_le_spread := by decide
  strictlyPositive := by
    intro source hsource target htarget
    simp only [cutoffOneEvenSpins, List.mem_cons,
      List.not_mem_nil, or_false] at hsource htarget
    rcases hsource with rfl | rfl | rfl <;>
      rcases htarget with rfl | rfl | rfl <;> decide
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    simp only [cutoffOneEvenSpins, List.mem_cons,
      List.not_mem_nil, or_false] at hfirst hsecond hleft hright
    rcases hfirst with rfl | rfl | rfl <;>
      rcases hsecond with rfl | rfl | rfl <;>
        rcases hleft with rfl | rfl | rfl <;>
          rcases hright with rfl | rfl | rfl <;> decide

/-- The odd centre-parity block has the sharper exact spread `5/4`. -/
def cutoffOneOddGramCertificate :
    FiniteCrossRatioDiameterCertificate
      cutoffOneReflectedFaceGram
      cutoffOneOddSpins cutoffOneOddSpins where
  spread := Q'.mkPos 5 4 (by decide)
  one_le_spread := by decide
  strictlyPositive := by
    intro source hsource target htarget
    simp only [cutoffOneOddSpins, List.mem_cons,
      List.not_mem_nil, or_false] at hsource htarget
    rcases hsource with rfl | rfl <;>
      rcases htarget with rfl | rfl <;> decide
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    simp only [cutoffOneOddSpins, List.mem_cons,
      List.not_mem_nil, or_false] at hfirst hsecond hleft hright
    rcases hfirst with rfl | rfl <;>
      rcases hsecond with rfl | rfl <;>
        rcases hleft with rfl | rfl <;>
          rcases hright with rfl | rfl <;> decide

/-- The exact common cutoff-one candidate rate is `7/15`. -/
theorem cutoffOneEvenGramCandidateRate :
    cutoffOneEvenGramCertificate.candidateRate ≈
      Q'.mkPos 7 15 (by decide) := by
  decide

theorem cutoffOneOddGramCandidateRate :
    cutoffOneOddGramCertificate.candidateRate ≈
      Q'.mkPos 1 9 (by decide) := by
  decide

#print axioms cutoffOneReflectedFaceGram_table
#print axioms cutoffOneEvenGramCertificate
#print axioms cutoffOneOddGramCertificate
#print axioms cutoffOneEvenGramCandidateRate
#print axioms cutoffOneOddGramCandidateRate

end YMGap.Continuum.CompactDualCutoffOneLocalFaceGramCertificate
