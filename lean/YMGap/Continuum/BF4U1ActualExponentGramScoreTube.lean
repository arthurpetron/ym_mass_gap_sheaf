/-
# Retained-charge tube for the actual finite U(1) exponent-Gram score

This module constructs an `AtlasScoreTube` for the literal
`atlasU1ExponentGramScore` at fixed BF4 geometry, fine coupling, outer
fine-charge carrier, and finite exponent-coordinate list.

Both entries in every absolute Gram discrepancy are approximated:

* the blocked entry is masked after its exact pullback to the normalized fine
  U(1) slab;
* the coarse entry is masked on its candidate-dependent normalized coarse
  U(1) slab.

The per-entry tolerance pays a factor of two and the finite coordinate
cardinality.  Candidate-dependent coarse state counts are handled by an
explicit recursive maximum over the finite positive coupling atlas.  No
candidate-independence of the blocked or coarse definitions is assumed.

## Honest scope

The outer `fineChargeCutoff` and exponent-coordinate list are fixed.  The
new cutoff removes only the internal retained-charge mask.  Thus this is not
an all-label outer-carrier limit, a spacing-uniform estimate as the nome tends
to one, a weak-coupling separator, or a physical AF trajectory.

All constructions are finite and exact over `Q'`.  There is no
`Classical.*`, `Real`, `native_decide`, custom axiom, noncomputable
declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff
import YMGap.Continuum.BF4U1FiniteExponentGramTailTube

namespace YMGap.Continuum.BF4U1ActualExponentGramScoreTube

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ExponentGramLocatedStability
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1SignedChargeTailInstantiation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite-score inequalities -/

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: rest, hbound => by
      have hhead := hbound head List.mem_cons_self
      have hrest :=
        listQSum_le_length_mul_local value hbound0 rest
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value rest ≤
            bound + Q'.ofNat rest.length * bound :=
        Q'.add_le_add hhead hrest
      have htarget :
          bound + Q'.ofNat rest.length * bound ≈
            Q'.ofNat (head :: rest).length * bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound ((1 : Q') * bound)
            (Q'.ofNat rest.length * bound)
            (Q'.eqv_symm (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv 1 (Q'.ofNat rest.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv 1 (Q'.ofNat rest.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv rest.length))
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv htarget)

private theorem sub_add_rearrange
    (a a' b b' : Q') :
    ((a + a') + (-(b + b'))) ≈
      ((a + (-b)) + (a' + (-b'))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (a + a') _ _ (Q'.neg_add_eqv b b')) ?_
  exact Q'.add_swap_inner a a' (-b) (-b')

private theorem pair_difference_rearrange
    (blocked coarse blockedCutoff coarseCutoff : Q') :
    ((blocked + (-coarse)) +
        (-(blockedCutoff + (-coarseCutoff)))) ≈
      (blocked + (-blockedCutoff)) +
        (coarseCutoff + (-coarse)) := by
  refine Q'.eqv_trans _ _ _
    (sub_add_rearrange
      blocked (-coarse) blockedCutoff (-coarseCutoff)) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-coarse)
      (-(-coarseCutoff)) coarseCutoff
      (Q'.neg_neg_eqv coarseCutoff)) ?_
  exact Q'.add_comm_eqv (-coarse) coarseCutoff

/-- Changing both entries of one absolute Gram discrepancy costs the sum of
the two entry errors. -/
theorem abs_gram_discrepancy_lipschitz
    (blocked coarse blockedCutoff coarseCutoff : Q') :
    Q'.abs
        (Q'.abs
            (blockedCutoff + (-coarseCutoff)) +
          (-Q'.abs (blocked + (-coarse)))) ≤
      Q'.abs (blocked + (-blockedCutoff)) +
        Q'.abs (coarse + (-coarseCutoff)) := by
  let fullDifference := blocked + (-coarse)
  let cutoffDifference := blockedCutoff + (-coarseCutoff)
  have habs :
      Q'.abs
          (Q'.abs cutoffDifference +
            (-Q'.abs fullDifference)) ≤
        Q'.abs (cutoffDifference + (-fullDifference)) := by
    have hone :=
      YMGap.Continuum.BF4U1FiniteExponentGramTailTube.abs_distance_to_reference_lipschitz
        cutoffDifference fullDifference 0
    have hcutoff :
        Q'.abs cutoffDifference ≈
          Q'.abs (cutoffDifference + (-(0 : Q'))) :=
      Q'.abs_eqv_congr
        (Q'.eqv_symm
          (Q'.eqv_of_eq
            (Q'.add_zero' cutoffDifference)))
    have hfull :
        Q'.abs fullDifference ≈
          Q'.abs (fullDifference + (-(0 : Q'))) :=
      Q'.abs_eqv_congr
        (Q'.eqv_symm
          (Q'.eqv_of_eq
            (Q'.add_zero' fullDifference)))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (Q'.add_eqv_congr'
            hcutoff (Q'.neg_eqv_congr _ _ hfull)))) ?_
    exact hone
  have hrearrange :
      (cutoffDifference + (-fullDifference)) ≈
        (blockedCutoff + (-blocked)) +
          (coarse + (-coarseCutoff)) := by
    refine Q'.eqv_trans _ _ _
      (pair_difference_rearrange
        blockedCutoff coarseCutoff blocked coarse) ?_
    exact Q'.add_eqv_congr_left
      (blockedCutoff + (-blocked))
      (coarse + (-coarseCutoff))
      (coarse + (-coarseCutoff))
      (Q'.eqv_refl _)
  have htriangle :
      Q'.abs (cutoffDifference + (-fullDifference)) ≤
        Q'.abs (blockedCutoff + (-blocked)) +
          Q'.abs (coarse + (-coarseCutoff)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hrearrange))
      (Q'.abs_add_le'
        (blockedCutoff + (-blocked))
        (coarse + (-coarseCutoff)))
  have hblocked :
      Q'.abs (blockedCutoff + (-blocked)) ≤
        Q'.abs (blocked + (-blockedCutoff)) :=
    Q'.le_of_eqv
      (YMGap.Constructive.ExpNeg.abs_sub_comm
        blockedCutoff blocked)
  exact Q'.le_trans' _ _ _ habs
    (Q'.le_trans' _ _ _ htriangle
      (Q'.add_le_add_right _ _ _
        hblocked))

/-! ## 2. The doubly masked actual U(1) score -/

/-- One retained-charge discrepancy coordinate.  Both the exact blocked
fine-pullback and the candidate-dependent coarse law are masked. -/
def retainedU1ExponentGramCoordinateDistance
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (retainedCharge : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  Q'.abs
    (u1BlockedExponentGramCoordinateChargeCutoff
        G g hg fineChargeCutoff coordinate retainedCharge +
      (-u1ExponentGramCoordinateChargeCutoff
        (coarseU1Data G candidate hcandidate fineChargeCutoff)
        coordinate retainedCharge))

/-- Finite-coordinate retained version of the literal
`u1ExponentGramDistance`. -/
def retainedU1ExponentGramDistance
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (retainedCharge : Nat)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  listQSum
    (retainedU1ExponentGramCoordinateDistance
      G g hg candidate hcandidate fineChargeCutoff retainedCharge)
    coordinates

/-- Atlas score obtained by replacing both entries of the actual U(1)
exponent-Gram distance by their retained-charge versions. -/
def retainedAtlasU1ExponentGramScore
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff retainedCharge : Nat)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    retainedU1ExponentGramDistance
      G g hg candidate (atlas.candidate_pos hcandidate)
      fineChargeCutoff retainedCharge coordinates
  else 0

theorem retainedAtlasU1ExponentGramScore_of_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff retainedCharge : Nat)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    retainedAtlasU1ExponentGramScore
        G g hg atlas fineChargeCutoff retainedCharge
        coordinates candidate =
      retainedU1ExponentGramDistance
        G g hg candidate (atlas.candidate_pos hcandidate)
        fineChargeCutoff retainedCharge coordinates := by
  unfold retainedAtlasU1ExponentGramScore
  rw [dif_pos hcandidate]

/-! ## 3. Explicit tolerance and finite-atlas maximum -/

/-- Per-entry tolerance after paying two changing Gram entries and reserving
one extra positive coordinate unit. -/
def twoEntryCoordinateTolerance
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Q' :=
  YMGap.Continuum.HKConv.divPos ε
    (Q'.ofNat (2 * (coordinates.length + 1)))

theorem twoEntryCoordinateTolerance_pos
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < twoEntryCoordinateTolerance coordinates ε :=
  YMGap.Continuum.HKConv.divPos_pos
    (CReal.num_pos_of_pos hε)

theorem twoEntryCoordinateScale_mul_tolerance_eqv
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') :
    Q'.ofNat (2 * (coordinates.length + 1)) *
        twoEntryCoordinateTolerance coordinates ε ≈
      ε := by
  unfold twoEntryCoordinateTolerance
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (Q'.ofNat (2 * (coordinates.length + 1)))
      (YMGap.Continuum.HKConv.divPos ε
        (Q'.ofNat (2 * (coordinates.length + 1))))) ?_
  exact YMGap.Continuum.HKConv.divPos_mul_eqv
    (CReal.num_pos_of_pos
      (by
        apply Q'.ofNat_succ_pos
          (2 * (coordinates.length + 1) - 1)))

/-- Candidate-wise cutoff paying both the normalized fine pullback and that
candidate's normalized coarse slab state count. -/
def candidateRetainedChargeCutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  max
    (signedChargeCarrierCutoff
      (fineU1Data G g hg fineChargeCutoff)
      (twoEntryCoordinateTolerance coordinates ε))
    (signedChargeCarrierCutoff
      (coarseU1Data G candidate hcandidate fineChargeCutoff)
      (twoEntryCoordinateTolerance coordinates ε))

/-- Candidate cutoffs with their constructive positivity proofs retained
through the explicit atlas head and attached tail. -/
def atlasCandidateRetainedChargeCutoffs
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : List Nat :=
  candidateRetainedChargeCutoff
      G g hg atlas.head atlas.head_pos
      fineChargeCutoff coordinates ε ::
    atlas.tail.attach.map (fun candidate =>
      candidateRetainedChargeCutoff
        G g hg candidate.1
        (atlas.tail_pos candidate.1 candidate.2)
        fineChargeCutoff coordinates ε)

/-- One common internal retained-charge cutoff for the whole finite atlas. -/
def atlasRetainedChargeCutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  YMGap.Continuum.BF4U1FiniteExponentGramTailTube.listNatMax
    (atlasCandidateRetainedChargeCutoffs
      G g hg atlas fineChargeCutoff coordinates ε)

theorem candidateRetainedChargeCutoff_le_atlas
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q')
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    candidateRetainedChargeCutoff
        G g hg candidate (atlas.candidate_pos hcandidate)
        fineChargeCutoff coordinates ε ≤
      atlasRetainedChargeCutoff
        G g hg atlas fineChargeCutoff coordinates ε := by
  apply
    YMGap.Continuum.BF4U1FiniteExponentGramTailTube.le_listNatMax_of_mem
  unfold PositiveCouplingAtlas.candidates at hcandidate
  rcases List.mem_cons.mp hcandidate with hhead | htail
  · subst candidate
    exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact
      ⟨⟨candidate, htail⟩,
        by simp,
        by simp only⟩

/-! ## 4. Pointwise score modulus and the actual atlas tube -/

theorem retainedU1ExponentGramDistance_abs_modulus
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      candidateRetainedChargeCutoff
          G g (Q'.le_of_lt hg0) candidate hcandidate
          fineChargeCutoff coordinates ε ≤
        M) :
    Q'.abs
        (retainedU1ExponentGramDistance
            G g (Q'.le_of_lt hg0) candidate hcandidate
            fineChargeCutoff M coordinates +
          (-u1ExponentGramDistance
            G g (Q'.le_of_lt hg0) candidate hcandidate
            fineChargeCutoff coordinates)) ≤
      ε := by
  let δ := twoEntryCoordinateTolerance coordinates ε
  have hδpos : (0 : Q') < δ :=
    twoEntryCoordinateTolerance_pos coordinates hε
  have hfineCutoff :
      signedChargeCarrierCutoff
          (fineU1Data G g (Q'.le_of_lt hg0)
            fineChargeCutoff) δ ≤
        M := by
    exact Nat.le_trans
      (Nat.le_max_left _ _)
      hM
  have hcoarseCutoff :
      signedChargeCarrierCutoff
          (coarseU1Data G candidate hcandidate
            fineChargeCutoff) δ ≤
        M := by
    exact Nat.le_trans
      (Nat.le_max_right _ _)
      hM
  have hsum :=
    abs_listQSum_sub_le
      (retainedU1ExponentGramCoordinateDistance
        G g (Q'.le_of_lt hg0) candidate hcandidate
        fineChargeCutoff M)
      (fun coordinate =>
        Q'.abs
          (u1BlockedExponentGramEntry
              G g (Q'.le_of_lt hg0)
              candidate hcandidate fineChargeCutoff coordinate +
            (-u1CoarseExponentGramEntry
              G candidate hcandidate
              fineChargeCutoff coordinate)))
      coordinates
  refine Q'.le_trans' _ _ _ hsum ?_
  have hpoint :
      ∀ coordinate,
        coordinate ∈ coordinates →
        Q'.abs
            (retainedU1ExponentGramCoordinateDistance
                G g (Q'.le_of_lt hg0)
                candidate hcandidate fineChargeCutoff M coordinate +
              (-Q'.abs
                (u1BlockedExponentGramEntry
                    G g (Q'.le_of_lt hg0)
                    candidate hcandidate fineChargeCutoff coordinate +
                  (-u1CoarseExponentGramEntry
                    G candidate hcandidate
                    fineChargeCutoff coordinate)))) ≤
          δ + δ := by
    intro coordinate _
    have hblocked :=
      u1BlockedExponentGramCoordinateSignedChargeCutoff_modulus
        G g hg0 hg1 candidate hcandidate
        fineChargeCutoff coordinate δ hδpos M hfineCutoff
    have hcoarse :=
      u1ExponentGramCoordinateSignedChargeCutoff_modulus
        (coarseU1Data G candidate hcandidate fineChargeCutoff)
        hcandidate hcandidate1 coordinate
        δ hδpos M hcoarseCutoff
    exact Q'.le_trans' _ _ _
      (abs_gram_discrepancy_lipschitz
        (u1BlockedExponentGramEntry
          G g (Q'.le_of_lt hg0)
          candidate hcandidate fineChargeCutoff coordinate)
        (u1CoarseExponentGramEntry
          G candidate hcandidate fineChargeCutoff coordinate)
        (u1BlockedExponentGramCoordinateChargeCutoff
          G g (Q'.le_of_lt hg0)
          fineChargeCutoff coordinate M)
        (u1ExponentGramCoordinateChargeCutoff
          (coarseU1Data G candidate hcandidate fineChargeCutoff)
          coordinate M))
      (Q'.add_le_add hblocked hcoarse)
  have hfinite :
      listQSum
          (fun coordinate =>
            Q'.abs
              (retainedU1ExponentGramCoordinateDistance
                  G g (Q'.le_of_lt hg0)
                  candidate hcandidate fineChargeCutoff M coordinate +
                (-Q'.abs
                  (u1BlockedExponentGramEntry
                      G g (Q'.le_of_lt hg0)
                      candidate hcandidate fineChargeCutoff coordinate +
                    (-u1CoarseExponentGramEntry
                      G candidate hcandidate
                      fineChargeCutoff coordinate)))))
          coordinates ≤
        Q'.ofNat coordinates.length * (δ + δ) :=
    listQSum_le_length_mul_local
      _ (Q'.zero_le_add _ _
        (Q'.le_of_lt hδpos) (Q'.le_of_lt hδpos))
      coordinates hpoint
  have hcountEqv :
      Q'.ofNat coordinates.length * (δ + δ) ≈
        Q'.ofNat (coordinates.length + coordinates.length) * δ := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat coordinates.length) δ δ) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (Q'.ofNat coordinates.length)
          (Q'.ofNat coordinates.length) δ)) ?_
    exact Q'.mul_eqv_congr_right _ _ δ
      (Q'.eqv_symm
        (Q'.ofNat_add_eqv
          coordinates.length coordinates.length))
  have hcount :
      Q'.ofNat (coordinates.length + coordinates.length) * δ ≤
        Q'.ofNat (2 * (coordinates.length + 1)) * δ :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (CReal.ofNat_le_ofNat (by omega))
      (Q'.le_of_lt hδpos)
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcountEqv)
      (Q'.le_trans' _ _ _ hcount
        (Q'.le_of_eqv
          (twoEntryCoordinateScale_mul_tolerance_eqv
            coordinates ε))))

theorem retainedAtlasU1ExponentGramScore_abs_modulus
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate, candidate ∈ atlas.candidates →
        candidate < (1 : Q'))
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    Q'.abs
        (retainedAtlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
            (atlasRetainedChargeCutoff
              G g (Q'.le_of_lt hg0) atlas
              fineChargeCutoff coordinates ε)
            coordinates candidate +
          (-atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas
            fineChargeCutoff coordinates candidate)) ≤
      ε := by
  rw [
    retainedAtlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
      (atlasRetainedChargeCutoff
        G g (Q'.le_of_lt hg0) atlas
        fineChargeCutoff coordinates ε)
      coordinates candidate hcandidate,
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
      coordinates candidate hcandidate
  ]
  exact retainedU1ExponentGramDistance_abs_modulus
    G g hg0 hg1 candidate
    (atlas.candidate_pos hcandidate)
    (hatlas1 candidate hcandidate)
    fineChargeCutoff coordinates ε hε
    (atlasRetainedChargeCutoff
      G g (Q'.le_of_lt hg0) atlas
      fineChargeCutoff coordinates ε)
    (candidateRetainedChargeCutoff_le_atlas
      G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
      coordinates ε candidate hcandidate)

/-- Actual score tube for the literal U(1) exponent-Gram atlas score, with
both its blocked and coarse entries internally charge-masked. -/
def actualU1ExponentGramAtlasScoreTube
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (hatlas1 :
      ∀ candidate, candidate ∈ atlas.candidates →
        candidate < (1 : Q'))
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε) :
    AtlasScoreTube atlas
      (retainedAtlasU1ExponentGramScore
        G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
        (atlasRetainedChargeCutoff
          G g (Q'.le_of_lt hg0) atlas
          fineChargeCutoff coordinates ε)
        coordinates)
      (atlasU1ExponentGramScore
        G g (Q'.le_of_lt hg0) atlas
        fineChargeCutoff coordinates)
      ε :=
  atlasScoreTubeOfAbs
    atlas
    (retainedAtlasU1ExponentGramScore
      G g (Q'.le_of_lt hg0) atlas fineChargeCutoff
      (atlasRetainedChargeCutoff
        G g (Q'.le_of_lt hg0) atlas
        fineChargeCutoff coordinates ε)
      coordinates)
    (atlasU1ExponentGramScore
      G g (Q'.le_of_lt hg0) atlas
      fineChargeCutoff coordinates)
    ε (Q'.le_of_lt hε)
    (retainedAtlasU1ExponentGramScore_abs_modulus
      G g hg0 hg1 atlas hatlas1
      fineChargeCutoff coordinates ε hε)

end YMGap.Continuum.BF4U1ActualExponentGramScoreTube

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1ActualExponentGramScoreTube.abs_gram_discrepancy_lipschitz
#print axioms YMGap.Continuum.BF4U1ActualExponentGramScoreTube.retainedU1ExponentGramDistance_abs_modulus
#print axioms YMGap.Continuum.BF4U1ActualExponentGramScoreTube.retainedAtlasU1ExponentGramScore_abs_modulus
#print axioms YMGap.Continuum.BF4U1ActualExponentGramScoreTube.actualU1ExponentGramAtlasScoreTube
