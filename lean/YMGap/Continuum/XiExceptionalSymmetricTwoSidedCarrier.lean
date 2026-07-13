/-
# Symmetric exact two-sided original carrier

If the original left residual is path-unsafe but the original right residual
is path-safe, the two payload slots can be exchanged: right residual in the
terminal background, left residual externally.  A constructive terminal-mask
replacement transforms this orientation back to the canonical two-sided
code, proving injectivity without duplicating the path-side decoder.
-/

import YMGap.Continuum.XiExceptionalReversePathTagFence

namespace YMGap.Continuum.XiExceptionalSymmetricTwoSidedCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def originalSymmetricTwoSidedCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (rightPathResidual Gamma qP b1 b2 entry)
    (leftPathResidual Gamma qP b1 b2 entry)

theorem originalSymmetricTwoSidedCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry _ _

def OriginalRightResidualPathSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  ∀ X, X ∈ path.polymerWalk.vertices →
    ∀ T, T ∈ selectByBits Gamma
      (rightPathResidual Gamma qP b1 b2 entry) →
      compatibleB X T = true

theorem originalSymmetricTwoSidedCarrierCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : OriginalRightResidualPathSafe Gamma qP b1 b2 entry) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let leftResidual := leftPathResidual Gamma qP b1 b2 entry
  let rightResidual := rightPathResidual Gamma qP b1 b2 entry
  have hleftSub : ∀ i, leftResidual.at i = true →
      entry.1.1.at i = true :=
    leftPathResidual_submask_left Gamma qP b1 b2 entry
  have hrightSub : ∀ i, rightResidual.at i = true →
      entry.1.2.at i = true :=
    rightPathResidual_submask_right Gamma qP b1 b2 entry
  have hcode := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry rightResidual leftResidual
    (exceptional_right_submask_compatible Gamma qP b1 b2 entry
      rightResidual hrightSub)
    (exceptional_right_submask_q Gamma qP b1 b2 entry
      rightResidual hrightSub)
    hsafe
    (exceptional_left_submask_compatible Gamma qP b1 b2 entry
      leftResidual hleftSub)
    (exceptional_left_submask_q Gamma qP b1 b2 entry
      leftResidual hleftSub)
  have hsource := occurrencePairWeight_eqv_original_path_residuals
    w qP b1 b2 Gamma label entry
  dsimp only at hcode hsource
  unfold originalSymmetricTwoSidedCarrierCode
  refine Q'.eqv_trans _ _ _ hcode ?_
  refine Q'.eqv_trans _
    (path.polymerWalk.activityWeight w label *
      (familyActivity w (selectByBits Gamma rightResidual) label *
        familyActivity w (selectByBits Gamma leftResidual) label)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (path.polymerWalk.activityWeight w label *
      (familyActivity w (selectByBits Gamma leftResidual) label *
        familyActivity w (selectByBits Gamma rightResidual) label)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv _ _)
  · exact Q'.eqv_symm hsource

/-! ## Payload-orientation normalization -/

def replaceTerminalBackground : OccChainCode n → OccBitVec n → OccChainCode n
  | .terminal _, background => .terminal background
  | .step next rest, background =>
      .step next (replaceTerminalBackground rest background)

theorem replaceTerminalBackground_ofWalk
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (old new : OccBitVec n) :
    replaceTerminalBackground (occurrenceChainCodeOfWalk walk old) new =
      occurrenceChainCodeOfWalk walk new := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [occurrenceChainCodeOfWalk, replaceTerminalBackground]
      rw [ih]

def transposeCarrierPayload (code : OccCarrierXiCodeAt Gamma) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := code.carrier.start
        chain := replaceTerminalBackground code.carrier.chain code.external }
    external := terminalBackground code.carrier.chain }

theorem transpose_symmetric_eq_original
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    transposeCarrierPayload
        (originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry) =
      originalTwoSidedCarrierCode Gamma qP b1 b2 entry := by
  unfold transposeCarrierPayload originalSymmetricTwoSidedCarrierCode
    originalTwoSidedCarrierCode exceptionalCustomCarrierCode
  dsimp only
  rw [replaceTerminalBackground_ofWalk,
    terminalBackground_occurrenceChainCodeOfWalk]

theorem originalSymmetricTwoSidedCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry1 =
      originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have htrans := congrArg transposeCarrierPayload hcode
  rw [transpose_symmetric_eq_original Gamma qP b1 b2 entry1,
    transpose_symmetric_eq_original Gamma qP b1 b2 entry2] at htrans
  exact originalTwoSidedCarrierCode_injective Gamma qP b1 b2
    entry1 entry2 htrans

/-! ## Duplicate-free regional summation -/

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem originalSymmetricTwoSidedPathSafe_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hsafe : ∀ entry, entry ∈ source →
      OriginalRightResidualPathSafe Gamma qP b1 b2 entry) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun entry => [originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry])
  · rw [flatMap_singleton_eq_map]
    apply nodup_map_of_injOn _ source hsource
    intro a _ b _ hcode
    exact originalSymmetricTwoSidedCarrierCode_injective
      Gamma qP b1 b2 a b hcode
  · intro code hcode
    obtain ⟨entry, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact originalSymmetricTwoSidedCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry hentry
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (originalSymmetricTwoSidedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry (hsafe entry hentry))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms originalSymmetricTwoSidedCarrierCode_mem
#print axioms originalSymmetricTwoSidedCarrierCode_weight_eqv_source
#print axioms replaceTerminalBackground_ofWalk
#print axioms transpose_symmetric_eq_original
#print axioms originalSymmetricTwoSidedCarrierCode_injective
#print axioms originalSymmetricTwoSidedPathSafe_region_global_bound

end YMGap.Continuum.XiExceptionalSymmetricTwoSidedCarrier
