/-
# Geometric summation of canonical paired-peeling block profiles

The ordered block profile has one coordinate for every face/replica scan key.
Its coordinate sum is exactly the total peeled mass.  Hence every canonical
profile lies in a bounded product carrier, while the weight `(16/25)^M`
factorizes into one geometric series per coordinate.  This module supplies
the arithmetic and carrier facts used by the complete inverse-fiber estimate.

Constructive contract: structural list recursion and exact rational finite
sums only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact profile length and mass -/

theorem traceRankBlocks_length (faces : List Nat)
    (trace : List SlabAcceptedPairedPeelRecord) : forall count,
    (slabAcceptedPairedPeelTraceRankBlocks faces trace count).length = count
  | 0 => rfl
  | count + 1 => by
      simp only [slabAcceptedPairedPeelTraceRankBlocks,
        List.length_cons, traceRankBlocks_length faces trace count]

theorem traceRankMassProfile_length (faces : List Nat)
    (trace : List SlabAcceptedPairedPeelRecord) (count : Nat) :
    (slabAcceptedPairedPeelTraceRankMassProfile
      faces trace count).length = count := by
  unfold slabAcceptedPairedPeelTraceRankMassProfile
  rw [List.length_map, traceRankBlocks_length]

private theorem traceRankBlocks_cons_eq_of_count_le_rank
    (faces : List Nat) (head : SlabAcceptedPairedPeelRecord)
    (tail : List SlabAcceptedPairedPeelRecord) : forall count,
    count ≤ slabAcceptedPairScanRank faces (head.rootFaceId, head.left) ->
    slabAcceptedPairedPeelTraceRankBlocks faces (head :: tail) count =
      slabAcceptedPairedPeelTraceRankBlocks faces tail count
  | 0, _ => rfl
  | count + 1, hle => by
      unfold slabAcceptedPairedPeelTraceRankBlocks
      congr 1
      · unfold slabAcceptedPairedPeelTraceSizesAtRank
        have hne :
            slabAcceptedPairScanRank faces (head.rootFaceId, head.left) ≠
              count := by omega
        simp [hne]
      · exact traceRankBlocks_cons_eq_of_count_le_rank
          faces head tail count (by omega)

private theorem traceRankBlocks_cons_sum_of_rank_lt
    (faces : List Nat) (head : SlabAcceptedPairedPeelRecord)
    (tail : List SlabAcceptedPairedPeelRecord) : forall count,
    slabAcceptedPairScanRank faces (head.rootFaceId, head.left) < count ->
    natListSum
        ((slabAcceptedPairedPeelTraceRankBlocks
          faces (head :: tail) count).map natListSum) =
      head.peelSize +
        natListSum
          ((slabAcceptedPairedPeelTraceRankBlocks
            faces tail count).map natListSum)
  | 0, hlt => by omega
  | count + 1, hlt => by
      unfold slabAcceptedPairedPeelTraceRankBlocks
      simp only [List.map_cons, natListSum]
      by_cases heq :
          slabAcceptedPairScanRank faces (head.rootFaceId, head.left) = count
      · have hlower := traceRankBlocks_cons_eq_of_count_le_rank
          faces head tail count (by omega)
        rw [hlower]
        unfold slabAcceptedPairedPeelTraceSizesAtRank
        simp [heq, natListSum]
        omega
      · have hlower :
            slabAcceptedPairScanRank faces
              (head.rootFaceId, head.left) < count := by omega
        have ih := traceRankBlocks_cons_sum_of_rank_lt
          faces head tail count hlower
        unfold slabAcceptedPairedPeelTraceSizesAtRank
        simp [heq]
        rw [ih]
        omega

/-- If every trace rank is represented among the stored blocks, the profile
sum is exactly the total peeled mass. -/
theorem traceRankMassProfile_sum_eq_traceMass_of_rank_lt
    (faces : List Nat) : forall
    (trace : List SlabAcceptedPairedPeelRecord) (count : Nat),
    (forall record, record ∈ trace ->
      slabAcceptedPairScanRank faces
        (record.rootFaceId, record.left) < count) ->
    natListSum
        (slabAcceptedPairedPeelTraceRankMassProfile
          faces trace count) =
      slabAcceptedPairedPeelTraceMass trace
  | [], count, _ => by
      induction count with
      | zero => rfl
      | succ count ih =>
          simp only [slabAcceptedPairedPeelTraceRankMassProfile,
            slabAcceptedPairedPeelTraceRankBlocks,
            slabAcceptedPairedPeelTraceSizesAtRank, List.filter_nil,
            List.map_nil, List.map_cons, natListSum]
          have hih := ih (fun record hmem => by cases hmem)
          unfold slabAcceptedPairedPeelTraceRankMassProfile at hih
          simpa only [Nat.zero_add] using hih
  | head :: tail, count, hrange => by
      have hhead := hrange head List.mem_cons_self
      have htail : forall record, record ∈ tail ->
          slabAcceptedPairScanRank faces
            (record.rootFaceId, record.left) < count := by
        intro record hrecord
        exact hrange record (List.mem_cons_of_mem head hrecord)
      have ih := traceRankMassProfile_sum_eq_traceMass_of_rank_lt
        faces tail count htail
      unfold slabAcceptedPairedPeelTraceRankMassProfile at ih ⊢
      rw [traceRankBlocks_cons_sum_of_rank_lt faces head tail count hhead, ih]
      unfold slabAcceptedPairedPeelTraceMass
      rfl

/-- The canonical full profile assigns all and only the trace mass to the
`2 * faces.length` scan coordinates. -/
theorem slabAcceptedPairCanonicalPeeling_rankMassProfile_sum_eq_traceMass
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    natListSum
        (slabAcceptedPairedPeelTraceRankMassProfile faces
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical state).2 (2 * faces.length)) =
      slabAcceptedPairedPeelTraceMass
        (slabAcceptedPairCanonicalPeeling
          D faces hphysical state).2 := by
  apply traceRankMassProfile_sum_eq_traceMass_of_rank_lt
  intro record hrecord
  apply scanRank_lt_two_mul_length
  exact slabAcceptedPairCanonicalPeeling_trace_root_mem
    D faces hphysical state record hrecord

private theorem natListSum_member_le : forall
    (values : List Nat) (value : Nat),
    value ∈ values -> value ≤ natListSum values
  | [], _, hmem => by cases hmem
  | head :: tail, value, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst value
        simp only [natListSum]
        omega
      · have ih := natListSum_member_le tail value htail
        simp only [natListSum]
        omega

/-- Every canonical profile lies in the literal product carrier whose
coordinate ceiling is the common paired trace-mass ceiling. -/
theorem slabAcceptedPairCanonicalPeeling_rankMassProfile_mem_allSeqs
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedPairedPeelTraceRankMassProfile faces
        (slabAcceptedPairCanonicalPeeling
          D faces hphysical state).2 (2 * faces.length) ∈
      allSeqs (2 * slabObservableRemovalMaxSize D + 1)
        (2 * faces.length) := by
  apply mem_allSeqs
  · exact traceRankMassProfile_length _ _ _
  · intro mass hmass
    have hmember := natListSum_member_le _ mass hmass
    rw [slabAcceptedPairCanonicalPeeling_rankMassProfile_sum_eq_traceMass
      D faces hphysical state] at hmember
    have htrace := slabAcceptedPairCanonicalPeeling_traceMass_le
      D faces hphysical state
    omega

/-! ## 2. One geometric series per scan coordinate -/

private theorem qpow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : forall exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _
          (qpow_eqv_congr_local h exponent))

/-- The fixed-profile rate has the same finite `25/9` geometric envelope as
the earlier global `16/25` rate. -/
theorem pairedPeelSignatureEntropyAnchorRatio_fullTail_le
    (count : Nat) :
    listQSum
        (fun mass => pairedPeelSignatureEntropyAnchorRatio ^ mass)
        (List.range count) ≤ Q'.mkPos 25 9 (by decide) := by
  have hbase : pairedPeelSignatureEntropyAnchorRatio ≈
      slabObservablePairedGlobalEntropyAnchorRatio :=
    Q'.eqv_trans _ (Q'.mkPos 16 25 (by decide)) _
      pairedPeelSignatureEntropyAnchorRatio_eqv
      (Q'.eqv_symm slabObservablePairedGlobalEntropyAnchorRatio_eqv)
  have hsum :
      listQSum
          (fun mass => pairedPeelSignatureEntropyAnchorRatio ^ mass)
          (List.range count) ≈
        listQSum
          (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
          (List.range count) :=
    listQSum_congr
      (fun mass => qpow_eqv_congr_local hbase mass) _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (slabObservablePairedGlobalEntropyAnchorRatio_fullTail_le count)

private theorem allSeqs_profileWeight_sum_succ_eqv
    (bound count : Nat) :
    listQSum
        (fun profile =>
          pairedPeelSignatureEntropyAnchorRatio ^ natListSum profile)
        (allSeqs bound (count + 1)) ≈
      listQSum
          (fun mass => pairedPeelSignatureEntropyAnchorRatio ^ mass)
          (List.range bound) *
        listQSum
          (fun profile =>
            pairedPeelSignatureEntropyAnchorRatio ^ natListSum profile)
          (allSeqs bound count) := by
  let q := pairedPeelSignatureEntropyAnchorRatio
  let tailWeight : List Nat -> Q' := fun profile => q ^ natListSum profile
  let tailSum := listQSum tailWeight (allSeqs bound count)
  have hflat := listQSum_flatMap tailWeight
    (fun mass =>
      (allSeqs bound count).map fun profile => mass :: profile)
    (List.range bound)
  have hinner : forall mass,
      listQSum tailWeight
          ((allSeqs bound count).map fun profile => mass :: profile) ≈
        q ^ mass * tailSum := by
    intro mass
    rw [listQSum_map]
    have hsplit :
        listQSum
            (fun profile => tailWeight (mass :: profile))
            (allSeqs bound count) ≈
          listQSum
            (fun profile => q ^ mass * tailWeight profile)
            (allSeqs bound count) := by
      apply listQSum_congr
      intro profile
      unfold tailWeight
      simp only [natListSum]
      exact Q'.pow_add_eqv q mass (natListSum profile)
    exact Q'.eqv_trans _ _ _ hsplit
      (listQSum_mul_left (q ^ mass) tailWeight
        (allSeqs bound count))
  have houter :
      listQSum
          (fun mass =>
            listQSum tailWeight
              ((allSeqs bound count).map fun profile => mass :: profile))
          (List.range bound) ≈
        listQSum (fun mass => q ^ mass * tailSum)
          (List.range bound) :=
    listQSum_congr hinner _
  have hcommuted :
      listQSum (fun mass => q ^ mass * tailSum) (List.range bound) ≈
        listQSum (fun mass => tailSum * q ^ mass) (List.range bound) :=
    listQSum_congr
      (fun mass => Q'.mul_comm_eqv (q ^ mass) tailSum) _
  have hfactor := listQSum_mul_left tailSum
    (fun mass => q ^ mass) (List.range bound)
  have hfinal :
      tailSum *
          listQSum (fun mass => q ^ mass) (List.range bound) ≈
        listQSum (fun mass => q ^ mass) (List.range bound) * tailSum :=
    Q'.mul_comm_eqv _ _
  change listQSum tailWeight
      ((List.range bound).flatMap fun mass =>
        (allSeqs bound count).map fun profile => mass :: profile) ≈ _
  exact Q'.eqv_trans _ _ _ hflat
    (Q'.eqv_trans _ _ _ houter
      (Q'.eqv_trans _ _ _ hcommuted
        (Q'.eqv_trans _ _ _ hfactor hfinal)))

/-- Summing every bounded block profile costs at most one factor `25/9` per
face/replica scan coordinate, independently of the coordinate cutoff. -/
theorem allSeqs_profileWeight_sum_le (bound : Nat) : forall count : Nat,
    listQSum
        (fun profile =>
          pairedPeelSignatureEntropyAnchorRatio ^ natListSum profile)
        (allSeqs bound count) ≤
      (Q'.mkPos 25 9 (by decide)) ^ count
  | 0 => by
      change pairedPeelSignatureEntropyAnchorRatio ^ 0 + 0 ≤
        (Q'.mkPos 25 9 (by decide)) ^ 0
      rw [Q'.pow_zero, Q'.pow_zero]
      exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  | count + 1 => by
      have hrec := allSeqs_profileWeight_sum_succ_eqv bound count
      have hhead := pairedPeelSignatureEntropyAnchorRatio_fullTail_le bound
      have htail := allSeqs_profileWeight_sum_le bound count
      have htailNonnegative : (0 : Q') ≤
          listQSum
            (fun profile =>
              pairedPeelSignatureEntropyAnchorRatio ^ natListSum profile)
            (allSeqs bound count) := by
        apply listQSum_nonnegative_on
        intro profile _
        exact Q'.pow_nonneg pairedPeelSignatureEntropyAnchorRatio
          (by decide) (natListSum profile)
      have hproduct := Q'.mul_le_mul_of_nonneg hhead htail
        (by decide) htailNonnegative
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrec) hproduct

/-! ## 3. The complete terminal inverse fiber -/

private theorem listQSum_mul_right_local {A : Type}
    (weight : A -> Q') (factor : Q') (items : List A) :
    listQSum (fun item => weight item * factor) items ≈
      listQSum weight items * factor := by
  have hcommute :
      listQSum (fun item => weight item * factor) items ≈
        listQSum (fun item => factor * weight item) items :=
    listQSum_congr (fun item => Q'.mul_comm_eqv _ _) _
  exact Q'.eqv_trans _ _ _ hcommute
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left factor weight items)
      (Q'.mul_comm_eqv factor (listQSum weight items)))

/-- **Complete fixed-terminal guard-fiber estimate.**  All trace lengths,
ordered signatures, positive peel-size compositions, and block-mass profiles
are summed.  The coefficient depends only on the fixed face list, not on the
representation cutoff, half-volume, terminal, or chosen source family. -/
theorem slabAcceptedPairCanonicalPeeling_fixedTerminal_weight_sum_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).1 = terminal) :
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      (Q'.mkPos 25 9 (by decide)) ^ (2 * faces.length) *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let D := anchorSlabPhysicalData cutoff half
  let profileOf : SlabAcceptedTwoReplicaState D -> List Nat :=
    fun source => slabAcceptedPairedPeelTraceRankMassProfile faces
      (slabAcceptedPairCanonicalPeeling D faces hphysical source).2
        (2 * faces.length)
  let targets := (sources.map profileOf).eraseDups
  let profileWeight : List Nat -> Q' := fun profile =>
    pairedPeelSignatureEntropyAnchorRatio ^ natListSum profile
  let terminalWeight :=
    slabAcceptedTwoReplicaStateWeight cutoff half terminal
  have htargetsNodup : targets.Nodup := eraseDupsNodupLocal _
  have hcoverage : forall source, source ∈ sources ->
      profileOf source ∈ targets := by
    intro source hsource
    apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  have htargetsSubset : forall profile, profile ∈ targets ->
      profile ∈ allSeqs (2 * slabObservableRemovalMaxSize D + 1)
        (2 * faces.length) := by
    intro profile hprofile
    have hmapped := List.mem_eraseDups.mp hprofile
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmapped
    exact slabAcceptedPairCanonicalPeeling_rankMassProfile_mem_allSeqs
      D faces hphysical source
  have hpartition := fiberWeight_total sources
    (slabAcceptedTwoReplicaStateWeight cutoff half)
    profileOf targets htargetsNodup hcoverage
  have hfiber : forall profile, profile ∈ targets ->
      fiberWeight sources
          (slabAcceptedTwoReplicaStateWeight cutoff half)
          profileOf profile ≤
        profileWeight profile * terminalWeight := by
    intro profile hprofile
    unfold fiberWeight
    have hfixed :=
      slabAcceptedPairCanonicalPeeling_fixedTerminalBlockProfileMass_weight_sum_le
        cutoff half faces hnodup hphysical terminal profile
        (natListSum profile) rfl
        (sources.filter fun source => decide (profile = profileOf source))
        (List.filter_sublist.nodup hsources)
        (fun source hsource =>
          hterminal source (List.mem_filter.mp hsource).1)
        (fun source hsource => by
          have heq : profile = profileOf source :=
            of_decide_eq_true (List.mem_filter.mp hsource).2
          exact heq.symm)
        (fun source hsource => by
          have heq : profile = profileOf source :=
            of_decide_eq_true (List.mem_filter.mp hsource).2
          have hsum :=
            slabAcceptedPairCanonicalPeeling_rankMassProfile_sum_eq_traceMass
              D faces hphysical source
          change natListSum (profileOf source) =
            slabAcceptedPairedPeelTraceMass
              (slabAcceptedPairCanonicalPeeling
                D faces hphysical source).2 at hsum
          rw [← heq] at hsum
          exact hsum.symm)
    simpa only [profileWeight, terminalWeight] using hfixed
  have hfibersLe :
      listQSum
          (fiberWeight sources
            (slabAcceptedTwoReplicaStateWeight cutoff half) profileOf)
          targets ≤
        listQSum (fun profile => profileWeight profile * terminalWeight)
          targets := by
    apply listQSum_le_of_injective targets targets
      (fiberWeight sources
        (slabAcceptedTwoReplicaStateWeight cutoff half) profileOf)
      (fun profile => profileWeight profile * terminalWeight)
      (fun profile => profile) htargetsNodup
    · intro profile hprofile
      exact hprofile
    · intro left _ right _ heq
      exact heq
    · exact hfiber
    · intro profile _
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg pairedPeelSignatureEntropyAnchorRatio
          (by decide) (natListSum profile))
        (slabAcceptedTwoReplicaStateWeight_nonnegative
          cutoff half terminal)
  have hprofilesSubset :
      listQSum profileWeight targets ≤
        listQSum profileWeight
          (allSeqs (2 * slabObservableRemovalMaxSize D + 1)
            (2 * faces.length)) := by
    apply listQSum_le_of_injective targets
      (allSeqs (2 * slabObservableRemovalMaxSize D + 1)
        (2 * faces.length))
      profileWeight profileWeight (fun profile => profile) htargetsNodup
    · exact htargetsSubset
    · intro left _ right _ heq
      exact heq
    · intro profile _
      exact Q'.le_refl' _
    · intro profile _
      exact Q'.pow_nonneg pairedPeelSignatureEntropyAnchorRatio
        (by decide) (natListSum profile)
  have hprofiles :
      listQSum profileWeight targets ≤
        (Q'.mkPos 25 9 (by decide)) ^ (2 * faces.length) :=
    Q'.le_trans' _ _ _ hprofilesSubset
      (allSeqs_profileWeight_sum_le
        (2 * slabObservableRemovalMaxSize D + 1)
        (2 * faces.length))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ terminalWeight
    hprofiles
    (slabAcceptedTwoReplicaStateWeight_nonnegative cutoff half terminal)
  have hfactor := listQSum_mul_right_local
    profileWeight terminalWeight targets
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ hfibersLe
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hscaled))

/-! ## 4. Explicit cutoff-uniform payment rate -/

/-- The complete profile-summation congestion coefficient. -/
def pairedPeelProfilePaymentCoefficient (faces : List Nat) : Q' :=
  (Q'.mkPos 25 9 (by decide)) ^ (2 * faces.length)

private theorem qpow_pos_local (value : Q')
    (hvalue : (0 : Q') < value) : forall exponent : Nat,
    (0 : Q') < value ^ exponent
  | 0 => by
      rw [Q'.pow_zero]
      decide
  | exponent + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hvalue (qpow_pos_local value hvalue exponent)

theorem pairedPeelProfilePaymentCoefficient_pos (faces : List Nat) :
    (0 : Q') < pairedPeelProfilePaymentCoefficient faces := by
  unfold pairedPeelProfilePaymentCoefficient
  exact qpow_pos_local _ (by decide) _

/-- Reciprocal of the complete congestion coefficient.  The face list is
fixed before the cutoff varies, so this is one literal positive rational at
every representation cutoff and half-volume. -/
def pairedPeelProfilePaymentRate (faces : List Nat) : Q' :=
  Q'.recipPos (pairedPeelProfilePaymentCoefficient faces)
    (pairedPeelProfilePaymentCoefficient_pos faces)

theorem pairedPeelProfilePaymentRate_pos (faces : List Nat) :
    (0 : Q') < pairedPeelProfilePaymentRate faces := by
  unfold pairedPeelProfilePaymentRate
  exact Q'.recipPos_pos _ _

/-- The explicit profile rate pays the entire terminal inverse fiber. -/
theorem pairedPeelProfilePaymentRate_mul_fixedTerminal_weight_sum_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).1 = terminal) :
    pairedPeelProfilePaymentRate faces *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let coefficient := pairedPeelProfilePaymentCoefficient faces
  let rate := pairedPeelProfilePaymentRate faces
  let terminalWeight :=
    slabAcceptedTwoReplicaStateWeight cutoff half terminal
  have hbound :=
    slabAcceptedPairCanonicalPeeling_fixedTerminal_weight_sum_le
      cutoff half faces hnodup hphysical terminal sources hsources hterminal
  change listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      coefficient * terminalWeight at hbound
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ rate hbound
    (Q'.le_of_lt (pairedPeelProfilePaymentRate_pos faces))
  have hcancel : rate * coefficient ≈ 1 := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv rate coefficient)
      (Q'.mul_recipPos_eqv coefficient
        (pairedPeelProfilePaymentCoefficient_pos faces))
  have hcollapse : rate * (coefficient * terminalWeight) ≈
      terminalWeight := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv rate coefficient terminalWeight))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (rate * coefficient) 1 terminalWeight hcancel)
        (Q'.one_mul_eqv terminalWeight))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.slabAcceptedPairCanonicalPeeling_rankMassProfile_sum_eq_traceMass
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.slabAcceptedPairCanonicalPeeling_rankMassProfile_mem_allSeqs
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.pairedPeelSignatureEntropyAnchorRatio_fullTail_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.allSeqs_profileWeight_sum_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.slabAcceptedPairCanonicalPeeling_fixedTerminal_weight_sum_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.pairedPeelProfilePaymentRate_pos
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric.pairedPeelProfilePaymentRate_mul_fixedTerminal_weight_sum_le
