/-
# A binary block code for ordered canonical paired-peeling traces

The canonical trace ranks are nondecreasing.  Group its positive peel sizes
by the finitely many face/replica scan ranks and encode each block by the exact
positive-composition binary code.  For a prescribed block-mass profile, the
dependent product carrier has cardinality

  product_r 2^(mass_r) = 2^(sum_r mass_r).

Ordered rank/value sequences are uniquely determined by their filtered rank
blocks.  Hence equal block codes reconstruct equal erased trace skeletons.
This removes the need to fix the number of repeated peels at each guard key.

Constructive contract: dependent finite products, stable filters, and natural
order only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Rank blocks and their dependent binary carrier -/

/-- Peel sizes carried by one exact scan rank. -/
def slabAcceptedPairedPeelTraceSizesAtRank
    (faces : List Nat) (rank : Nat)
    (trace : List SlabAcceptedPairedPeelRecord) : List Nat :=
  (trace.filter fun record => decide
      (slabAcceptedPairScanRank faces
        (record.rootFaceId, record.left) = rank)).map
    SlabAcceptedPairedPeelRecord.peelSize

/-- All rank blocks below `count`, stored from the last rank down to zero.
The reverse order makes structural lookup and dependent products literal. -/
def slabAcceptedPairedPeelTraceRankBlocks
    (faces : List Nat) (trace : List SlabAcceptedPairedPeelRecord) :
    Nat -> List (List Nat)
  | 0 => []
  | count + 1 =>
      slabAcceptedPairedPeelTraceSizesAtRank faces count trace ::
        slabAcceptedPairedPeelTraceRankBlocks faces trace count

/-- Exact mass profile of the stored rank blocks. -/
def slabAcceptedPairedPeelTraceRankMassProfile
    (faces : List Nat) (trace : List SlabAcceptedPairedPeelRecord)
    (count : Nat) : List Nat :=
  (slabAcceptedPairedPeelTraceRankBlocks faces trace count).map natListSum

/-- Binary positive-composition code of every stored rank block. -/
def slabAcceptedPairedPeelTraceRankBlockCode
    (faces : List Nat) (trace : List SlabAcceptedPairedPeelRecord)
    (count : Nat) : List (List Nat) :=
  (slabAcceptedPairedPeelTraceRankBlocks faces trace count).map
    positiveCompositionBinaryCode

/-- Dependent product of binary words with prescribed lengths. -/
def binaryWordProfileCarrier : List Nat -> List (List (List Nat))
  | [] => [[]]
  | mass :: masses =>
      (allSeqs 2 mass).flatMap fun code =>
        (binaryWordProfileCarrier masses).map fun codes => code :: codes

private theorem flatMap_cons_code_length
    {A : Type} (heads : List A) (tails : List (List A)) :
    (heads.flatMap fun head => tails.map fun tail => head :: tail).length =
      heads.length * tails.length := by
  induction heads with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul]
      omega

/-- The dependent binary profile carrier has exact product cardinality. -/
theorem binaryWordProfileCarrier_length : forall masses : List Nat,
    (binaryWordProfileCarrier masses).length = 2 ^ natListSum masses
  | [] => rfl
  | mass :: masses => by
      rw [binaryWordProfileCarrier, flatMap_cons_code_length,
        length_allSeqs, binaryWordProfileCarrier_length masses]
      simp only [natListSum]
      rw [Nat.pow_add]

/-- The block code of positive words belongs to the carrier indexed by their
exact mass profile. -/
theorem positiveCompositionBlockCode_mem_profileCarrier :
    forall blocks : List (List Nat),
    (forall block, block ∈ blocks ->
      forall size, size ∈ block -> 0 < size) ->
    blocks.map positiveCompositionBinaryCode ∈
      binaryWordProfileCarrier (blocks.map natListSum)
  | [], _ => List.mem_cons_self
  | block :: blocks, hpositive => by
      unfold binaryWordProfileCarrier
      apply List.mem_flatMap.mpr
      refine ⟨positiveCompositionBinaryCode block,
        positiveCompositionBinaryCode_mem_allSeqs
          (natListSum block) block
          (fun size hsize =>
            hpositive block List.mem_cons_self size hsize)
          rfl, ?_⟩
      apply List.mem_map.mpr
      refine ⟨blocks.map positiveCompositionBinaryCode,
        positiveCompositionBlockCode_mem_profileCarrier blocks
          (fun next hnext size hsize =>
            hpositive next (List.mem_cons_of_mem block hnext) size hsize),
        rfl⟩

/-! ## 2. Structural lookup and code injectivity -/

/-- Structural lookup in the reverse rank-block list. -/
theorem slabAcceptedPairedPeelTraceRankBlocks_lookup
    (faces : List Nat) (trace : List SlabAcceptedPairedPeelRecord) :
    forall count rank,
      rank < count ->
      (slabAcceptedPairedPeelTraceRankBlocks faces trace count).getD
          (count - 1 - rank) [] =
        slabAcceptedPairedPeelTraceSizesAtRank faces rank trace
  | 0, _, hrank => by omega
  | count + 1, rank, hrank => by
      by_cases htop : rank = count
      · subst rank
        simp only [slabAcceptedPairedPeelTraceRankBlocks,
          Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
      · have hrankTail : rank < count := by omega
        have hindex : count + 1 - 1 - rank =
            (count - 1 - rank) + 1 := by omega
        rw [hindex]
        simp only [slabAcceptedPairedPeelTraceRankBlocks,
          List.getD_cons_succ]
        exact slabAcceptedPairedPeelTraceRankBlocks_lookup
          faces trace count rank hrankTail

/-- Equal block-code lists reconstruct equal positive size blocks. -/
theorem positiveCompositionBlockCode_injective
    (left right : List (List Nat))
    (hleft : forall block, block ∈ left ->
      forall size, size ∈ block -> 0 < size)
    (hright : forall block, block ∈ right ->
      forall size, size ∈ block -> 0 < size)
    (hcode : left.map positiveCompositionBinaryCode =
      right.map positiveCompositionBinaryCode) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => cases hcode
  | cons leftHead leftTail ih =>
      cases right with
      | nil => cases hcode
      | cons rightHead rightTail =>
          have hparts := List.cons.inj hcode
          have hhead := positiveCompositionBinaryCode_injective
            leftHead rightHead
            (hleft leftHead List.mem_cons_self)
            (hright rightHead List.mem_cons_self) hparts.1
          subst rightHead
          exact congrArg (List.cons leftHead)
            (ih rightTail
              (fun block hblock =>
                hleft block (List.mem_cons_of_mem leftHead hblock))
              (fun block hblock =>
                hright block (List.mem_cons_of_mem leftHead hblock))
              hparts.2)

/-! ## 3. Ordered sequences are determined by their filtered blocks -/

private theorem filter_rank_eq_nil_of_ne
    {A : Type} (rank : A -> Nat) (query : Nat) :
    forall items : List A,
    (forall item, item ∈ items -> rank item ≠ query) ->
      items.filter (fun item => decide (rank item = query)) = []
  | [], _ => rfl
  | head :: tail, hne => by
      have hhead := hne head List.mem_cons_self
      have htail := filter_rank_eq_nil_of_ne rank query tail
        (fun item hitem => hne item (List.mem_cons_of_mem head hitem))
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [if_neg hhead, htail]

/-- Two nondecreasing finite sequences with the same value list in every rank
fiber have the same ordered `(rank,value)` projection. -/
theorem pairwiseRankValue_eq_of_filtered_eq
    {A B : Type} (rank : A -> Nat) (value : A -> B) :
    forall left right : List A,
    left.Pairwise (fun x y => rank x ≤ rank y) ->
    right.Pairwise (fun x y => rank x ≤ rank y) ->
    (forall query,
      (left.filter fun item => decide (rank item = query)).map value =
        (right.filter fun item => decide (rank item = query)).map value) ->
    left.map (fun item => (rank item, value item)) =
      right.map (fun item => (rank item, value item)) := by
  intro left
  induction left with
  | nil =>
      intro right hleft hright hblocks
      cases right with
      | nil => rfl
      | cons head tail =>
          have hblock := hblocks (rank head)
          simp only [List.filter_nil, List.map_nil, List.filter_cons,
            decide_true, if_true, List.map_cons] at hblock
          cases hblock
  | cons leftHead leftTail ih =>
      intro right hleft hright hblocks
      cases right with
      | nil =>
          have hblock := hblocks (rank leftHead)
          simp only [List.filter_cons, decide_true, if_true,
            List.map_cons, List.filter_nil, List.map_nil] at hblock
          cases hblock
      | cons rightHead rightTail =>
          have hleftParts := List.pairwise_cons.mp hleft
          have hrightParts := List.pairwise_cons.mp hright
          have hrank : rank leftHead = rank rightHead := by
            rcases Nat.lt_trichotomy (rank leftHead) (rank rightHead) with
              hlt | heq | hgt
            · have hrightEmpty :
                  (rightHead :: rightTail).filter
                      (fun item => decide
                        (rank item = rank leftHead)) = [] := by
                apply filter_rank_eq_nil_of_ne rank (rank leftHead)
                intro item hitem
                rcases List.mem_cons.mp hitem with hhead | htail
                · subst item
                  omega
                · have hle := hrightParts.1 item htail
                  omega
              have hblock := hblocks (rank leftHead)
              rw [hrightEmpty] at hblock
              simp only [List.map_nil, List.filter_cons, decide_true,
                if_true, List.map_cons] at hblock
              cases hblock
            · exact heq
            · have hleftEmpty :
                  (leftHead :: leftTail).filter
                      (fun item => decide
                        (rank item = rank rightHead)) = [] := by
                apply filter_rank_eq_nil_of_ne rank (rank rightHead)
                intro item hitem
                rcases List.mem_cons.mp hitem with hhead | htail
                · subst item
                  omega
                · have hle := hleftParts.1 item htail
                  omega
              have hblock := hblocks (rank rightHead)
              rw [hleftEmpty] at hblock
              simp only [List.map_nil, List.filter_cons, decide_true,
                if_true, List.map_cons] at hblock
              cases hblock
          have hvalue : value leftHead = value rightHead := by
            have hblock := hblocks (rank leftHead)
            simp only [List.filter_cons, decide_true, if_true,
              List.map_cons, hrank] at hblock
            exact (List.cons.inj hblock).1
          have htailBlocks : forall query,
              (leftTail.filter fun item =>
                  decide (rank item = query)).map value =
                (rightTail.filter fun item =>
                  decide (rank item = query)).map value := by
            intro query
            have hblock := hblocks query
            by_cases hquery : rank leftHead = query
            · have hqueryRight : rank rightHead = query := hrank.symm.trans hquery
              simp only [List.filter_cons, hquery, hqueryRight,
                decide_true, if_true, List.map_cons] at hblock
              exact (List.cons.inj hblock).2
            · have hqueryRight : rank rightHead ≠ query := by
                intro heq
                exact hquery (hrank.trans heq)
              simp only [List.filter_cons, hquery, hqueryRight,
                decide_false, if_false] at hblock
              exact hblock
          simp only [List.map_cons]
          rw [hrank, hvalue,
            ih rightTail hleftParts.2 hrightParts.2 htailBlocks]

/-! ## 4. Scan-rank injectivity on a duplicate-free face list -/

theorem slabAcceptedPairFaceRank_eq_iff_of_mem
    (faces : List Nat) (hnodup : faces.Nodup)
    (left right : Nat) (hleft : left ∈ faces) (hright : right ∈ faces) :
    slabAcceptedPairFaceRank left faces =
        slabAcceptedPairFaceRank right faces <-> left = right := by
  induction faces with
  | nil => cases hleft
  | cons head tail ih =>
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have hheadNotTail := (List.nodup_cons.mp hnodup).1
      constructor
      · intro hrank
        by_cases hleftHead : left = head
        · by_cases hrightHead : right = head
          · exact hleftHead.trans hrightHead.symm
          · have hrightTail : right ∈ tail := by
              rcases List.mem_cons.mp hright with hhead | htail
              · exact False.elim (hrightHead hhead)
              · exact htail
            simp only [slabAcceptedPairFaceRank, hleftHead, hrightHead,
              if_true, if_false] at hrank
            omega
        · have hleftTail : left ∈ tail := by
            rcases List.mem_cons.mp hleft with hhead | htail
            · exact False.elim (hleftHead hhead)
            · exact htail
          by_cases hrightHead : right = head
          · simp only [slabAcceptedPairFaceRank, hleftHead, hrightHead,
              if_true, if_false] at hrank
            omega
          · have hrightTail : right ∈ tail := by
              rcases List.mem_cons.mp hright with hhead | htail
              · exact False.elim (hrightHead hhead)
              · exact htail
            simp only [slabAcceptedPairFaceRank, hleftHead, hrightHead,
              if_false] at hrank
            exact (ih htailNodup hleftTail hrightTail).mp
              (by omega)
      · intro heq
        subst right
        rfl

/-- The doubled face rank plus side bit is injective on listed keys. -/
theorem slabAcceptedPairScanRank_injective_of_mem
    (faces : List Nat) (hnodup : faces.Nodup)
    (left right : Nat × Bool)
    (hleft : left.1 ∈ faces) (hright : right.1 ∈ faces)
    (hrank : slabAcceptedPairScanRank faces left =
      slabAcceptedPairScanRank faces right) :
    left = right := by
  let leftBit : Nat := if left.2 then 0 else 1
  let rightBit : Nat := if right.2 then 0 else 1
  have hleftBit : leftBit ≤ 1 := by
    unfold leftBit
    cases left.2 <;> decide
  have hrightBit : rightBit ≤ 1 := by
    unfold rightBit
    cases right.2 <;> decide
  have hrank' :
      2 * slabAcceptedPairFaceRank left.1 faces + leftBit =
        2 * slabAcceptedPairFaceRank right.1 faces + rightBit := by
    simpa only [leftBit, rightBit, slabAcceptedPairScanRank] using hrank
  have hfaceRank : slabAcceptedPairFaceRank left.1 faces =
      slabAcceptedPairFaceRank right.1 faces := by
    omega
  have hface := (slabAcceptedPairFaceRank_eq_iff_of_mem
    faces hnodup left.1 right.1 hleft hright).mp hfaceRank
  have hside : left.2 = right.2 := by
    have hbit : leftBit = rightBit := by omega
    unfold leftBit rightBit at hbit
    cases hleftSide : left.2 <;> cases hrightSide : right.2
    · rfl
    · simp [hleftSide, hrightSide] at hbit
    · simp [hleftSide, hrightSide] at hbit
    · rfl
  exact Prod.ext hface hside

/-! ## 5. Equal ordered block codes reconstruct the erased skeleton -/

theorem scanRank_lt_two_mul_length
    (faces : List Nat) (key : Nat × Bool)
    (hmem : key.1 ∈ faces) :
    slabAcceptedPairScanRank faces key < 2 * faces.length := by
  have hface := slabAcceptedPairFaceRank_lt_length_of_mem
    key.1 faces hmem
  let bit : Nat := if key.2 then 0 else 1
  have hbit : bit ≤ 1 := by
    unfold bit
    cases key.2 <;> decide
  change 2 * slabAcceptedPairFaceRank key.1 faces + bit <
    2 * faces.length
  omega

private theorem traceSkeleton_eq_of_rankSizePairs_eq
    (faces : List Nat) (hnodup : faces.Nodup) :
    forall left right : List SlabAcceptedPairedPeelRecord,
    (forall record, record ∈ left -> record.rootFaceId ∈ faces) ->
    (forall record, record ∈ right -> record.rootFaceId ∈ faces) ->
    left.map (fun record =>
        (slabAcceptedPairScanRank faces
          (record.rootFaceId, record.left), record.peelSize)) =
      right.map (fun record =>
        (slabAcceptedPairScanRank faces
          (record.rootFaceId, record.left), record.peelSize)) ->
    left.map SlabAcceptedPairedPeelRecord.skeleton =
      right.map SlabAcceptedPairedPeelRecord.skeleton
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hpairs => by cases hpairs
  | _ :: _, [], _, _, hpairs => by cases hpairs
  | leftHead :: leftTail, rightHead :: rightTail,
      hleftMem, hrightMem, hpairs => by
      have hparts := List.cons.inj hpairs
      have hrank := congrArg Prod.fst hparts.1
      have hsize := congrArg Prod.snd hparts.1
      have hkey := slabAcceptedPairScanRank_injective_of_mem
        faces hnodup
        (leftHead.rootFaceId, leftHead.left)
        (rightHead.rootFaceId, rightHead.left)
        (hleftMem leftHead List.mem_cons_self)
        (hrightMem rightHead List.mem_cons_self) hrank
      have hskeleton :
          YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.SlabAcceptedPairedPeelRecord.skeleton leftHead =
            YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.SlabAcceptedPairedPeelRecord.skeleton rightHead := by
        cases leftHead with
        | mk leftRoot leftSide leftSize leftCode =>
            cases rightHead with
            | mk rightRoot rightSide rightSize rightCode =>
                simp only at hkey hsize ⊢
                have hroot := congrArg Prod.fst hkey
                have hside := congrArg Prod.snd hkey
                simp only at hroot hside
                subst rightRoot
                subst rightSide
                subst rightSize
                rfl
      simp only [List.map_cons]
      rw [hskeleton,
        traceSkeleton_eq_of_rankSizePairs_eq faces hnodup
          leftTail rightTail
          (fun record hrecord =>
            hleftMem record (List.mem_cons_of_mem leftHead hrecord))
          (fun record hrecord =>
            hrightMem record (List.mem_cons_of_mem rightHead hrecord))
          hparts.2]

theorem traceRankBlocks_sizes_pos
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall count block,
    block ∈ slabAcceptedPairedPeelTraceRankBlocks faces
        (slabAcceptedPairCanonicalPeeling D faces hphysical state).2 count ->
    forall size, size ∈ block -> 0 < size
  | 0, _, hblock, _, _ => by cases hblock
  | count + 1, block, hblock, size, hsize => by
      rcases List.mem_cons.mp hblock with hhead | htail
      · subst block
        obtain ⟨record, hrecordFilter, rfl⟩ := List.mem_map.mp hsize
        exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
          D faces hphysical state record
            (List.mem_filter.mp hrecordFilter).1
      · exact traceRankBlocks_sizes_pos
          D faces hphysical state count block htail size hsize

private theorem pairwise_of_map_pairwise
    {A B : Type} (mapValue : A -> B) (relation : B -> B -> Prop) :
    forall items : List A,
    (items.map mapValue).Pairwise relation ->
      items.Pairwise (fun left right =>
        relation (mapValue left) (mapValue right))
  | [], _ => List.Pairwise.nil
  | head :: tail, hpairwise => by
      have hparts := List.pairwise_cons.mp hpairwise
      apply List.pairwise_cons.mpr
      refine ⟨?_, pairwise_of_map_pairwise mapValue relation tail hparts.2⟩
      intro item hitem
      exact hparts.1 (mapValue item)
        (List.mem_map.mpr ⟨item, hitem, rfl⟩)

/-- **Ordered block-code injectivity.**  Equal per-rank positive-composition
codes determine equal erased skeletons for any two canonical traces. -/
theorem slabAcceptedPairCanonicalPeeling_skeleton_eq_of_rankBlockCode_eq
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (leftState rightState : SlabAcceptedTwoReplicaState D)
    (hcode :
      slabAcceptedPairedPeelTraceRankBlockCode faces
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical leftState).2 (2 * faces.length) =
        slabAcceptedPairedPeelTraceRankBlockCode faces
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical rightState).2 (2 * faces.length)) :
    (slabAcceptedPairCanonicalPeeling
        D faces hphysical leftState).2.map
          SlabAcceptedPairedPeelRecord.skeleton =
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical rightState).2.map
          SlabAcceptedPairedPeelRecord.skeleton := by
  let leftTrace := (slabAcceptedPairCanonicalPeeling
    D faces hphysical leftState).2
  let rightTrace := (slabAcceptedPairCanonicalPeeling
    D faces hphysical rightState).2
  have hleftPositive : forall block,
      block ∈ slabAcceptedPairedPeelTraceRankBlocks
          faces leftTrace (2 * faces.length) ->
      forall size, size ∈ block -> 0 < size := by
    exact traceRankBlocks_sizes_pos D faces hphysical leftState
      (2 * faces.length)
  have hrightPositive : forall block,
      block ∈ slabAcceptedPairedPeelTraceRankBlocks
          faces rightTrace (2 * faces.length) ->
      forall size, size ∈ block -> 0 < size := by
    exact traceRankBlocks_sizes_pos D faces hphysical rightState
      (2 * faces.length)
  have hblocks :
      slabAcceptedPairedPeelTraceRankBlocks
          faces leftTrace (2 * faces.length) =
        slabAcceptedPairedPeelTraceRankBlocks
          faces rightTrace (2 * faces.length) := by
    apply positiveCompositionBlockCode_injective _ _
      hleftPositive hrightPositive
    exact hcode
  have hfiltered : forall query,
      (leftTrace.filter fun record => decide
          (slabAcceptedPairScanRank faces
            (record.rootFaceId, record.left) = query)).map
          SlabAcceptedPairedPeelRecord.peelSize =
        (rightTrace.filter fun record => decide
          (slabAcceptedPairScanRank faces
            (record.rootFaceId, record.left) = query)).map
          SlabAcceptedPairedPeelRecord.peelSize := by
    intro query
    by_cases hquery : query < 2 * faces.length
    · have hget := congrArg
          (fun blocks => blocks.getD (2 * faces.length - 1 - query) [])
          hblocks
      have hleftLookup := slabAcceptedPairedPeelTraceRankBlocks_lookup
        faces leftTrace (2 * faces.length) query hquery
      have hrightLookup := slabAcceptedPairedPeelTraceRankBlocks_lookup
        faces rightTrace (2 * faces.length) query hquery
      exact hleftLookup.symm.trans (hget.trans hrightLookup)
    · have hleftEmpty :
          leftTrace.filter (fun record => decide
            (slabAcceptedPairScanRank faces
              (record.rootFaceId, record.left) = query)) = [] := by
        apply filter_rank_eq_nil_of_ne
          (fun record : SlabAcceptedPairedPeelRecord =>
            slabAcceptedPairScanRank faces
              (record.rootFaceId, record.left)) query leftTrace
        intro record hrecord heq
        have hroot := slabAcceptedPairCanonicalPeeling_trace_root_mem
          D faces hphysical leftState record hrecord
        have hlt := scanRank_lt_two_mul_length faces
          (record.rootFaceId, record.left) hroot
        omega
      have hrightEmpty :
          rightTrace.filter (fun record => decide
            (slabAcceptedPairScanRank faces
              (record.rootFaceId, record.left) = query)) = [] := by
        apply filter_rank_eq_nil_of_ne
          (fun record : SlabAcceptedPairedPeelRecord =>
            slabAcceptedPairScanRank faces
              (record.rootFaceId, record.left)) query rightTrace
        intro record hrecord heq
        have hroot := slabAcceptedPairCanonicalPeeling_trace_root_mem
          D faces hphysical rightState record hrecord
        have hlt := scanRank_lt_two_mul_length faces
          (record.rootFaceId, record.left) hroot
        omega
      rw [hleftEmpty, hrightEmpty]
  have hleftOrdered : leftTrace.Pairwise
      (fun left right =>
        slabAcceptedPairScanRank faces (left.rootFaceId, left.left) ≤
          slabAcceptedPairScanRank faces
            (right.rootFaceId, right.left)) := by
    apply pairwise_of_map_pairwise
      (fun record : SlabAcceptedPairedPeelRecord =>
        slabAcceptedPairScanRank faces (record.rootFaceId, record.left))
      (fun left right => left ≤ right) leftTrace
    exact slabAcceptedPairCanonicalPeeling_traceScanRanks_pairwise
      D faces hnodup hphysical leftState
  have hrightOrdered : rightTrace.Pairwise
      (fun left right =>
        slabAcceptedPairScanRank faces (left.rootFaceId, left.left) ≤
          slabAcceptedPairScanRank faces
            (right.rootFaceId, right.left)) := by
    apply pairwise_of_map_pairwise
      (fun record : SlabAcceptedPairedPeelRecord =>
        slabAcceptedPairScanRank faces (record.rootFaceId, record.left))
      (fun left right => left ≤ right) rightTrace
    exact slabAcceptedPairCanonicalPeeling_traceScanRanks_pairwise
      D faces hnodup hphysical rightState
  have hpairs := pairwiseRankValue_eq_of_filtered_eq
    (fun record : SlabAcceptedPairedPeelRecord =>
      slabAcceptedPairScanRank faces (record.rootFaceId, record.left))
    SlabAcceptedPairedPeelRecord.peelSize leftTrace rightTrace
    hleftOrdered hrightOrdered
    hfiltered
  exact traceSkeleton_eq_of_rankSizePairs_eq faces hnodup
    leftTrace rightTrace
    (slabAcceptedPairCanonicalPeeling_trace_root_mem
      D faces hphysical leftState)
    (slabAcceptedPairCanonicalPeeling_trace_root_mem
      D faces hphysical rightState)
    hpairs

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode.binaryWordProfileCarrier_length
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode.positiveCompositionBlockCode_mem_profileCarrier
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode.pairwiseRankValue_eq_of_filtered_eq
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode.slabAcceptedPairCanonicalPeeling_skeleton_eq_of_rankBlockCode_eq
