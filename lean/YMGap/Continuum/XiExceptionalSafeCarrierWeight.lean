/-
# Exact weight of the compatibility-safe exceptional path carrier

The safe carrier discards the reached component from both terminal masks.
This file identifies its chain weight exactly: a mapped incompatibility path
times any admissible background compatible with every path vertex.  The
identity exposes the precise finite budget available for each safe-code
fiber; no off-path branch factor is hidden in the target term.
-/

import YMGap.Continuum.XiExceptionalTargetNodup

namespace YMGap.Continuum.XiExceptionalSafeCarrierWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A raw chain code following a cons-form walk -/

def chainCodeOfWalk {edge : Polymer L → Polymer L → Bool}
    {X Y : Polymer L} (walk : CWalk edge X Y)
    (background : List (Polymer L)) : ChainCode L.Plaquette :=
  match walk with
  | .single _ => .terminal background
  | .cons _ rest => .step rest.start (chainCodeOfWalk rest background)

theorem erase_occurrenceChainCodeOfWalk_map
    (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j : Nat}
    (hedge : ∀ x y, edge x y = true →
      (!(compatibleB (polyAt Gamma x) (polyAt Gamma y))) = true)
    (walk : CWalk edge i j) (background : OccBitVec Gamma.length) :
    eraseOccChainCode Gamma (occurrenceChainCodeOfWalk walk background) =
      chainCodeOfWalk (mapCWalk (edgeB := fun X Y : Polymer L =>
        !(compatibleB X Y)) (polyAt Gamma) hedge walk)
        (selectByBits Gamma background) := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode, mapCWalk,
        chainCodeOfWalk, CWalk.start_eq]
      rw [ih]

/-! ## 2. Exact chain/background factorization -/

theorem chainCodeOfWalk_weight_eqv
    (w : Q') (qP b2 : Polymer L → Bool)
    (Gamma B : List (Polymer L)) (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (walk : CWalk (fun A C : Polymer L => !(compatibleB A C)) X Y)
      (bg : Polymer L → Bool),
      (∀ Z, Z ∈ walk.vertices → qP Z = true) →
      b2 Y = true →
      familyCompatibleB B = true →
      B.all qP = true →
      B.all bg = true →
      (∀ Z, Z ∈ walk.vertices → ∀ T, T ∈ B →
        compatibleB Z T = true) →
      chainCodeWeight w qP b2 Gamma label X bg
          (chainCodeOfWalk walk B) ≈
        walk.activityWeight w label * familyActivity w B label
  | X, _, .single _, bg, hq, hb2, hBcompat, hBq, hBbg, hBpath => by
      have hqX : qP X = true := hq X List.mem_cons_self
      have hall : B.all
          (fun T => (qP T && bg T) && compatibleB X T) = true := by
        apply List.all_eq_true.mpr
        intro T hTB
        have hqT := List.all_eq_true.mp hBq T hTB
        have hbgT := List.all_eq_true.mp hBbg T hTB
        have hcT := hBpath X List.mem_cons_self T hTB
        simp [hqT, hbgT, hcT]
      unfold chainCodeOfWalk chainCodeWeight CWalk.activityWeight
      simp only [hqX, hb2, Bool.true_and, if_true,
        admissibleFamilyWeight, hall, hBcompat]
      exact Q'.eqv_refl _
  | X, Y, .cons hXY rest, bg, hq, hb2, hBcompat, hBq, hBbg,
      hBpath => by
      have hqNext : qP rest.start = true :=
        hq rest.start (List.mem_cons_of_mem X (CWalk.start_mem_vertices rest))
      have hXY' : (!(compatibleB X rest.start)) = true := by
        simpa only [CWalk.start_eq] using hXY
      have hcond : (qP rest.start && (!(compatibleB X rest.start))) = true :=
        (Bool.and_eq_true _ _).mpr ⟨hqNext, hXY'⟩
      simp only [CWalk.start_eq] at hcond
      have hBbg' : B.all (fun T => bg T && compatibleB X T) = true := by
        apply List.all_eq_true.mpr
        intro T hTB
        have hbgT := List.all_eq_true.mp hBbg T hTB
        have hcT := hBpath X List.mem_cons_self T hTB
        simp [hbgT, hcT]
      have ih := chainCodeOfWalk_weight_eqv w qP b2 Gamma B label rest
        (fun T => bg T && compatibleB X T)
        (fun Z hZ => hq Z (List.mem_cons_of_mem X hZ)) hb2
        hBcompat hBq hBbg'
        (fun Z hZ T hTB =>
          hBpath Z (List.mem_cons_of_mem X hZ) T hTB)
      simp only [chainCodeOfWalk, chainCodeWeight, CWalk.activityWeight,
        CWalk.start_eq, hcond, if_true]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (activity w X label) _ _ ih) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (activity w X label)
          (rest.activityWeight w label) (familyActivity w B label))

/-! ## 3. The source-dependent safe encoder -/

def exceptionalSafeCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  sourcePathCarrierXiCode Gamma qP b1 b2 entry.1
    (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2)

theorem exceptionalSafeCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalSafeCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma :=
  sourcePathCarrierXiCode_mem Gamma qP b1 b2 entry.1
    (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2)

theorem sourceExceptionalPath_polymerWalk_eq_map
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    path.polymerWalk =
      mapCWalk
        (edgeB := fun X Y : Polymer L => !(compatibleB X Y))
        (polyAt Gamma)
        (fun _ _ h => disagreementEdge_incAtDistinct Gamma
          (bitMask pair.1) (bitMask pair.2) h)
        path.indexWalk := by
  rfl

theorem exceptionalSafeCarrierCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let cut := forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let outsideLeft := maskFamily Gamma
      (outsideMask cut (bitMask pair.1))
    let outsideRight := maskFamily Gamma
      (outsideMask cut (bitMask pair.2))
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalSafeCarrierCode Gamma qP b1 b2 entry) ≈
      (path.polymerWalk.activityWeight w label *
        familyActivity w outsideLeft label) *
        familyActivity w outsideRight label := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let cut := forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let outsideLeft := maskFamily Gamma
    (outsideMask cut (bitMask pair.1))
  let outsideRight := maskFamily Gamma
    (outsideMask cut (bitMask pair.2))
  let background := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.1)) 0
  let external := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.2)) 0
  have hleftBase :
      familyCompatibleB (maskFamily Gamma (bitMask pair.1)) = true := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact facts.left_family_compatible
  have hrightBase :
      familyCompatibleB (maskFamily Gamma (bitMask pair.2)) = true := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact facts.right_family_compatible
  have hleftCompat : familyCompatibleB outsideLeft = true :=
    outsideMask_familyCompatible Gamma cut (bitMask pair.1)
      hleftBase
  have hrightCompat : familyCompatibleB outsideRight = true :=
    outsideMask_familyCompatible Gamma cut (bitMask pair.2)
      hrightBase
  have hleftQ : outsideLeft.all qP = true :=
    maskFamily_all_of_pointwise Gamma
      (outsideMask cut (bitMask pair.1)) qP
      (fun i hi hsel => facts.left_q i hi
        (outsideMask_parts cut (bitMask pair.1) hsel).1)
  have hrightQ : outsideRight.all qP = true :=
    maskFamily_all_of_pointwise Gamma
      (outsideMask cut (bitMask pair.2)) qP
      (fun i hi hsel => facts.right_q i hi
        (outsideMask_parts cut (bitMask pair.2) hsel).1)
  have hb2seed : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hpathCompatible : ∀ X, X ∈ path.polymerWalk.vertices →
      ∀ T, T ∈ outsideLeft → compatibleB X T = true :=
    distinct_path_compatible_with_outside_left Gamma qP b2
      (bitMask pair.1) (bitMask pair.2)
      (exceptionalMarkedIndex Gamma b1 b2 pair)
      facts.left_q facts.right_q facts.marked_reached
      facts.left_pairwise facts.right_pairwise
  have hmap := sourceExceptionalPath_polymerWalk_eq_map
    Gamma qP b1 b2 pair facts
  have herase := erase_occurrenceChainCodeOfWalk_map Gamma
    (fun _ _ h => disagreementEdge_incAtDistinct Gamma
      (bitMask pair.1) (bitMask pair.2) h)
    path.indexWalk background
  rw [← hmap] at herase
  have hselectLeft : selectByBits Gamma background = outsideLeft := by
    exact select_bitsFromMask_eq_maskFamily Gamma
      (outsideMask cut (bitMask pair.1))
  rw [hselectLeft] at herase
  have hchain :
      chainCodeWeight w qP b2 Gamma label
          (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair))
          (fun _ => true)
          (eraseOccChainCode Gamma
            (occurrenceChainCodeOfWalk path.indexWalk background)) ≈
        path.polymerWalk.activityWeight w label *
          familyActivity w outsideLeft label := by
    rw [herase]
    apply chainCodeOfWalk_weight_eqv w qP b2 Gamma outsideLeft label
      path.polymerWalk (fun _ => true) path.q_true hb2seed
      hleftCompat hleftQ
    · apply List.all_eq_true.mpr
      intro _ _
      rfl
    · exact hpathCompatible
  have hselectRight : selectByBits Gamma external = outsideRight := by
    exact select_bitsFromMask_eq_maskFamily Gamma
      (outsideMask cut (bitMask pair.2))
  have hexternal : admissibleFamilyWeight w qP label
      (selectByBits Gamma external) =
        familyActivity w outsideRight label := by
    rw [hselectRight]
    unfold admissibleFamilyWeight
    rw [hrightQ, hrightCompat]
    rfl
  have hqMarked : qP
      (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair)) = true :=
    facts.right_q (exceptionalMarkedIndex Gamma b1 b2 pair)
      facts.marked_lt facts.marked_right_true
  change
    carrierCodeWeight w qP b1 b2 Gamma label
        (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair),
          eraseOccChainCode Gamma
            (occurrenceChainCodeOfWalk path.indexWalk background)) *
      admissibleFamilyWeight w qP label (selectByBits Gamma external) ≈
    (path.polymerWalk.activityWeight w label *
      familyActivity w outsideLeft label) *
      familyActivity w outsideRight label
  unfold carrierCodeWeight
  simp only [hqMarked, facts.marked_b1, Bool.true_and, if_true]
  rw [hexternal]
  exact Q'.mul_eqv_congr_right _ _ _ hchain

#print axioms erase_occurrenceChainCodeOfWalk_map
#print axioms chainCodeOfWalk_weight_eqv
#print axioms exceptionalSafeCarrierCode_mem
#print axioms sourceExceptionalPath_polymerWalk_eq_map
#print axioms exceptionalSafeCarrierCode_weight_eqv

end YMGap.Continuum.XiExceptionalSafeCarrierWeight
