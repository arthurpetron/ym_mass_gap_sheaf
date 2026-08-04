/-
# Active 32-link carrier for the cutoff-one BF4 surface campaign

Every one of the 128 embedded unit-four-cube surfaces uses only 32 of the
116 literal corrected-slab links.  This module puts those links first with a
checked swap chain and proves that the other 84 normalized Haar variables
can be deleted exactly.  The proof works at the original polynomial level:
it does not evaluate a surface contraction or assume the desired
topological answer.

## Axiom gate

Finite lists, exact rational moments, and the existing block-reindex theorem
only.  No Classical.*, native_decide, sorry, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar
import YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic inactive-tail deletion -/

/-- Keep precisely the coordinate prefix belonging to `blocks` quaternion
variables. -/
def trimQuaternionPolynomial (blocks : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term => (term.1.take (4 * blocks), term.2)

/-- Every exponent beyond the declared quaternion prefix is literally zero.
This is stronger than mere Haar support: zero padding is allowed. -/
def QuaternionTailZeroAfter (blocks : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    allZero (term.1.drop (4 * blocks)) = true

def quaternionTailZeroAfterCheck
    (blocks : Nat) (polynomial : RatPoly) : Bool :=
  polynomial.all fun term => allZero (term.1.drop (4 * blocks))

theorem quaternionTailZeroAfter_of_check
    {blocks : Nat} {polynomial : RatPoly}
    (hcheck : quaternionTailZeroAfterCheck blocks polynomial = true) :
    QuaternionTailZeroAfter blocks polynomial := by
  intro term hterm
  exact List.all_eq_true.mp hcheck term hterm

private theorem exponentAt_take_of_lt (monomial : List Nat) :
    ∀ count coordinate : Nat, coordinate < count →
      exponentAt (monomial.take count) coordinate =
        exponentAt monomial coordinate
  | 0, _, hcoordinate => by omega
  | count + 1, 0, _ => by
      cases monomial <;> simp [exponentAt]
  | count + 1, coordinate + 1, hcoordinate => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons _ rest =>
          simp only [List.take_succ_cons]
          change exponentAt (rest.take count) coordinate =
            exponentAt rest coordinate
          exact exponentAt_take_of_lt rest count coordinate (by omega)

private theorem allZero_drop_of_allZero :
    ∀ (values : List Nat) (count : Nat),
      allZero values = true → allZero (values.drop count) = true
  | [], count, _ => by cases count <;> rfl
  | _ :: _, 0, hzero => hzero
  | value :: rest, count + 1, hzero => by
      simp only [allZero, Bool.and_eq_true] at hzero
      exact allZero_drop_of_allZero rest count hzero.2

private theorem exponentAt_eq_zero_of_allZero :
    ∀ (values : List Nat) (coordinate : Nat),
      allZero values = true → exponentAt values coordinate = 0
  | [], _, _ => by simp [exponentAt]
  | value :: rest, 0, hzero => by
      simp only [allZero, Bool.and_eq_true, decide_eq_true_eq] at hzero
      simpa [exponentAt] using hzero.1
  | value :: rest, coordinate + 1, hzero => by
      simp only [allZero, Bool.and_eq_true] at hzero
      simpa [exponentAt] using
        exponentAt_eq_zero_of_allZero rest coordinate hzero.2

private theorem quaternionHaarPrefix_eq_one_of_allZero
    (blocks : Nat) (monomial : List Nat)
    (hzero : allZero monomial = true) :
    quaternionHaarPrefix blocks monomial ≈ 1 := by
  induction blocks generalizing monomial with
  | zero => exact Q'.eqv_refl 1
  | succ blocks induction =>
      unfold quaternionHaarPrefix
      rw [exponentAt_eq_zero_of_allZero monomial 0 hzero,
        exponentAt_eq_zero_of_allZero monomial 1 hzero,
        exponentAt_eq_zero_of_allZero monomial 2 hzero,
        exponentAt_eq_zero_of_allZero monomial 3 hzero]
      exact Q'.eqv_trans _
        (1 * quaternionHaarPrefix blocks (monomial.drop 4)) _
        (Q'.mul_eqv_congr_right _ _ _ sphereMoment4_one)
        (Q'.eqv_trans _ (1 * 1) _
          (Q'.mul_eqv_congr_left _ _ _
            (induction (monomial.drop 4)
              (allZero_drop_of_allZero monomial 4 hzero)))
          (Q'.one_mul_eqv 1))

private theorem quaternionHaarMono_eq_one_of_allZero
    (blocks : Nat) (monomial : List Nat)
    (hlength : monomial.length = 4 * blocks)
    (hzero : allZero monomial = true) :
    quaternionHaarMono blocks monomial ≈ 1 := by
  unfold quaternionHaarMono
  rw [if_pos (by
    rw [List.drop_eq_nil_of_le (Nat.le_of_eq hlength)]
    rfl)]
  exact quaternionHaarPrefix_eq_one_of_allZero blocks monomial hzero

private theorem quaternionHaarPrefix_append_exact_local
    (sourceBlocks targetBlocks : Nat) :
    ∀ source target : List Nat,
      source.length = 4 * sourceBlocks →
      quaternionHaarPrefix (sourceBlocks + targetBlocks)
          (source ++ target) ≈
        quaternionHaarPrefix sourceBlocks source *
          quaternionHaarPrefix targetBlocks target
  | source, target, hsource => by
      induction sourceBlocks generalizing source with
      | zero =>
          have hnil : source = [] := by
            cases source with
            | nil => rfl
            | cons _ _ => simp at hsource
          subst source
          simpa [quaternionHaarPrefix] using
            (Q'.eqv_symm
              (Q'.one_mul_eqv
                (quaternionHaarPrefix targetBlocks target)))
      | succ blocks induction =>
          cases source with
          | nil => simp at hsource
          | cons x0 source1 =>
              cases source1 with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at hsource
                  omega
              | cons x1 source2 =>
                  cases source2 with
                  | nil =>
                      simp only [List.length_cons, List.length_nil] at hsource
                      omega
                  | cons x2 source3 =>
                      cases source3 with
                      | nil =>
                          simp only [List.length_cons, List.length_nil] at hsource
                          omega
                      | cons x3 tail =>
                          have htail : tail.length = 4 * blocks := by
                            simp at hsource
                            omega
                          rw [show blocks + 1 + targetBlocks =
                              (blocks + targetBlocks) + 1 by omega]
                          simp only [quaternionHaarPrefix, exponentAt,
                            List.getD_cons_zero, List.getD_cons_succ,
                            List.drop_succ_cons, List.drop_zero]
                          exact Q'.eqv_trans _ _ _
                            (Q'.mul_eqv_congr_left _ _ _
                              (induction tail htail))
                            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem quaternionHaarMono_append_exact_local
    (sourceBlocks targetBlocks : Nat)
    (source target : List Nat)
    (hsource : source.length = 4 * sourceBlocks)
    (htarget : target.length = 4 * targetBlocks) :
    quaternionHaarMono (sourceBlocks + targetBlocks)
        (source ++ target) ≈
      quaternionHaarMono sourceBlocks source *
        quaternionHaarMono targetBlocks target := by
  have htotal : (source ++ target).length =
      4 * (sourceBlocks + targetBlocks) := by
    simp [hsource, htarget]
    omega
  unfold quaternionHaarMono
  rw [if_pos (by
      rw [List.drop_eq_nil_of_le (Nat.le_of_eq htotal)]
      rfl),
    if_pos (by
      rw [List.drop_eq_nil_of_le (Nat.le_of_eq hsource)]
      rfl),
    if_pos (by
      rw [List.drop_eq_nil_of_le (Nat.le_of_eq htarget)]
      rfl)]
  exact quaternionHaarPrefix_append_exact_local
    sourceBlocks targetBlocks source target hsource

private theorem quaternionHaarMono_trim_inactive
    (active inactive : Nat) (monomial : List Nat)
    (hlength : monomial.length = 4 * (active + inactive))
    (hzero : allZero (monomial.drop (4 * active)) = true) :
    quaternionHaarMono (active + inactive) monomial ≈
      quaternionHaarMono active (monomial.take (4 * active)) := by
  let source := monomial.take (4 * active)
  let target := monomial.drop (4 * active)
  have hprefix : 4 * active ≤ monomial.length := by
    rw [hlength]
    omega
  have hsource : source.length = 4 * active := by
    unfold source
    rw [List.length_take, Nat.min_eq_left hprefix]
  have htarget : target.length = 4 * inactive := by
    unfold target
    rw [List.length_drop, hlength]
    omega
  have hsplit : source ++ target = monomial := by
    exact List.take_append_drop (4 * active) monomial
  change quaternionHaarMono (active + inactive) monomial ≈
    quaternionHaarMono active source
  exact Q'.eqv_trans _
    (quaternionHaarMono (active + inactive) (source ++ target)) _
    (Q'.eqv_of_eq (congrArg (quaternionHaarMono (active + inactive))
      hsplit.symm))
    (Q'.eqv_trans _ _ _
      (quaternionHaarMono_append_exact_local
        active inactive source target hsource htarget)
      (Q'.eqv_trans _
        (quaternionHaarMono active source * 1) _
        (Q'.mul_eqv_congr_left _ _ _
          (quaternionHaarMono_eq_one_of_allZero
            inactive target htarget hzero))
        (Q'.mul_one_eqv _)))

/-- Exact deletion of a zero-padded normalized Haar tail.  The exact-length
hypothesis matches block reindexing, which pads every term to the full
carrier length. -/
theorem quaternionHaar_trim_inactive
    (active inactive : Nat) : ∀ polynomial : RatPoly,
    (∀ term, term ∈ polynomial →
      term.1.length = 4 * (active + inactive)) →
    QuaternionTailZeroAfter active polynomial →
    quaternionHaar (active + inactive) polynomial ≈
      quaternionHaar active (trimQuaternionPolynomial active polynomial)
  | [], _, _ => Q'.eqv_refl 0
  | term :: rest, hlength, hzero => by
      change
        term.2 * quaternionHaarMono (active + inactive) term.1 +
              quaternionHaar (active + inactive) rest ≈
          term.2 * quaternionHaarMono active
              (term.1.take (4 * active)) +
            quaternionHaar active
              (trimQuaternionPolynomial active rest)
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (quaternionHaarMono_trim_inactive active inactive term.1
            (hlength term (by simp))
            (hzero term (by simp))))
        (quaternionHaar_trim_inactive active inactive rest
          (fun other hother => hlength other (by simp [hother]))
          (fun other hother => hzero other (by simp [hother])))

/-! ## 2. The checked 32-link surface carrier -/

/-- Literal raw link blocks touched by the 24 unit-four-cube faces, in the
deterministic order used by the active contractor. -/
def bf4SurfaceActiveRawBlocks : List Nat :=
  [0, 3, 2, 1, 6, 5, 4, 9, 8, 7, 11, 10, 13, 12, 15, 14,
   17, 16, 19, 18, 21, 20, 23, 22, 27, 30, 34, 33, 42, 43, 50, 57]

theorem bf4SurfaceActiveRawBlocks_spec :
    bf4SurfaceActiveRawBlocks.length = 32 ∧
    bf4SurfaceActiveRawBlocks.Nodup ∧
    bf4SurfaceActiveRawBlocks.all (fun block => decide (block < 116)) = true := by
  decide

/-- Selection-sort swaps putting the 32 active blocks first. -/
def bf4SurfaceActiveCarrierSwaps : List RawQuaternionBlockSwap :=
  [⟨1, 3⟩, ⟨4, 6⟩, ⟨7, 9⟩, ⟨10, 11⟩, ⟨12, 13⟩,
   ⟨14, 15⟩, ⟨16, 17⟩, ⟨18, 19⟩, ⟨20, 21⟩, ⟨22, 23⟩,
   ⟨24, 27⟩, ⟨25, 30⟩, ⟨26, 34⟩, ⟨27, 33⟩, ⟨28, 42⟩,
   ⟨29, 43⟩, ⟨30, 50⟩, ⟨31, 57⟩]

theorem bf4SurfaceActiveCarrierSwaps_valid :
    rawQuaternionBlockSwapsValid 116
      bf4SurfaceActiveCarrierSwaps = true := by
  decide

def bf4SurfaceActiveCarrierSteps :
    List (QuaternionBlockInvolution 116) :=
  certifyRawQuaternionBlockSwaps bf4SurfaceActiveCarrierSwaps
    bf4SurfaceActiveCarrierSwaps_valid

def reindexBF4SurfaceActiveCarrier (polynomial : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain bf4SurfaceActiveCarrierSteps polynomial

theorem bf4SurfaceActiveCarrier_source_order :
    (List.range 32).map
        (quaternionBlockSwapChainSource bf4SurfaceActiveCarrierSteps) =
      bf4SurfaceActiveRawBlocks := by
  decide

/-- The complementary raw blocks, in the exact order left by the same swap
chain.  Naming this table keeps subsequent finite incidence checks free of
dependent permutation proof data. -/
def bf4SurfaceInactiveRawBlocks : List Nat :=
  [32, 24, 26, 35, 36, 37, 38, 39, 40, 41, 28, 29, 44, 45,
   46, 47, 48, 49, 25, 51, 52, 53, 54, 55, 56, 31, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
   74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
   88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101,
   102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
   114, 115]

theorem bf4SurfaceInactiveRawBlocks_spec :
    bf4SurfaceInactiveRawBlocks.length = 84 ∧
    bf4SurfaceInactiveRawBlocks.Nodup ∧
    bf4SurfaceInactiveRawBlocks.all
      (fun block => decide (block < 116)) = true := by
  decide

/-- The inactive source table is the literal tail of the checked carrier
permutation. -/
theorem bf4SurfaceInactiveCarrier_source_order :
    (List.range 84).map (fun offset =>
      quaternionBlockSwapChainSource
        bf4SurfaceActiveCarrierSteps (32 + offset)) =
      bf4SurfaceInactiveRawBlocks := by
  decide

theorem bf4SurfaceInactiveCarrier_source
    (offset : Nat) (hoffset : offset < 84) :
    quaternionBlockSwapChainSource
        bf4SurfaceActiveCarrierSteps (32 + offset) =
      bf4SurfaceInactiveRawBlocks.getD offset 0 := by
  have hleft :
      ((List.range 84).map (fun index =>
        quaternionBlockSwapChainSource
          bf4SurfaceActiveCarrierSteps (32 + index))).getD offset 0 =
        quaternionBlockSwapChainSource
          bf4SurfaceActiveCarrierSteps (32 + offset) := by
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_range hoffset]
    rfl
  exact Eq.trans hleft.symm
    (congrArg (fun values : List Nat => values.getD offset 0)
      bf4SurfaceInactiveCarrier_source_order)

theorem reindexBF4SurfaceActiveCarrier_haar
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial) :
    quaternionHaar 116 (reindexBF4SurfaceActiveCarrier polynomial) ≈
      quaternionHaar 116 polynomial := by
  exact quaternionHaar_applyQuaternionBlockSwapChain
    bf4SurfaceActiveCarrierSteps polynomial hsupport

private theorem applyQuaternionBlockSwapChain_term_length
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks)),
      swaps ≠ [] → ∀ (polynomial : RatPoly) (term : RatTerm),
      term ∈ applyQuaternionBlockSwapChain swaps polynomial →
      term.1.length = 4 * blocks
  | [], hne, _, _, _ => False.elim (hne rfl)
  | first :: rest, _, polynomial, term, hterm => by
      cases rest with
      | nil =>
          obtain ⟨source, _, rfl⟩ := List.mem_map.mp hterm
          exact reindexQuaternionExponents_length first source.1
      | cons next tail =>
          exact applyQuaternionBlockSwapChain_term_length
            (next :: tail) (by simp)
            (reindexQuaternionPolynomial first polynomial) term hterm

theorem reindexBF4SurfaceActiveCarrier_term_length
    (polynomial : RatPoly) (term : RatTerm)
    (hterm : term ∈ reindexBF4SurfaceActiveCarrier polynomial) :
    term.1.length = 4 * 116 := by
  exact applyQuaternionBlockSwapChain_term_length
    bf4SurfaceActiveCarrierSteps (by decide) polynomial term hterm

/-! ## 3. Literal surface factors use no other blocks -/

private theorem drop_monoMul_local :
    ∀ (count : Nat) (left right : List Nat),
      (monoMul left right).drop count =
        monoMul (left.drop count) (right.drop count)
  | 0, _, _ => rfl
  | count + 1, [], right => by simp [monoMul]
  | count + 1, left, [] => by
      rw [monoMul_right_nil_local, List.drop_nil,
        monoMul_right_nil_local]
  | count + 1, _ :: left, _ :: right => by
      simp only [monoMul, List.drop_succ_cons]
      exact drop_monoMul_local count left right
where
  monoMul_right_nil_local : ∀ monomial : List Nat,
      monoMul monomial [] = monomial
    | [] => rfl
    | _ :: _ => by simp only [monoMul]

private theorem allZero_monoMul_local : ∀ left right : List Nat,
    allZero (monoMul left right) = (allZero left && allZero right)
  | left, right => by
      induction left generalizing right with
      | nil => simp [monoMul, allZero]
      | cons leftHead left induction =>
          cases right with
          | nil => simp [monoMul, allZero]
          | cons rightHead right =>
              simp [monoMul, allZero, induction right,
                Nat.add_eq_zero_iff, Bool.and_assoc,
                Bool.and_left_comm]

private theorem mem_polyMul_local {left right : RatPoly} {term : RatTerm}
    (hterm : term ∈ polyMul left right) :
    ∃ source, source ∈ left ∧ ∃ target, target ∈ right ∧
      term = (monoMul source.1 target.1, source.2 * target.2) := by
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨source, hsource, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨target, htarget, rfl⟩ := hterm
  exact ⟨source, hsource, target, htarget, rfl⟩

theorem QuaternionTailZeroAfter.polyMul
    {blocks : Nat} {left right : RatPoly}
    (hleft : QuaternionTailZeroAfter blocks left)
    (hright : QuaternionTailZeroAfter blocks right) :
  QuaternionTailZeroAfter blocks (polyMul left right) := by
  intro term hterm
  obtain ⟨source, hsource, target, htarget, rfl⟩ :=
    mem_polyMul_local hterm
  rw [drop_monoMul_local, allZero_monoMul_local,
    hleft source hsource, hright target htarget]
  decide

private theorem applyQuaternionBlockSwapChain_polyMul
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (left right : RatPoly),
      applyQuaternionBlockSwapChain swaps (polyMul left right) =
        polyMul (applyQuaternionBlockSwapChain swaps left)
          (applyQuaternionBlockSwapChain swaps right)
  | [], _, _ => rfl
  | swap :: rest, left, right => by
      simp only [applyQuaternionBlockSwapChain]
      rw [reindexQuaternionPolynomial_mul,
        applyQuaternionBlockSwapChain_polyMul rest]

def bf4SurfaceActiveSpinFactor (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial
    (correctedSlabPlaquettePolynomial 1 face).scalar spin

/-- Every selected face of each of the certified 128 surfaces lies in the
24-face unit-four-cube carrier.  This is a small bit-mask support certificate,
separate from the polynomial proof below. -/
def bf4EmbeddedSurfaceActiveFaceSupportCheck : Bool :=
  binarySurfaceMasks.all fun compactMask =>
    (boundaryCompleteSlabPlaquettes 1).all fun face =>
      decide
        (embeddedSurfaceLabelling compactMask
              ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 0 ∨
          (boundaryCompleteSlabPlaquettes 1).idxOf face ∈
            activeHypercubeSlabFaceIds)

theorem bf4EmbeddedSurfaceActiveFaceSupportCheck_true :
    bf4EmbeddedSurfaceActiveFaceSupportCheck = true := by
  decide

/-- Only the 24 potentially selected four-edge plaquettes are checked against
the 84 inactive target blocks.  The check runs entirely on geometry and the
proved swap-chain source map; it does not expand or reindex a polynomial. -/
def bf4SurfaceActiveFactorTailCheck : Bool :=
  (boundaryCompleteSlabPlaquettes 1).all fun face =>
    if (boundaryCompleteSlabPlaquettes 1).idxOf face ∈
        activeHypercubeSlabFaceIds then
      bf4SurfaceInactiveRawBlocks.all fun source =>
        decide (slabFaceBlockDegree source face = 0)
    else true

theorem bf4SurfaceActiveFactorTailCheck_true :
    bf4SurfaceActiveFactorTailCheck = true := by
  decide

private theorem getD_mem_of_lt {A : Type} (fallback : A) :
    ∀ (items : List A) (index : Nat), index < items.length →
      items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => by simp
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ, List.mem_cons]
      exact Or.inr (getD_mem_of_lt fallback tail index (by simpa using hindex))

private theorem bf4SurfaceActiveSpinFactor_source_degree_zero
    (face : Z4Plaq) (hface : face ∈ boundaryCompleteSlabPlaquettes 1)
    (spin : Nat) (hspin : spin ≤ 1) (source : Nat)
    (hincidence : slabFaceBlockDegree source face = 0) :
    HasQuaternionBlockDegree source 0
      (bf4SurfaceActiveSpinFactor face spin) := by
  have hcases : spin = 0 ∨ spin = 1 := by omega
  rcases hcases with hzero | hone
  · subst spin
    simpa [bf4SurfaceActiveSpinFactor] using
      hasQuaternionBlockDegree_one source
  · subst spin
    simpa [bf4SurfaceActiveSpinFactor, hincidence] using
      (correctedSlabPlaquetteScalar_blockDegree source hface).smul 2

private theorem exponentAt_le_quaternionBlockDegree
    (monomial : List Nat) (coordinate : Nat) :
    exponentAt monomial coordinate ≤
      quaternionBlockDegree monomial (coordinate / 4) := by
  have hcomponent : coordinate % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcoordinateEq :
      coordinate = 4 * (coordinate / 4) + coordinate % 4 := by
    omega
  have hcases :
      coordinate % 4 = 0 ∨ coordinate % 4 = 1 ∨
        coordinate % 4 = 2 ∨ coordinate % 4 = 3 := by
    omega
  have hExponent :
      exponentAt monomial coordinate =
        exponentAt monomial
          (4 * (coordinate / 4) + coordinate % 4) :=
    congrArg (exponentAt monomial) hcoordinateEq
  rw [hExponent]
  unfold quaternionBlockDegree
  rcases hcases with h0 | h1 | h2 | h3
  · simp only [h0, Nat.add_zero]
    omega
  · rw [h1]
    omega
  · rw [h2]
    omega
  · rw [h3]
    omega

private theorem allZero_of_exponentAt_zero
    (values : List Nat)
    (hzero : ∀ coordinate, coordinate < values.length →
      exponentAt values coordinate = 0) :
    allZero values = true := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      have hhead := hzero 0 (by simp)
      have htail : ∀ coordinate, coordinate < rest.length →
          exponentAt rest coordinate = 0 := by
        intro coordinate hcoordinate
        simpa [exponentAt] using hzero (coordinate + 1) (by simp [hcoordinate])
      simp [exponentAt] at hhead
      simp [allZero, hhead, induction htail]

private theorem tailZero_of_inactive_block_degree_zero
    (polynomial : RatPoly)
    (hlength : ∀ term, term ∈ polynomial → term.1.length = 4 * 116)
    (hdegree : ∀ block, 32 ≤ block → block < 116 →
      QuaternionBlockDegreeAtMost block 0 polynomial) :
    QuaternionTailZeroAfter 32 polynomial := by
  intro term hterm
  let tail := term.1.drop (4 * 32)
  apply allZero_of_exponentAt_zero tail
  intro coordinate hcoordinate
  have htailLength : tail.length = 4 * 84 := by
    unfold tail
    rw [List.length_drop, hlength term hterm]
  have hglobal : 4 * 32 + coordinate < 4 * 116 := by
    rw [htailLength] at hcoordinate
    omega
  have hblockLower : 32 ≤ (4 * 32 + coordinate) / 4 := by omega
  have hblockUpper : (4 * 32 + coordinate) / 4 < 116 := by omega
  have hzeroDegree := hdegree ((4 * 32 + coordinate) / 4)
    hblockLower hblockUpper term hterm
  have hcoordLe := exponentAt_le_quaternionBlockDegree
    term.1 (4 * 32 + coordinate)
  have hcoordZero : exponentAt term.1 (4 * 32 + coordinate) = 0 := by
    omega
  unfold tail
  rw [exponentAt_drop]
  simpa [Nat.add_assoc] using hcoordZero

theorem reindexBF4SurfaceActiveSpinFactor_tailZero
    (face : Z4Plaq) (hface : face ∈ boundaryCompleteSlabPlaquettes 1)
    (hactive : (boundaryCompleteSlabPlaquettes 1).idxOf face ∈
      activeHypercubeSlabFaceIds)
    (spin : Nat) (hspin : spin ≤ 1) :
    QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier
        (bf4SurfaceActiveSpinFactor face spin)) := by
  have hfaceCheck := List.all_eq_true.mp
    bf4SurfaceActiveFactorTailCheck_true face hface
  rw [if_pos hactive] at hfaceCheck
  apply tailZero_of_inactive_block_degree_zero
  · exact reindexBF4SurfaceActiveCarrier_term_length _
  · intro block hblockLower hblockUpper
    have hoffset : block - 32 < 84 := by omega
    have hblockEq : 32 + (block - 32) = block := by omega
    let source := bf4SurfaceInactiveRawBlocks.getD (block - 32) 0
    have hsourceMem : source ∈ bf4SurfaceInactiveRawBlocks :=
      getD_mem_of_lt 0 bf4SurfaceInactiveRawBlocks (block - 32) (by
        rw [bf4SurfaceInactiveRawBlocks_spec.1]
        exact hoffset)
    have hsourceCheck := of_decide_eq_true
      (List.all_eq_true.mp hfaceCheck
      source hsourceMem
      )
    apply applyQuaternionBlockSwapChain_degreeAtMost
      (swaps := bf4SurfaceActiveCarrierSteps)
      (block := block) (maxDegree := 0)
      hblockUpper (bf4SurfaceActiveSpinFactor face spin)
    have hsourceEq :
        quaternionBlockSwapChainSource
          bf4SurfaceActiveCarrierSteps block = source := by
      rw [← hblockEq]
      exact bf4SurfaceInactiveCarrier_source (block - 32) hoffset
    intro term hterm
    exact Nat.le_of_eq
      (bf4SurfaceActiveSpinFactor_source_degree_zero
        face hface spin hspin
        (quaternionBlockSwapChainSource
          bf4SurfaceActiveCarrierSteps block)
        (by simpa [hsourceEq] using hsourceCheck) term hterm)

private theorem reindexBF4SurfaceActiveCarrier_polyOne_tailZero :
    QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier polyOne) := by
  exact quaternionTailZeroAfter_of_check (by decide)

theorem reindexBF4SurfacePlaquetteFactor_tailZero
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks)
    (face : Z4Plaq)
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier
        (correctedSlabPlaquetteSpinFactor 1
          (embeddedSurfaceLabelling compactMask) face)) := by
  let faceId := (boundaryCompleteSlabPlaquettes 1).idxOf face
  let spin := embeddedSurfaceLabelling compactMask faceId
  have hsupportCheck := List.all_eq_true.mp
    bf4EmbeddedSurfaceActiveFaceSupportCheck_true compactMask hmask
  have hfaceSupport := of_decide_eq_true
    (List.all_eq_true.mp hsupportCheck face hface)
  have hspin : spin ≤ 1 := embeddedSurfaceLabelling_le_one compactMask faceId
  have hcases : spin = 0 ∨ spin = 1 := by omega
  rcases hcases with hzero | hone
  · unfold correctedSlabPlaquetteSpinFactor
    change QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier
        (characterPolynomial
          (correctedSlabPlaquettePolynomial 1 face).scalar spin))
    rw [hzero]
    exact reindexBF4SurfaceActiveCarrier_polyOne_tailZero
  · have hactive : faceId ∈ activeHypercubeSlabFaceIds := by
      rcases hfaceSupport with hlabelZero | hactive
      · change spin = 0 at hlabelZero
        omega
      · exact hactive
    unfold correctedSlabPlaquetteSpinFactor
    exact reindexBF4SurfaceActiveSpinFactor_tailZero face hface
      hactive spin hspin

theorem reindexBF4SurfaceFactorProduct_tailZero
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks) :
    ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces →
      face ∈ boundaryCompleteSlabPlaquettes 1) →
    QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier
        (faces.foldr
          (fun face total => polyMul
            (correctedSlabPlaquetteSpinFactor 1
              (embeddedSurfaceLabelling compactMask) face)
            total)
          polyOne))
  | [], _ => reindexBF4SurfaceActiveCarrier_polyOne_tailZero
  | face :: rest, hfaces => by
      simp only [List.foldr]
      unfold reindexBF4SurfaceActiveCarrier
      rw [applyQuaternionBlockSwapChain_polyMul]
      exact QuaternionTailZeroAfter.polyMul
        (reindexBF4SurfacePlaquetteFactor_tailZero compactMask hmask face
          (hfaces face List.mem_cons_self))
        (reindexBF4SurfaceFactorProduct_tailZero compactMask hmask rest
          (fun other hother =>
            hfaces other (List.mem_cons_of_mem face hother)))

theorem reindexBF4EmbeddedSurfaceIntegrand_tailZero
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks) :
    QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier
        (exactCorrectedSlabSpinNetworkIntegrand 1
          (embeddedSurfaceLabelling compactMask))) := by
  unfold exactCorrectedSlabSpinNetworkIntegrand
  exact reindexBF4SurfaceFactorProduct_tailZero compactMask hmask
    (boundaryCompleteSlabPlaquettes 1) (fun _ hface => hface)

/-! ## 4. The actual 116-to-32 surface bridge -/

def embeddedSurfaceActivePolynomial (compactMask : Nat) : RatPoly :=
  trimQuaternionPolynomial 32
    (reindexBF4SurfaceActiveCarrier
      (exactCorrectedSlabSpinNetworkIntegrand 1
        (embeddedSurfaceLabelling compactMask)))

def embeddedSurfaceActiveHaar (compactMask : Nat) : Q' :=
  quaternionHaar 32 (embeddedSurfaceActivePolynomial compactMask)

/-- Every actual embedded BF4 surface coefficient is exactly its normalized
32-link active-carrier integral.  The 84 deleted variables have been proved
absent and contribute normalized Haar mass one. -/
theorem exactEmbeddedSurfaceHaarCoefficient_eq_active
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks) :
    exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask) ≈
      embeddedSurfaceActiveHaar compactMask := by
  let polynomial := exactCorrectedSlabSpinNetworkIntegrand 1
    (embeddedSurfaceLabelling compactMask)
  have hsupport : SupportedQuaternionBlocks 116 polynomial := by
    simpa [polynomial] using
      exactCorrectedSlabSpinNetworkIntegrand_supported 1
        (embeddedSurfaceLabelling compactMask)
  have hreindex := reindexBF4SurfaceActiveCarrier_haar polynomial hsupport
  have htrim := quaternionHaar_trim_inactive 32 84
    (reindexBF4SurfaceActiveCarrier polynomial)
    (fun term hterm => by
      have := reindexBF4SurfaceActiveCarrier_term_length
        polynomial term hterm
      simpa using this)
    (by
      simpa [polynomial] using
        reindexBF4EmbeddedSurfaceIntegrand_tailZero compactMask hmask)
  unfold exactCorrectedSlabHaarCoefficient embeddedSurfaceActiveHaar
    embeddedSurfaceActivePolynomial
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hreindex) (by simpa using htrim)

/-- The already-proved five-based-cycle Haar marginal and the literal
32-link active carrier are the same exact rational value on every certified
surface.  This triangulates the two independent reductions of the original
116-link coefficient. -/
theorem embeddedSurfaceBasedCycleFive_eq_active
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks) :
    quaternionHaar 5
        (embeddedSurfaceBasedCycleFivePolynomial compactMask) ≈
      embeddedSurfaceActiveHaar compactMask := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (exactEmbeddedSurfaceHaarCoefficient_eq_basedCycleFive compactMask))
    (exactEmbeddedSurfaceHaarCoefficient_eq_active compactMask hmask)

/-- Exact reduction of the remaining closed-surface bridge to 128
32-variable active-carrier contractions. -/
theorem cutoffOneClosedSurfaceTopologicalAmplitude_of_active
    (hactive : ∀ compactMask : Nat,
      compactMask ∈ binarySurfaceMasks →
      embeddedSurfaceActiveHaar compactMask ≈
        surfaceTopologicalHaarAmplitude compactMask) :
    CutoffOneClosedSurfaceTopologicalAmplitude := by
  apply cutoffOneClosedSurfaceTopologicalAmplitude_of_basedCycleFive
  intro compactMask hmask
  exact Q'.eqv_trans _ _ _
    (embeddedSurfaceBasedCycleFive_eq_active compactMask hmask)
    (hactive compactMask hmask)

end YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier.quaternionHaar_trim_inactive
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier.reindexBF4SurfaceActiveCarrier_haar
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier.exactEmbeddedSurfaceHaarCoefficient_eq_active
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier.embeddedSurfaceBasedCycleFive_eq_active
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier.cutoffOneClosedSurfaceTopologicalAmplitude_of_active
