/-
# Generic external-family allocator for parallel branches

One-attached parallel children need not enter the carrier walk.  This module
specializes the custom exceptional carrier to an empty terminal background
and an arbitrary external occurrence mask.  Any compatible, q-admissible
external family then factors with the canonical marked-to-bad path exactly.
An injective external encoding gives a duplicate-free target block and
singleton fibers, and the standard finite block summation closes globally.
-/

import YMGap.Continuum.XiExceptionalParallelBranchAllocator

namespace YMGap.Continuum.XiExceptionalParallelExternalFamily

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalTargetBlocks

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

def emptyOccurrenceBits (Gamma : List (Polymer L)) :
    OccBitVec Gamma.length :=
  bitsFromMask Gamma.length (fun _ => false) 0

theorem maskFamily_false : ∀ (Gamma : List (Polymer L)) (offset : Nat),
    maskFamilyFrom Gamma (fun _ => false) offset = []
  | [], _ => by simp [maskFamilyFrom]
  | _ :: Gamma, offset => by
      simp only [maskFamilyFrom, Bool.false_eq_true, ↓reduceIte]
      exact maskFamily_false Gamma (offset + 1)

theorem select_emptyOccurrenceBits (Gamma : List (Polymer L)) :
    selectByBits Gamma (emptyOccurrenceBits Gamma) = [] := by
  unfold emptyOccurrenceBits
  rw [select_bitsFromMask_eq_maskFamily]
  exact maskFamily_false Gamma 0

def parallelExternalCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length) : OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (emptyOccurrenceBits Gamma) external

theorem parallelExternalCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length) :
    parallelExternalCarrierCode Gamma qP b1 b2 entry external ∈
      occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry
    (emptyOccurrenceBits Gamma) external

/-- Exact articulation-preserving factorization: the carrier path is counted
once and all parallel children occur only in the external family factor. -/
theorem parallelExternalCarrierCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hexternalCompatible :
      familyCompatibleB (selectByBits Gamma external) = true)
    (hexternalQ : (selectByBits Gamma external).all qP = true) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  dsimp only
  have h := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry (emptyOccurrenceBits Gamma) external
    (by rw [select_emptyOccurrenceBits]; rfl)
    (by rw [select_emptyOccurrenceBits]; rfl)
    (by
      dsimp only
      intro X _ T hT
      rw [select_emptyOccurrenceBits] at hT
      cases hT)
    hexternalCompatible hexternalQ
  dsimp only at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [select_emptyOccurrenceBits]
  simp only [familyActivity_nil]
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)

theorem parallelExternalCarrierCode_injective_of_external
    {alpha : Type}
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (hexternalInjective : ∀ a b, external a = external b → a = b) :
    ∀ a b,
      parallelExternalCarrierCode Gamma qP b1 b2 (entry a) (external a) =
        parallelExternalCarrierCode Gamma qP b1 b2 (entry b) (external b) →
      a = b := by
  intro a b hcode
  apply hexternalInjective a b
  have hext := congrArg (fun code => code.external) hcode
  simpa [parallelExternalCarrierCode, exceptionalCustomCarrierCode] using hext

def parallelExternalBlock {alpha : Type}
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (sources : List alpha) : List (OccCarrierXiCodeAt Gamma) :=
  sources.map (fun a =>
    parallelExternalCarrierCode Gamma qP b1 b2 (entry a) (external a))

theorem parallelExternalBlock_nodup {alpha : Type}
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (sources : List alpha) (hsources : sources.Nodup)
    (hexternalInjective : ∀ a, a ∈ sources → ∀ b, b ∈ sources →
      external a = external b → a = b) :
    (parallelExternalBlock Gamma qP b1 b2 entry external sources).Nodup := by
  unfold parallelExternalBlock
  apply nodup_map_of_injOn _ sources hsources
  intro a ha b hb hcode
  apply hexternalInjective a ha b hb
  have hext := congrArg (fun code => code.external) hcode
  simpa [parallelExternalCarrierCode, exceptionalCustomCarrierCode] using hext

theorem parallelExternalBlock_mem {alpha : Type}
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (sources : List alpha) : ∀ code,
    code ∈ parallelExternalBlock Gamma qP b1 b2 entry external sources →
      code ∈ occurrenceCarrierXiCodes Gamma := by
  intro code hcode
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hcode
  exact parallelExternalCarrierCode_mem Gamma qP b1 b2 (entry a) (external a)

/-- Source-fiber multiplicity is one whenever external occurrence masks are
injective. -/
theorem parallelExternal_source_fiber_unique {alpha : Type}
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (hexternalInjective : ∀ a b, external a = external b → a = b)
    (a b : alpha)
    (hcode : parallelExternalCarrierCode Gamma qP b1 b2
        (entry a) (external a) =
      parallelExternalCarrierCode Gamma qP b1 b2
        (entry b) (external b)) :
    a = b :=
  parallelExternalCarrierCode_injective_of_external Gamma qP b1 b2
    entry external hexternalInjective a b hcode

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

/-- Generic finite-source closure for the external-family allocator. -/
theorem parallelExternal_global_bound {alpha : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : alpha → ExceptionalSourceEntry Gamma qP b1 b2)
    (external : alpha → OccBitVec Gamma.length)
    (sources : List alpha) (sourceWeight : alpha → Q')
    (hsources : sources.Nodup)
    (hexternalInjective : ∀ a, a ∈ sources → ∀ b, b ∈ sources →
      external a = external b → a = b)
    (hlocal : ∀ a, a ∈ sources →
      sourceWeight a ≤ occurrenceCarrierXiCodeWeight
        w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2
          (entry a) (external a))) :
    qListSum sourceWeight sources ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks sources
    (occurrenceCarrierXiCodes Gamma) sourceWeight
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun a => [parallelExternalCarrierCode Gamma qP b1 b2
      (entry a) (external a)])
  · have hmap := parallelExternalBlock_nodup Gamma qP b1 b2
      entry external sources hsources hexternalInjective
    rw [flatMap_singleton_eq_map]
    exact hmap
  · intro code hcode
    obtain ⟨a, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact parallelExternalCarrierCode_mem Gamma qP b1 b2
      (entry a) (external a)
  · intro a ha
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact hlocal a ha
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms select_emptyOccurrenceBits
#print axioms parallelExternalCarrierCode_mem
#print axioms parallelExternalCarrierCode_weight_eqv
#print axioms parallelExternalCarrierCode_injective_of_external
#print axioms parallelExternalBlock_nodup
#print axioms parallelExternalBlock_mem
#print axioms parallelExternal_source_fiber_unique
#print axioms parallelExternal_global_bound

end YMGap.Continuum.XiExceptionalParallelExternalFamily
