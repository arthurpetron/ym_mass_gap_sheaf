/-
# Structural Fubini for at-most-six fundamental block words

The cutoff-one geometry supplies, at each physical link, an ordered list of
at most six oriented fundamental matrix coefficients.  The established total
local Haar dispatcher instead uses the seven-constructor carrier
`CutoffOneHaarWord`.  This leaf gives the exact constructive bridge.

The input list is retained as data together with its proved length bound; the
conversion neither truncates nor inserts a default branch.  A bounded local
factor word is reconciled with the dispatcher's branch-specific association
only after finite-product Haar, beneath an arbitrary independent spectator.
The final theorem iterates that one-block result over pairwise distinct
in-range blocks while retaining the factor lists structurally.  It never
forms a Cartesian family of local choices or a Boolean assignment space.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct

namespace YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization
open YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

/-! ## 1. A proof-carrying nontruncating word -/

/-- An ordered fundamental word whose literal list is proved to have length
at most six.  The list, rather than a bounded-function encoding, remains the
primary data. -/
structure AtMostSixFundamentalWord where
  occurrences : List FundamentalOccurrence
  length_le_six : occurrences.length ≤ 6

/-- Total conversion of a proved-bounded list into the seven exact dispatcher
branches.  The eighth pattern is contradictory; there is no fallback word. -/
private def toCutoffOneHaarWord :
    (occurrences : List FundamentalOccurrence) →
      occurrences.length ≤ 6 → CutoffOneHaarWord
  | [], _ => .v0
  | first :: [], _ => .v1 first
  | first :: second :: [], _ => .v2 first second
  | first :: second :: third :: [], _ => .v3 first second third
  | first :: second :: third :: fourth :: [], _ =>
      .v4 first second third fourth
  | first :: second :: third :: fourth :: fifth :: [], _ =>
      .v5 first second third fourth fifth
  | first :: second :: third :: fourth :: fifth :: sixth :: [], _ =>
      .v6 first second third fourth fifth sixth
  | _first :: _second :: _third :: _fourth :: _fifth :: _sixth ::
      _seventh :: _rest, hlength => by
      simp only [List.length_cons] at hlength
      omega

namespace AtMostSixFundamentalWord

/-- The exact dispatcher word selected by the retained occurrence list. -/
def toHaarWord (word : AtMostSixFundamentalWord) : CutoffOneHaarWord :=
  toCutoffOneHaarWord word.occurrences word.length_le_six

/-- The ordered list of honest complex coefficient factors on one block. -/
def factorWord (word : AtMostSixFundamentalWord)
    (block : Nat) : List ComplexRatPoly :=
  word.occurrences.map (fundamentalOccurrenceCoefficient block)

private theorem valence_toCutoffOneHaarWord :
    ∀ (occurrences : List FundamentalOccurrence)
      (hlength : occurrences.length ≤ 6),
      valence (toCutoffOneHaarWord occurrences hlength) =
        occurrences.length
  | [], _ => rfl
  | _first :: [], _ => rfl
  | _first :: _second :: [], _ => rfl
  | _first :: _second :: _third :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: _sixth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: _sixth ::
      _seventh :: _rest, hlength => by
      simp only [List.length_cons] at hlength
      omega

/-- Conversion preserves the literal local valence exactly. -/
theorem valence_toHaarWord (word : AtMostSixFundamentalWord) :
    valence word.toHaarWord = word.occurrences.length := by
  rcases word with ⟨occurrences, hlength⟩
  exact valence_toCutoffOneHaarWord occurrences hlength

end AtMostSixFundamentalWord

/-! ## 2. Association bridges under finite-product Haar -/

/-- A right-associated nonempty oriented word and its tail-first factor list
have the same Haar value beneath every spectator.  The arbitrary spectator is
the induction invariant; no bare Haar equivalence is multiplied by context. -/
private theorem finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
    (blockCount block : Nat) :
    ∀ (spectator : ComplexRatPoly) (first : FundamentalOccurrence)
      (rest : List FundamentalOccurrence),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (orientedFundamentalWord block first rest)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              ((first :: rest).map
                (fundamentalOccurrenceCoefficient block)))))
  | spectator, first, [] => by
      apply rationalComplexEqv_symm
      simpa only [orientedFundamentalWord, List.map,
        complexRatPolyProduct] using
        (rationalComplexEqv_trans
          (finiteProductHaarComplex_mul_assoc_context blockCount
            spectator
            (fundamentalOccurrenceCoefficient block first)
            complexRatPolyOne)
          (finiteProductHaarComplex_mul_one blockCount
            (complexRatPolyMul spectator
              (fundamentalOccurrenceCoefficient block first))))
  | spectator, first, second :: rest => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc_context blockCount
          spectator (fundamentalOccurrenceCoefficient block first)
          (orientedFundamentalWord block second rest)) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
          blockCount block
          (complexRatPolyMul spectator
            (fundamentalOccurrenceCoefficient block first))
          second rest) ?_
      simpa only [orientedFundamentalWord, List.map,
        complexRatPolyProduct] using
        (finiteProductHaarComplex_mul_assoc blockCount spectator
          (fundamentalOccurrenceCoefficient block first)
          (complexRatPolyProduct
            ((second :: rest).map
              (fundamentalOccurrenceCoefficient block))))

/-- A nonempty left fold and the matching tail-first factor word have the
same Haar value beneath an arbitrary spectator.  The proof moves the
spectator around the complete factor word using an explicit `List.Perm` and
the accumulated-product theorem; it does not appeal to raw associativity. -/
private theorem finiteProductHaarComplex_mul_foldl_eq_mul_product_cons
    (blockCount : Nat) (spectator first : ComplexRatPoly)
    (rest : List ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (rest.foldl complexRatPolyMul first)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct (first :: rest)))) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_comm blockCount spectator
      (rest.foldl complexRatPolyMul first)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc_context blockCount
          (rest.foldl complexRatPolyMul first)
          spectator complexRatPolyOne)
        (finiteProductHaarComplex_mul_one blockCount
          (complexRatPolyMul
            (rest.foldl complexRatPolyMul first) spectator)))) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
      blockCount first rest [spectator]) ?_
  have hperm :
      (first :: rest ++ [spectator]).Perm
        (spectator :: first :: rest) := by
    simpa only [List.cons_append, List.nil_append, List.append_nil] using
      (List.perm_middle
        (l₁ := first :: rest) (a := spectator) (l₂ := []))
  simpa only [complexRatPolyProduct] using
    (finiteProductHaarComplex_product_perm blockCount hperm)

/-- The paired association used by the four-valent dispatcher is likewise
the same complete factor word under every external spectator. -/
private theorem finiteProductHaarComplex_mul_pairedFour_eq_mul_product
    (blockCount : Nat)
    (spectator first second third fourth : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMul first second)
            (complexRatPolyMul third fourth))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct [first, second, third, fourth]))) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_comm blockCount spectator
      (complexRatPolyMul
        (complexRatPolyMul first second)
        (complexRatPolyMul third fourth))) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount
      (complexRatPolyMul first second) third fourth spectator) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount
      (complexRatPolyMul (complexRatPolyMul first second) third)
      fourth spectator) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_comm blockCount
      (complexRatPolyMul
        (complexRatPolyMul
          (complexRatPolyMul first second) third) fourth)
      spectator) ?_
  simpa only [List.foldl, complexRatPolyProduct] using
    (finiteProductHaarComplex_mul_foldl_eq_mul_product_cons
      blockCount spectator first [second, third, fourth])

/-! ## 3. The bounded single-block dispatcher -/

/-- Recover the literal list from a dispatcher word.  This nondependent view
keeps the seven association proofs separate from the proof-valued length
argument used by `toCutoffOneHaarWord`. -/
private def cutoffOneHaarWordOccurrences :
    CutoffOneHaarWord → List FundamentalOccurrence
  | .v0 => []
  | .v1 first => [first]
  | .v2 first second => [first, second]
  | .v3 first second third => [first, second, third]
  | .v4 first second third fourth => [first, second, third, fourth]
  | .v5 first second third fourth fifth =>
      [first, second, third, fourth, fifth]
  | .v6 first second third fourth fifth sixth =>
      [first, second, third, fourth, fifth, sixth]

/-- The proof-carrying conversion retains every occurrence, in order. -/
private theorem cutoffOneHaarWordOccurrences_toCutoffOneHaarWord :
    ∀ (occurrences : List FundamentalOccurrence)
      (hlength : occurrences.length ≤ 6),
      cutoffOneHaarWordOccurrences
          (toCutoffOneHaarWord occurrences hlength) =
        occurrences
  | [], _ => rfl
  | _first :: [], _ => rfl
  | _first :: _second :: [], _ => rfl
  | _first :: _second :: _third :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: _sixth :: [], _ => rfl
  | _first :: _second :: _third :: _fourth :: _fifth :: _sixth ::
      _seventh :: _rest, hlength => by
      simp only [List.length_cons] at hlength
      omega

/-- The seven dispatcher associations, proved by ordinary constructor cases.
No proof-valued length argument occurs in this theorem's motive. -/
private theorem finiteProductHaarComplex_mul_cutoffOneTerm_eq_haarWordFactorProduct
    (blockCount block : Nat) (spectator : ComplexRatPoly)
    (word : CutoffOneHaarWord) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (cutoffOneFundamentalTerm block word)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct
            ((cutoffOneHaarWordOccurrences word).map
              (fundamentalOccurrenceCoefficient block))))) := by
  cases word with
  | v0 =>
      exact rationalComplexEqv_refl _
  | v1 first =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (orientedFundamentalWord block first [])))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              ((first :: []).map
                (fundamentalOccurrenceCoefficient block)))))
      exact finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
        blockCount block spectator first []
  | v2 first second =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (orientedFundamentalWord block first [second])))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              ((first :: second :: []).map
                (fundamentalOccurrenceCoefficient block)))))
      exact finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
        blockCount block spectator first [second]
  | v3 first second third =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (orientedFundamentalWord block first [second, third])))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              ((first :: second :: third :: []).map
                (fundamentalOccurrenceCoefficient block)))))
      exact finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
        blockCount block spectator first [second, third]
  | v4 first second third fourth =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul
              (complexRatPolyMul
                (fundamentalOccurrenceCoefficient block first)
                (fundamentalOccurrenceCoefficient block second))
              (complexRatPolyMul
                (fundamentalOccurrenceCoefficient block third)
                (fundamentalOccurrenceCoefficient block fourth)))))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              [fundamentalOccurrenceCoefficient block first,
               fundamentalOccurrenceCoefficient block second,
               fundamentalOccurrenceCoefficient block third,
               fundamentalOccurrenceCoefficient block fourth])))
      exact finiteProductHaarComplex_mul_pairedFour_eq_mul_product
        blockCount spectator
        (fundamentalOccurrenceCoefficient block first)
        (fundamentalOccurrenceCoefficient block second)
        (fundamentalOccurrenceCoefficient block third)
        (fundamentalOccurrenceCoefficient block fourth)
  | v5 first second third fourth fifth =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (orientedFundamentalWord block first
              [second, third, fourth, fifth])))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              ((first :: second :: third :: fourth :: fifth :: []).map
                (fundamentalOccurrenceCoefficient block)))))
      exact finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
        blockCount block spectator first [second, third, fourth, fifth]
  | v6 first second third fourth fifth sixth =>
      change RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            ([fundamentalOccurrenceCoefficient block second,
              fundamentalOccurrenceCoefficient block third,
              fundamentalOccurrenceCoefficient block fourth,
              fundamentalOccurrenceCoefficient block fifth,
              fundamentalOccurrenceCoefficient block sixth].foldl
                complexRatPolyMul
                (fundamentalOccurrenceCoefficient block first))))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              (fundamentalOccurrenceCoefficient block first ::
                [fundamentalOccurrenceCoefficient block second,
                 fundamentalOccurrenceCoefficient block third,
                 fundamentalOccurrenceCoefficient block fourth,
                 fundamentalOccurrenceCoefficient block fifth,
                 fundamentalOccurrenceCoefficient block sixth]))))
      exact finiteProductHaarComplex_mul_foldl_eq_mul_product_cons
        blockCount spectator
        (fundamentalOccurrenceCoefficient block first)
        [fundamentalOccurrenceCoefficient block second,
         fundamentalOccurrenceCoefficient block third,
         fundamentalOccurrenceCoefficient block fourth,
         fundamentalOccurrenceCoefficient block fifth,
         fundamentalOccurrenceCoefficient block sixth]

/-- Reassociate the retained factor list into the exact branch selected by
the total dispatcher, only beneath finite-product Haar. -/
theorem finiteProductHaarComplex_mul_factorWord_eq_cutoffOneFundamentalTerm
    (blockCount block : Nat) (spectator : ComplexRatPoly)
    (word : AtMostSixFundamentalWord) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct (word.factorWord block))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (cutoffOneFundamentalTerm block word.toHaarWord))) := by
  have hfactor :
      word.factorWord block =
        (cutoffOneHaarWordOccurrences word.toHaarWord).map
          (fundamentalOccurrenceCoefficient block) := by
    change
      word.occurrences.map (fundamentalOccurrenceCoefficient block) =
        (cutoffOneHaarWordOccurrences
          (toCutoffOneHaarWord
            word.occurrences word.length_le_six)).map
          (fundamentalOccurrenceCoefficient block)
    rw [cutoffOneHaarWordOccurrences_toCutoffOneHaarWord]
  rw [hfactor]
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_cutoffOneTerm_eq_haarWordFactorProduct
      blockCount block spectator word.toHaarWord)

/-- **Bounded exact local dispatcher under an arbitrary independent
spectator.**  The source is the literal ordered factor list supplied by
geometry; the target is the already verified total local Haar kernel. -/
theorem finiteProductHaarComplex_mul_atMostSixFactorWord_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (word : AtMostSixFundamentalWord) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct (word.factorWord block))))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (cutoffOneHaarKernel word.toHaarWord)) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_factorWord_eq_cutoffOneFundamentalTerm
      blockCount block spectator word)
    (genericBlock_cutoffOneFundamentalTerm_projector_with_complex_spectator
      blockCount block hblock spectator hindependent word.toHaarWord)

/-! ## 4. Pairwise-distinct multiblock iteration -/

/-- One bounded local word together with its selected in-range block. -/
structure AtMostSixBlockWord (blockCount : Nat) where
  block : Nat
  block_lt : block < blockCount
  word : AtMostSixFundamentalWord

/-- Concatenate the literal coefficient factors block by block, without
forming a product of local choice sets. -/
def atMostSixBlockFactorWords {blockCount : Nat} :
    List (AtMostSixBlockWord blockCount) → List ComplexRatPoly
  | [] => []
  | entry :: entries =>
      entry.word.factorWord entry.block ++
        atMostSixBlockFactorWords entries

/-- Tail-first product of the corresponding exact local Haar kernels. -/
def atMostSixBlockKernelProduct {blockCount : Nat} :
    List (AtMostSixBlockWord blockCount) → RationalComplex
  | [] => rationalComplexOne
  | entry :: entries =>
      YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
        (cutoffOneHaarKernel entry.word.toHaarWord)
        (atMostSixBlockKernelProduct entries)

private theorem complexQuaternionBlockIndependent_fundamentalOccurrenceCoefficient_of_ne
    {source target : Nat} (hne : source ≠ target)
    (occurrence : FundamentalOccurrence) :
    ComplexQuaternionBlockIndependent target
      (fundamentalOccurrenceCoefficient source occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · exact complexQuaternionBlockIndependent_forwardFundamentalCoefficient
      hne row column
  · exact complexQuaternionBlockIndependent_reverseFundamentalCoefficient
      hne row column

private theorem complexQuaternionBlockIndependent_foldl
    (target : Nat) :
    ∀ (factors : List ComplexRatPoly) (accumulator : ComplexRatPoly),
      ComplexQuaternionBlockIndependent target accumulator →
      (∀ factor, factor ∈ factors →
        ComplexQuaternionBlockIndependent target factor) →
      ComplexQuaternionBlockIndependent target
        (factors.foldl complexRatPolyMul accumulator)
  | [], accumulator, haccumulator, _ => haccumulator
  | factor :: factors, accumulator, haccumulator, hall =>
      complexQuaternionBlockIndependent_foldl target factors
        (complexRatPolyMul accumulator factor)
        (complexQuaternionBlockIndependent_mul haccumulator
          (hall factor List.mem_cons_self))
        (fun item hitem =>
          hall item (List.mem_cons_of_mem factor hitem))

private theorem atMostSixBlockFactorWords_factor_independent
    {blockCount target : Nat} :
    ∀ (entries : List (AtMostSixBlockWord blockCount)),
      (∀ entry, entry ∈ entries → entry.block ≠ target) →
      ∀ factor, factor ∈ atMostSixBlockFactorWords entries →
        ComplexQuaternionBlockIndependent target factor
  | [], _, factor, hfactor => by
      simp only [atMostSixBlockFactorWords, List.not_mem_nil] at hfactor
  | entry :: entries, havoid, factor, hfactor => by
      simp only [atMostSixBlockFactorWords, List.mem_append] at hfactor
      rcases hfactor with hhead | htail
      · unfold AtMostSixFundamentalWord.factorWord at hhead
        obtain ⟨occurrence, _hoccurrence, rfl⟩ := List.mem_map.mp hhead
        exact
          complexQuaternionBlockIndependent_fundamentalOccurrenceCoefficient_of_ne
            (havoid entry List.mem_cons_self) occurrence
      · exact atMostSixBlockFactorWords_factor_independent entries
          (fun candidate hcandidate =>
            havoid candidate (List.mem_cons_of_mem entry hcandidate))
          factor htail

private theorem atMostSixBlockFactorWords_foldl_independent
    {blockCount target : Nat}
    (entries : List (AtMostSixBlockWord blockCount))
    (havoid : ∀ entry, entry ∈ entries → entry.block ≠ target) :
    ComplexQuaternionBlockIndependent target
      ((atMostSixBlockFactorWords entries).foldl
        complexRatPolyMul complexRatPolyOne) :=
  complexQuaternionBlockIndependent_foldl target
    (atMostSixBlockFactorWords entries) complexRatPolyOne
    (complexRatPolyOne_blockIndependent target)
    (atMostSixBlockFactorWords_factor_independent entries havoid)

/-- **Exact structural multiblock dispatcher.**  Pairwise-distinct selected
blocks can be integrated one at a time.  The tail's accumulated coefficient
word is proved independent of the head block and serves as its spectator;
the resulting scalar kernels are retained as a tail-first product. -/
theorem finiteProductHaarComplex_atMostSixDistinctBlockWords
    (blockCount : Nat) :
    ∀ (entries : List (AtMostSixBlockWord blockCount)),
      (entries.map AtMostSixBlockWord.block).Nodup →
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyProduct
            (atMostSixBlockFactorWords entries)))
        (atMostSixBlockKernelProduct entries)
  | [], _ => by
      simpa only [atMostSixBlockFactorWords,
        atMostSixBlockKernelProduct, complexRatPolyProduct] using
        (finiteProductHaarComplex_one blockCount)
  | entry :: entries, hblocks => by
      have hparts :
          entry.block ∉ entries.map AtMostSixBlockWord.block ∧
            (entries.map AtMostSixBlockWord.block).Nodup := by
        exact List.nodup_cons.mp hblocks
      have htailAvoid :
          ∀ candidate, candidate ∈ entries →
            candidate.block ≠ entry.block := by
        intro candidate hcandidate heq
        exact hparts.1
          (List.mem_map.mpr ⟨candidate, hcandidate, heq⟩)
      have hindependent :
          ComplexQuaternionBlockIndependent entry.block
            ((atMostSixBlockFactorWords entries).foldl
              complexRatPolyMul complexRatPolyOne) :=
        atMostSixBlockFactorWords_foldl_independent entries htailAvoid
      have hperm :
          (entry.word.factorWord entry.block ++
              atMostSixBlockFactorWords entries).Perm
            (atMostSixBlockFactorWords entries ++
              entry.word.factorWord entry.block) :=
        List.perm_append_comm
      refine rationalComplexEqv_trans
        (by
          simpa only [atMostSixBlockFactorWords] using
            (finiteProductHaarComplex_product_perm blockCount hperm)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexEqv_symm
          (rationalComplexEqv_trans
            (finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
              blockCount complexRatPolyOne
              (atMostSixBlockFactorWords entries)
              (entry.word.factorWord entry.block))
            (finiteProductHaarComplex_one_mul blockCount
              (complexRatPolyProduct
                (atMostSixBlockFactorWords entries ++
                  entry.word.factorWord entry.block))))) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_atMostSixFactorWord_projector_with_complex_spectator
          blockCount entry.block entry.block_lt
          ((atMostSixBlockFactorWords entries).foldl
            complexRatPolyMul complexRatPolyOne)
          hindependent entry.word) ?_
      have htail :
          RationalComplexEqv
            (finiteProductHaarComplex blockCount
              ((atMostSixBlockFactorWords entries).foldl
                complexRatPolyMul complexRatPolyOne))
            (atMostSixBlockKernelProduct entries) :=
        rationalComplexEqv_trans
          (finiteProductHaarComplex_foldl_one_eq_product blockCount
            (atMostSixBlockFactorWords entries))
          (finiteProductHaarComplex_atMostSixDistinctBlockWords
            blockCount entries hparts.2)
      refine rationalComplexEqv_trans
        (generic_rationalComplexMul_eqv
          (finiteProductHaarComplex blockCount
            ((atMostSixBlockFactorWords entries).foldl
              complexRatPolyMul complexRatPolyOne))
          (cutoffOneHaarKernel entry.word.toHaarWord)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexMul_congr htail
          (rationalComplexEqv_refl
            (cutoffOneHaarKernel entry.word.toHaarWord))) ?_
      simpa only [atMostSixBlockKernelProduct] using
        (rationalComplexMul_comm
          (atMostSixBlockKernelProduct entries)
          (cutoffOneHaarKernel entry.word.toHaarWord))

/-! ## Axiom audit -/

#print axioms finiteProductHaarComplex_mul_orientedWord_eq_mul_factorProduct
#print axioms finiteProductHaarComplex_mul_foldl_eq_mul_product_cons
#print axioms finiteProductHaarComplex_mul_pairedFour_eq_mul_product
#print axioms cutoffOneHaarWordOccurrences_toCutoffOneHaarWord
#print axioms finiteProductHaarComplex_mul_cutoffOneTerm_eq_haarWordFactorProduct
#print axioms AtMostSixFundamentalWord.valence_toHaarWord
#print axioms finiteProductHaarComplex_mul_factorWord_eq_cutoffOneFundamentalTerm
#print axioms finiteProductHaarComplex_mul_atMostSixFactorWord_projector_with_complex_spectator
#print axioms finiteProductHaarComplex_atMostSixDistinctBlockWords

end YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini
