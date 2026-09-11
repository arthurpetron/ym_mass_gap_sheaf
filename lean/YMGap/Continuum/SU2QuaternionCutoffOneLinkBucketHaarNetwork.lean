/-
# The cutoff-one link-bucket Haar network

This leaf completes the geometry-to-dispatcher step at one named Boolean
environment.  Every touched physical link receives its literal, stably
ordered bucket of oriented fundamental occurrences, together with the N0
geometric proof that the bucket has valence at most six.  The common block is
the constructive `listIndexOf` of that physical link in the duplicate-free
touched-link carrier.

The concatenation of those local factor words is proved equal, not merely
permutation equivalent, to the N1 link-major coefficient word.  Pairwise
distinctness of the selected Haar blocks then follows from duplicate-freeness
of the physical-link carrier, so the structural at-most-six Fubini theorem
evaluates the whole named face network as the product of its honest local
`cutoffOneHaarKernel` values.

No global channel assignment or Boolean Cartesian product is formed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
import YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini

namespace YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketHaarNetwork

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct
open YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
open YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini

/-! ## 1. Literal bounded words at physical links -/

/-- The ordered occurrence word at one physical link.  This is exactly the
N0 stable bucket, with no sorting, truncation, or padding. -/
def cutoffOneLinkBucketFundamentalOccurrences
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (link : Z4Link) : List FundamentalOccurrence :=
  (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
    (cutoffOneDescriptorOccurrence environment)

/-- The literal occurrence bucket packaged for the total local Haar
dispatcher.  The sole bound is the geometric four-dimensional valence bound
proved at N0. -/
def cutoffOneLinkBucketFundamentalWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : Z4Link) : AtMostSixFundamentalWord :=
  { occurrences :=
      cutoffOneLinkBucketFundamentalOccurrences
        orientationAt n support environment link
    length_le_six := by
      unfold cutoffOneLinkBucketFundamentalOccurrences
      rw [List.length_map]
      exact cutoffOneLinkOccurrenceBucket_length_le_six hsupport link }

@[simp] theorem cutoffOneLinkBucketFundamentalWord_occurrences
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : Z4Link) :
    (cutoffOneLinkBucketFundamentalWord
      orientationAt n support environment hsupport link).occurrences =
      cutoffOneLinkBucketFundamentalOccurrences
        orientationAt n support environment link := by
  rfl

/-- The coefficient word contributed by one physical-link bucket, expressed
in the common touched-link block list. -/
def cutoffOneLinkBucketCoefficientWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (link : Z4Link) : List ComplexRatPoly :=
  (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
    (cutoffOneDescriptorCoefficient
      (cutoffOneTouchedLinks n support) environment)

/-- At its physical link's common `listIndexOf` block, the packaged local
word gives exactly the descriptor coefficient word of that bucket. -/
theorem cutoffOneLinkBucketFundamentalWord_factorWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : Z4Link) :
    (cutoffOneLinkBucketFundamentalWord
      orientationAt n support environment hsupport link).factorWord
        (listIndexOf link (cutoffOneTouchedLinks n support)) =
      cutoffOneLinkBucketCoefficientWord
        orientationAt n support environment link := by
  unfold cutoffOneLinkBucketFundamentalWord
    cutoffOneLinkBucketFundamentalOccurrences
    cutoffOneLinkBucketCoefficientWord
    AtMostSixFundamentalWord.factorWord
  rw [List.map_map]
  apply List.map_congr_left
  intro descriptor hdescriptor
  simp only [Function.comp_apply]
  unfold cutoffOneDescriptorCoefficient
    CutoffOneLinkOccurrenceDescriptor.block
  rw [(mem_cutoffOneLinkOccurrenceBucket.mp hdescriptor).2]

/-! ## 2. One in-range, pairwise-distinct block per touched link -/

/-- A proof-carrying touched link becomes one bounded dispatcher entry.  Its
block is definitionally the first index of its physical link in the common
touched-link list. -/
def cutoffOneTouchedLinkBlockWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : { link : Z4Link // link ∈ cutoffOneTouchedLinks n support }) :
    AtMostSixBlockWord (cutoffOneTouchedLinks n support).length :=
  { block := listIndexOf link.val (cutoffOneTouchedLinks n support)
    block_lt := listIndexOf_lt_of_mem link.val
      (cutoffOneTouchedLinks n support) link.property
    word := cutoffOneLinkBucketFundamentalWord
      orientationAt n support environment hsupport link.val }

@[simp] theorem cutoffOneTouchedLinkBlockWord_block
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : { link : Z4Link // link ∈ cutoffOneTouchedLinks n support }) :
    (cutoffOneTouchedLinkBlockWord
      orientationAt n support environment hsupport link).block =
      listIndexOf link.val (cutoffOneTouchedLinks n support) := by
  rfl

theorem cutoffOneTouchedLinkBlockWord_block_lt
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : { link : Z4Link // link ∈ cutoffOneTouchedLinks n support }) :
    (cutoffOneTouchedLinkBlockWord
      orientationAt n support environment hsupport link).block <
      (cutoffOneTouchedLinks n support).length :=
  (cutoffOneTouchedLinkBlockWord
    orientationAt n support environment hsupport link).block_lt

theorem cutoffOneTouchedLinkBlockWord_factorWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : { link : Z4Link // link ∈ cutoffOneTouchedLinks n support }) :
    (cutoffOneTouchedLinkBlockWord
      orientationAt n support environment hsupport link).word.factorWord
        (cutoffOneTouchedLinkBlockWord
          orientationAt n support environment hsupport link).block =
      cutoffOneLinkBucketCoefficientWord
        orientationAt n support environment link.val := by
  exact cutoffOneLinkBucketFundamentalWord_factorWord
    orientationAt n support environment hsupport link.val

/-- The production dispatcher entries, in the exact canonical touched-link
order.  `List.attach` supplies only membership proofs; it adds no choices. -/
def cutoffOneTouchedLinkBlockWords
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    List (AtMostSixBlockWord (cutoffOneTouchedLinks n support).length) :=
  (cutoffOneTouchedLinks n support).attach.map
    (cutoffOneTouchedLinkBlockWord
      orientationAt n support environment hsupport)

/-- The selected block list is the literal map of `listIndexOf` over the
physical touched-link carrier. -/
theorem cutoffOneTouchedLinkBlockWords_blocks
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (cutoffOneTouchedLinkBlockWords
      orientationAt n support environment hsupport).map
        AtMostSixBlockWord.block =
      (cutoffOneTouchedLinks n support).map
        (fun link => listIndexOf link (cutoffOneTouchedLinks n support)) := by
  unfold cutoffOneTouchedLinkBlockWords
  rw [List.map_map]
  change
    (cutoffOneTouchedLinks n support).attach.map
        (fun link =>
          listIndexOf link.val (cutoffOneTouchedLinks n support)) = _
  calc
    _ = ((cutoffOneTouchedLinks n support).attach.map Subtype.val).map
          (fun link =>
            listIndexOf link (cutoffOneTouchedLinks n support)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro link _
        rfl
    _ = _ := by
        rw [List.attach_map_subtype_val]

private theorem listIndexOf_injective_of_mem
    {A : Type} [DecidableEq A] (xs : List A)
    {left right : A}
    (hleft : left ∈ xs) (hright : right ∈ xs)
    (hindex : listIndexOf left xs = listIndexOf right xs) :
    left = right := by
  have hleftGet :=
    getD_listIndexOf_of_mem left left xs hleft
  have hrightGet :=
    getD_listIndexOf_of_mem left right xs hright
  calc
    left = xs.getD (listIndexOf left xs) left := hleftGet.symm
    _ = xs.getD (listIndexOf right xs) left := by rw [hindex]
    _ = right := hrightGet

private theorem cutoffOneTouchedLinks_listIndexOf_nodup
    (n : Nat) (support : List Nat) :
    ((cutoffOneTouchedLinks n support).map
      (fun link => listIndexOf link
        (cutoffOneTouchedLinks n support))).Nodup := by
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    (fun link : Z4Link =>
      listIndexOf link (cutoffOneTouchedLinks n support))
    (cutoffOneTouchedLinks n support)
    (cutoffOneTouchedLinks_nodup n support)
  intro left hleft right hright hindex
  exact listIndexOf_injective_of_mem
    (cutoffOneTouchedLinks n support) hleft hright hindex

/-- Hence the dispatcher entries select pairwise-distinct Haar blocks. -/
theorem cutoffOneTouchedLinkBlockWords_blocks_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    ((cutoffOneTouchedLinkBlockWords
      orientationAt n support environment hsupport).map
        AtMostSixBlockWord.block).Nodup := by
  rw [cutoffOneTouchedLinkBlockWords_blocks]
  exact cutoffOneTouchedLinks_listIndexOf_nodup n support

/-! ## 3. Exact link-major concatenation -/

/-- Mapping the common coefficient semantics over the flattened link buckets
is exactly the flat map of the individual bucket coefficient words. -/
theorem cutoffOneLinkMajorCoefficientWord_eq_flatMap_bucketCoefficientWords
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    cutoffOneLinkMajorCoefficientWord
        orientationAt n support environment =
      (cutoffOneTouchedLinks n support).flatMap
        (cutoffOneLinkBucketCoefficientWord
          orientationAt n support environment) := by
  unfold cutoffOneLinkMajorCoefficientWord
    cutoffOneLinkMajorOccurrenceDescriptors
    cutoffOneLinkBucketCoefficientWord
  simp only [List.map_flatMap]

private theorem atMostSixBlockFactorWords_map_touchedLinkBlockWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    ∀ linked :
        List { link : Z4Link // link ∈ cutoffOneTouchedLinks n support },
      atMostSixBlockFactorWords
          (linked.map (cutoffOneTouchedLinkBlockWord
            orientationAt n support environment hsupport)) =
        (linked.map Subtype.val).flatMap
          (cutoffOneLinkBucketCoefficientWord
            orientationAt n support environment)
  | [] => rfl
  | link :: linked => by
      simp only [List.map_cons, atMostSixBlockFactorWords,
        List.flatMap_cons]
      rw [cutoffOneTouchedLinkBlockWord_factorWord
          orientationAt n support environment hsupport link,
        atMostSixBlockFactorWords_map_touchedLinkBlockWord
          orientationAt n support environment hsupport linked]

/-- **Exact geometry/dispatcher word identification.**  Concatenating the
bounded local factor words in touched-link order gives definitionally the
same coefficient sequence as the N1 stable link-major word. -/
theorem atMostSixBlockFactorWords_cutoffOneTouchedLinkBlockWords_eq_linkMajor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    atMostSixBlockFactorWords
        (cutoffOneTouchedLinkBlockWords
          orientationAt n support environment hsupport) =
      cutoffOneLinkMajorCoefficientWord
        orientationAt n support environment := by
  unfold cutoffOneTouchedLinkBlockWords
  rw [atMostSixBlockFactorWords_map_touchedLinkBlockWord
      orientationAt n support environment hsupport
      (cutoffOneTouchedLinks n support).attach]
  rw [List.attach_map_subtype_val]
  exact
    (cutoffOneLinkMajorCoefficientWord_eq_flatMap_bucketCoefficientWords
      orientationAt n support environment).symm

/-! ## 4. Per-environment Haar evaluation -/

/-- The link-major coefficient product is evaluated by the product of the
honest local cutoff-one Haar kernels, one for each touched physical link. -/
theorem finiteProductHaarComplex_cutoffOneLinkMajorCoefficientProduct_eq_linkBucketKernelProduct
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          (cutoffOneLinkMajorCoefficientWord
            orientationAt n support environment)))
      (atMostSixBlockKernelProduct
        (cutoffOneTouchedLinkBlockWords
          orientationAt n support environment hsupport)) := by
  rw [← atMostSixBlockFactorWords_cutoffOneTouchedLinkBlockWords_eq_linkMajor
    orientationAt n support environment hsupport]
  exact finiteProductHaarComplex_atMostSixDistinctBlockWords
    (cutoffOneTouchedLinks n support).length
    (cutoffOneTouchedLinkBlockWords
      orientationAt n support environment hsupport)
    (cutoffOneTouchedLinkBlockWords_blocks_nodup
      orientationAt n support environment hsupport)

/-- **N2 named-environment Haar network.**  For every valid cutoff-one
support and every named Boolean environment, the full literal oriented-face
product has Haar value equal to the product of the local dispatcher kernels
of its touched-link buckets. -/
theorem finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkBucketKernelProduct
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (cutoffOneOrientedFaceTraceProductAt
          orientationAt n support environment))
      (atMostSixBlockKernelProduct
        (cutoffOneTouchedLinkBlockWords
          orientationAt n support environment hsupport)) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkMajorCoefficientProduct
      orientationAt n support environment)
    (finiteProductHaarComplex_cutoffOneLinkMajorCoefficientProduct_eq_linkBucketKernelProduct
      orientationAt n support environment hsupport)

/-! ## Axiom audit -/

#print axioms cutoffOneLinkBucketFundamentalWord_factorWord
#print axioms cutoffOneTouchedLinkBlockWords_blocks_nodup
#print axioms atMostSixBlockFactorWords_cutoffOneTouchedLinkBlockWords_eq_linkMajor
#print axioms finiteProductHaarComplex_cutoffOneLinkMajorCoefficientProduct_eq_linkBucketKernelProduct
#print axioms finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkBucketKernelProduct

end YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketHaarNetwork
