/-
# Exact five-block marginal of the resummed BF4 vacuum moments

The literal corrected BF4 slab uses 116 quaternion link blocks.  The five
tree-gauge chords transmitted through the reflection cut are represented in
that raw link enumeration by blocks `11, 3, 6, 23, 42`.  This module moves
those five blocks, in physical transmitted order, to the end of the product
carrier and integrates the other 111 blocks by exact normalized `S^3` Haar.

The result is an exact five-block polynomial marginal for each of the two
resummed centered-vacuum moments.  Its variables are still the five selected
raw chord-link representatives.  Identifying them with the five cycle
holonomies of the existing tree-gauge polynomial requires a nonlinear
vertex-gauge change of variables; no such identification is claimed here.

## Axiom gate

Finite lists, explicit block permutations, exact rational moments, and
constructive recursion only.  No `Classical.*`, `native_decide`, `sorry`,
custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
import YMGap.Continuum.SU2QuaternionHaarHeadFubini

namespace YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The five geometric raw-link representatives -/

/-- Raw 116-link block numbers of the five transmitted tree-gauge chords,
in the canonical order `{0,4,5,6,10}`. -/
def exactTransmittedRawBlocks : List Nat :=
  bf4TransmittedCycleTable.map fun cycle =>
    (boundaryCompleteSlabLinks 1).idxOf (bf4SpatialChord cycle)

theorem exactTransmittedRawBlocks_eq :
    exactTransmittedRawBlocks = [11, 3, 6, 23, 42] := by
  decide

theorem exactTransmittedRawBlocks_length :
    exactTransmittedRawBlocks.length = 5 := by
  rw [exactTransmittedRawBlocks_eq]
  rfl

theorem exactTransmittedRawBlocks_nodup :
    exactTransmittedRawBlocks.Nodup := by
  rw [exactTransmittedRawBlocks_eq]
  decide

theorem exactTransmittedRawBlocks_lt_116 :
    ∀ block, block ∈ exactTransmittedRawBlocks → block < 116 := by
  rw [exactTransmittedRawBlocks_eq]
  intro block hblock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
  omega

/-! ## 2. Move the transmitted blocks to the five-block tail -/

/-- Five disjoint transpositions.  New tail blocks `111,...,115` read the
old transmitted blocks `11,3,6,23,42`; the inverse action is the same map. -/
def transmittedTailBlockMap (block : Nat) : Nat :=
  if block = 11 then 111
  else if block = 111 then 11
  else if block = 3 then 112
  else if block = 112 then 3
  else if block = 6 then 113
  else if block = 113 then 6
  else if block = 23 then 114
  else if block = 114 then 23
  else if block = 42 then 115
  else if block = 115 then 42
  else block

/-- The transmitted-to-tail map as constructive involution data on the
literal 116-block carrier. -/
def transmittedTailBlockInvolution :
    QuaternionBlockInvolution 116 where
  map := transmittedTailBlockMap
  map_lt := by
    intro block hblock
    by_cases h11 : block = 11
    · subst block
      decide
    · by_cases h111 : block = 111
      · subst block
        decide
      · by_cases h3 : block = 3
        · subst block
          decide
        · by_cases h112 : block = 112
          · subst block
            decide
          · by_cases h6 : block = 6
            · subst block
              decide
            · by_cases h113 : block = 113
              · subst block
                decide
              · by_cases h23 : block = 23
                · subst block
                  decide
                · by_cases h114 : block = 114
                  · subst block
                    decide
                  · by_cases h42 : block = 42
                    · subst block
                      decide
                    · by_cases h115 : block = 115
                      · subst block
                        decide
                      · simpa [transmittedTailBlockMap, h11, h111, h3,
                          h112, h6, h113, h23, h114, h42, h115]
                        using hblock
  involutive := by
    intro block _
    by_cases h11 : block = 11
    · subst block
      decide
    · by_cases h111 : block = 111
      · subst block
        decide
      · by_cases h3 : block = 3
        · subst block
          decide
        · by_cases h112 : block = 112
          · subst block
            decide
          · by_cases h6 : block = 6
            · subst block
              decide
            · by_cases h113 : block = 113
              · subst block
                decide
              · by_cases h23 : block = 23
                · subst block
                  decide
                · by_cases h114 : block = 114
                  · subst block
                    decide
                  · by_cases h42 : block = 42
                    · subst block
                      decide
                    · by_cases h115 : block = 115
                      · subst block
                        decide
                      · simp [transmittedTailBlockMap, h11, h111, h3,
                          h112, h6, h113, h23, h114, h42, h115]

/-- The new five-block tail reads precisely the old geometric transmitted
representatives, in the canonical transmitted order. -/
theorem transmittedTailBlockInvolution_tail_order :
    [111, 112, 113, 114, 115].map
        transmittedTailBlockInvolution.map =
      exactTransmittedRawBlocks := by
  rw [exactTransmittedRawBlocks_eq]
  decide

/-! ## 3. Exact integration of an arbitrary number of head blocks -/

/-- Iterate the polynomial-valued normalized Haar integral over the head
quaternion block. -/
def partialHaarHeads : Nat → RatPoly → RatPoly
  | 0, polynomial => polynomial
  | blocks + 1, polynomial =>
      partialHaarHeads blocks (partialHaarHead polynomial)

/-- Iterated constructive Fubini: integrating `integratedBlocks` head blocks
and then the `tailBlocks` survivors is the original product Haar. -/
theorem quaternionHaar_partialHaarHeads
    (tailBlocks : Nat) : ∀ (integratedBlocks : Nat) (polynomial : RatPoly),
    quaternionHaar tailBlocks
        (partialHaarHeads integratedBlocks polynomial) ≈
      quaternionHaar (tailBlocks + integratedBlocks) polynomial
  | 0, polynomial => Q'.eqv_refl _
  | integratedBlocks + 1, polynomial => by
      refine Q'.eqv_trans _
        (quaternionHaar (tailBlocks + integratedBlocks)
          (partialHaarHead polynomial)) _
        (quaternionHaar_partialHaarHeads
          tailBlocks integratedBlocks
          (partialHaarHead polynomial)) ?_
      simpa [Nat.add_assoc] using
        quaternionHaar_partialHaarHead
          (tailBlocks + integratedBlocks) polynomial

/-- One head integration removes one quaternion block from syntactic
support. -/
theorem partialHaarHead_supported
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks (blocks + 1) polynomial) :
    SupportedQuaternionBlocks blocks (partialHaarHead polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  have hlength := hsupport source hsource
  simp only [partialHaarHeadTerm, List.length_drop]
  omega

/-- Iterated head integration removes the declared number of quaternion
blocks from syntactic support. -/
theorem partialHaarHeads_supported
    (tailBlocks : Nat) : ∀ (integratedBlocks : Nat)
      (polynomial : RatPoly),
    SupportedQuaternionBlocks
        (tailBlocks + integratedBlocks) polynomial →
      SupportedQuaternionBlocks tailBlocks
        (partialHaarHeads integratedBlocks polynomial)
  | 0, polynomial, hsupport => hsupport
  | integratedBlocks + 1, polynomial, hsupport => by
      apply partialHaarHeads_supported tailBlocks integratedBlocks
        (partialHaarHead polynomial)
      apply partialHaarHead_supported
      simpa [Nat.add_assoc] using hsupport

/-- Reindexing constructs an exponent vector with exactly the declared
block length, so its output is syntactically supported independently of
trailing coordinates in the input ledger. -/
theorem reindexQuaternionPolynomial_supported
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (reindexQuaternionPolynomial permutation polynomial) := by
  intro term hterm
  obtain ⟨source, _, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  simp only
  exact Nat.le_of_eq
    (reindexQuaternionExponents_length permutation source.1)

/-! ## 4. The universal 116-to-five transmitted marginal -/

/-- Reindex the transmitted raw-link blocks to the tail and integrate the
other 111 normalized quaternion blocks. -/
def exactTransmittedFiveMarginal (polynomial : RatPoly) : RatPoly :=
  partialHaarHeads 111
    (reindexQuaternionPolynomial
      transmittedTailBlockInvolution polynomial)

/-- The constructed marginal is genuinely a polynomial on at most five
quaternion blocks (twenty real coordinates). -/
theorem exactTransmittedFiveMarginal_supported_five
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks 5
      (exactTransmittedFiveMarginal polynomial) := by
  unfold exactTransmittedFiveMarginal
  apply partialHaarHeads_supported 5 111
  simpa using
    reindexQuaternionPolynomial_supported
      transmittedTailBlockInvolution polynomial

/-- **Exact 116-to-five Fubini theorem.**  On every polynomial supported by
the literal slab carrier, the 116-fold product Haar equals the fivefold Haar
of its transmitted raw-link marginal. -/
theorem quaternionHaar_116_eq_transmittedFiveMarginal
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 116 polynomial) :
    quaternionHaar 116 polynomial ≈
      quaternionHaar 5 (exactTransmittedFiveMarginal polynomial) := by
  refine Q'.eqv_trans _
    (quaternionHaar 116
      (reindexQuaternionPolynomial
        transmittedTailBlockInvolution polynomial)) _ ?_ ?_
  · exact Q'.eqv_symm
      (quaternionHaar_reindex
        transmittedTailBlockInvolution polynomial hsupport)
  · exact Q'.eqv_symm
      (by
        simpa [exactTransmittedFiveMarginal] using
          quaternionHaar_partialHaarHeads 5 111
            (reindexQuaternionPolynomial
              transmittedTailBlockInvolution polynomial))

/-! ## 5. Support of the two resummed slab polynomials -/

private theorem supported_polySmul_local
    {blocks : Nat} {scale : Q'} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private theorem supported_finitePolySum
    {Index : Type} {blocks : Nat} (polynomial : Index → RatPoly)
    (hsupport : ∀ item, SupportedQuaternionBlocks blocks (polynomial item)) :
    ∀ items, SupportedQuaternionBlocks blocks
      (finitePolySum polynomial items)
  | [] => by
      intro term hterm
      simp [finitePolySum, polyZero] at hterm
  | head :: tail => by
      intro term hterm
      rcases List.mem_append.mp hterm with hhead | htail
      · exact hsupport head term hhead
      · exact supported_finitePolySum polynomial hsupport tail term htail

theorem exactCorrectedSlabWeightedIntegrand_supported_116
    (w : Q') (K : Nat)
    (faceLabel :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    SupportedQuaternionBlocks 116
      (exactCorrectedSlabWeightedIntegrand w K faceLabel) := by
  unfold exactCorrectedSlabWeightedIntegrand
  apply supported_polySmul_local
  rw [← correctedSlabLinks_extent_one_length]
  exact exactCorrectedSlabSpinNetworkIntegrand_supported 1 faceLabel

theorem exactVacuumRowResummedPolynomial_supported_116
    (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 116
      (exactVacuumRowResummedPolynomial w K) := by
  unfold exactVacuumRowResummedPolynomial
  apply supported_finitePolySum
  intro right
  apply supported_finitePolySum
  intro boundary
  exact exactCorrectedSlabWeightedIntegrand_supported_116 w K _

theorem exactConstantMomentResummedPolynomial_supported_116
    (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 116
      (exactConstantMomentResummedPolynomial w K) := by
  unfold exactConstantMomentResummedPolynomial
  apply supported_finitePolySum
  intro left
  apply supported_finitePolySum
  intro right
  apply supported_finitePolySum
  intro boundary
  exact exactCorrectedSlabWeightedIntegrand_supported_116 w K _

/-! ## 6. Fivefold Haar forms of the unresolved centered moments -/

def exactVacuumRowTransmittedFivePolynomial
    (w : Q') (K : Nat) : RatPoly :=
  exactTransmittedFiveMarginal
    (exactVacuumRowResummedPolynomial w K)

def exactConstantMomentTransmittedFivePolynomial
    (w : Q') (K : Nat) : RatPoly :=
  exactTransmittedFiveMarginal
    (exactConstantMomentResummedPolynomial w K)

/-- The exact signed vacuum row is a fivefold Haar value after all other
raw slab-link blocks are integrated. -/
theorem exactVacuumRightConstantCrossMoment_eq_transmittedFiveHaar
    (w : Q') (K : Nat) :
    exactVacuumRightConstantCrossMoment w K ≈
      quaternionHaar 5
        (exactVacuumRowTransmittedFivePolynomial w K) := by
  exact Q'.eqv_trans _
    (quaternionHaar 116
      (exactVacuumRowResummedPolynomial w K)) _
    (exactVacuumRightConstantCrossMoment_eq_resummedHaar w K)
    (quaternionHaar_116_eq_transmittedFiveMarginal _
      (exactVacuumRowResummedPolynomial_supported_116 w K))

/-- The exact constant quadratic moment has the same fivefold transmitted
raw-link Haar reduction. -/
theorem exactConstantQuadraticMoment_eq_transmittedFiveHaar
    (w : Q') (K : Nat) :
    exactConstantQuadraticMoment w K ≈
      quaternionHaar 5
        (exactConstantMomentTransmittedFivePolynomial w K) := by
  exact Q'.eqv_trans _
    (quaternionHaar 116
      (exactConstantMomentResummedPolynomial w K)) _
    (exactConstantQuadraticMoment_eq_resummedHaar w K)
    (quaternionHaar_116_eq_transmittedFiveMarginal _
      (exactConstantMomentResummedPolynomial_supported_116 w K))

/-! ## 7. The full centered expression on the five-block marginal -/

/-- The signed-Haar side of the centered vacuum probe after both finite
label resummation and integration of the 111 non-transmitted raw blocks. -/
def exactTransmittedFiveCenteredVacuumMomentExpression
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        quaternionHaar 5
          (exactVacuumRowTransmittedFivePolynomial w K) +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        quaternionHaar 5
          (exactVacuumRowTransmittedFivePolynomial w K) +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
      (-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling)) *
        quaternionHaar 5
          (exactConstantMomentTransmittedFivePolynomial w K)))

theorem exactResummedCenteredVacuumMomentExpression_eq_transmittedFive
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactResummedCenteredVacuumMomentExpression w hw K ≈
      exactTransmittedFiveCenteredVacuumMomentExpression w hw K := by
  unfold exactResummedCenteredVacuumMomentExpression
    exactTransmittedFiveCenteredVacuumMomentExpression
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl 1)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left
        (-centralPhysicalRowMarginal
          w hw K 0 zeroEdgeLabelling) _ _
        (quaternionHaar_116_eq_transmittedFiveMarginal _
          (exactVacuumRowResummedPolynomial_supported_116 w K)))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left
          (-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) _ _
          (quaternionHaar_116_eq_transmittedFiveMarginal _
            (exactVacuumRowResummedPolynomial_supported_116 w K)))
        (Q'.mul_eqv_congr_left
          ((-centralPhysicalRowMarginal
              w hw K 0 zeroEdgeLabelling) *
            (-centralPhysicalRowMarginal
              w hw K 0 zeroEdgeLabelling)) _ _
          (quaternionHaar_116_eq_transmittedFiveMarginal _
            (exactConstantMomentResummedPolynomial_supported_116 w K)))))

/-- The exact centered vacuum quadratic is therefore an explicit fivefold
normalized Haar expression on the transmitted raw-link marginal. -/
theorem exactSlabAllCutoffQuadratic_centeredVacuum_eq_transmittedFiveHaar
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K) ≈
      exactTransmittedFiveCenteredVacuumMomentExpression w hw K := by
  exact Q'.eqv_trans _
    (exactResummedCenteredVacuumMomentExpression w hw K) _
    (exactSlabAllCutoffQuadratic_centeredVacuum_eq_resummedHaar
      w hw K)
    (exactResummedCenteredVacuumMomentExpression_eq_transmittedFive
      w hw K)

end YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal.quaternionHaar_partialHaarHeads
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal.quaternionHaar_116_eq_transmittedFiveMarginal
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal.exactVacuumRightConstantCrossMoment_eq_transmittedFiveHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal.exactConstantQuadraticMoment_eq_transmittedFiveHaar
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal.exactSlabAllCutoffQuadratic_centeredVacuum_eq_transmittedFiveHaar
