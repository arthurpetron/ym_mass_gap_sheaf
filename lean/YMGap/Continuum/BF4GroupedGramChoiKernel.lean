/-
# Exact reflected holonomy gluing for the positive BF4 feature Gram

`BF4ReflectedAllSpinMehlerGramEndpoint` constructs a positive finite
Feynman--Kac endpoint as a weighted Gram of five-Haar half-amplitudes.  Until
now that Gram had not been identified with one literal reflected
ten-holonomy Haar integral.

This file closes that finite algebraic seam.

* Every supported five-holonomy polynomial is put in a canonical
  twenty-coordinate form without changing its normalized Haar value.
* The geometric all-spin wavefunction, one-sided shifted action, and one
  ordered kinetic feature word are assembled into an exact holonomy
  half-polynomial.
* Source and reflected target halves are glued on disjoint five-holonomy
  blocks.
* Exact product-Haar factorization proves that the grouped ten-holonomy
  integral is the existing positive feature Gram entry.
* For an arbitrary finite signed packet, the complete reflected quadratic
  is one grouped sum of literal integral squares and is nonnegative.

This is an exact finite-cutoff holonomy Gram/Choi identity for the positive
feature approximation.  It does not yet prove that the directed positive
feature truncations converge to the compact physical endpoint, nor identify
that compact endpoint with the corrected Wilson slab spin-foam Choi kernel.

## Axiom gate

Finite lists, exact `Q'` polynomial algebra, and normalized quaternion Haar
moments only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GeometricAllSpinHaarGram
import YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.BF4GroupedGramChoiKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4GeometricAllSpinHaarGram
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical block monomials preserve product Haar -/

/-- Canonical exponent vector of exactly `4 * blocks` entries.  Missing
coordinates are filled by the `exponentAt` default zero and coordinates
beyond the declared block prefix are discarded. -/
def canonicalQuaternionMonomial :
    Nat → List Nat → List Nat
  | 0, _ => []
  | blocks + 1, monomial =>
      exponentAt monomial 0 ::
      exponentAt monomial 1 ::
      exponentAt monomial 2 ::
      exponentAt monomial 3 ::
      canonicalQuaternionMonomial blocks
        (monomial.drop 4)

theorem canonicalQuaternionMonomial_length
    (blocks : Nat) (monomial : List Nat) :
    (canonicalQuaternionMonomial blocks monomial).length =
      4 * blocks := by
  induction blocks generalizing monomial with
  | zero => rfl
  | succ blocks induction =>
      simp only [canonicalQuaternionMonomial,
        List.length_cons]
      rw [induction]
      omega

theorem quaternionHaarPrefix_canonical
    (blocks : Nat) (monomial : List Nat) :
    quaternionHaarPrefix blocks
        (canonicalQuaternionMonomial blocks monomial) ≈
      quaternionHaarPrefix blocks monomial := by
  induction blocks generalizing monomial with
  | zero => exact Q'.eqv_refl 1
  | succ blocks induction =>
      simp only [canonicalQuaternionMonomial,
        quaternionHaarPrefix, exponentAt,
        List.getD_cons_zero, List.getD_cons_succ,
        List.drop_succ_cons, List.drop_zero]
      exact Q'.mul_eqv_congr_left
        (sphereMoment4
          (exponentAt monomial 0)
          (exponentAt monomial 1)
          (exponentAt monomial 2)
          (exponentAt monomial 3))
        _ _
        (induction (monomial.drop 4))

private theorem allZero_drop_of_length_le
    (values : List Nat) (coordinates : Nat)
    (hlength : values.length ≤ coordinates) :
    allZero (values.drop coordinates) = true := by
  rw [List.drop_eq_nil_of_le hlength]
  rfl

/-- Canonicalizing a supported monomial does not change its normalized
product-Haar moment. -/
theorem quaternionHaarMono_canonical
    (blocks : Nat) (monomial : List Nat)
    (hsupport : monomial.length ≤ 4 * blocks) :
    quaternionHaarMono blocks
        (canonicalQuaternionMonomial blocks monomial) ≈
      quaternionHaarMono blocks monomial := by
  have hcanonicalLength :=
    canonicalQuaternionMonomial_length blocks monomial
  have hcanonicalTail :
      allZero
        ((canonicalQuaternionMonomial blocks monomial).drop
          (4 * blocks)) = true :=
    allZero_drop_of_length_le _ _
      (by omega)
  have hsourceTail :
      allZero (monomial.drop (4 * blocks)) = true :=
    allZero_drop_of_length_le monomial
      (4 * blocks) hsupport
  unfold quaternionHaarMono
  rw [if_pos hcanonicalTail, if_pos hsourceTail]
  exact quaternionHaarPrefix_canonical blocks monomial

/-- Canonicalize every monomial in a rational polynomial to the displayed
quaternion block prefix. -/
def canonicalQuaternionPolynomial
    (blocks : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term =>
    (canonicalQuaternionMonomial blocks term.1,
      term.2)

theorem canonicalQuaternionPolynomial_supported
    (blocks : Nat) (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (canonicalQuaternionPolynomial blocks polynomial) := by
  intro term hterm
  simp only [canonicalQuaternionPolynomial,
    List.mem_map] at hterm
  rcases hterm with ⟨source, _, rfl⟩
  rw [canonicalQuaternionMonomial_length]
  exact Nat.le_refl _

/-- Canonicalization is invisible to normalized product Haar on every
supported polynomial. -/
theorem quaternionHaar_canonical
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      SupportedQuaternionBlocks blocks polynomial →
      quaternionHaar blocks
          (canonicalQuaternionPolynomial
            blocks polynomial) ≈
        quaternionHaar blocks polynomial
  | [], _ => Q'.eqv_refl 0
  | term :: rest, hsupport => by
      have hterm :
          term.1.length ≤ 4 * blocks :=
        hsupport term List.mem_cons_self
      have hrest :
          SupportedQuaternionBlocks blocks rest := by
        intro other hother
        exact hsupport other
          (List.mem_cons_of_mem term hother)
      change
        term.2 *
              quaternionHaarMono blocks
                (canonicalQuaternionMonomial
                  blocks term.1) +
            quaternionHaar blocks
              (canonicalQuaternionPolynomial
                blocks rest) ≈
          term.2 *
              quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left term.2 _ _
          (quaternionHaarMono_canonical
            blocks term.1 hterm))
        (quaternionHaar_canonical blocks rest hrest)

/-! ## 2. Exact five-holonomy half-polynomials -/

private theorem supported_polyOne_five :
    SupportedQuaternionBlocks 5 polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons,
    List.not_mem_nil] at hterm
  rcases hterm with hterm | hterm
  · rw [hterm]
    decide
  · exact False.elim hterm

private theorem supported_polyAdd_five
    {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks 5 left)
    (hright : SupportedQuaternionBlocks 5 right) :
    SupportedQuaternionBlocks 5
      (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  rcases hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polySmul_five
    (coefficient : Q') {polynomial : RatPoly}
    (hsupport :
      SupportedQuaternionBlocks 5 polynomial) :
    SupportedQuaternionBlocks 5
      (polySmul coefficient polynomial) := by
  intro term hterm
  simp only [polySmul, List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  exact hsupport source hsource

theorem sourceMehlerWavefunction_supported
    (state : EdgeLabelling) :
    SupportedQuaternionBlocks 5
      (sourceMehlerWavefunction state) := by
  unfold sourceMehlerWavefunction
  split
  · exact supported_polyOne_five
  · exact
      geometricBF4WavefunctionOfState_supported_five
        state

theorem sourceDiagonalComplementMomentPolynomial_supported
    (exponent : Nat) :
    SupportedQuaternionBlocks 5
      (sourceDiagonalComplementMomentPolynomial
        exponent) := by
  let half :=
    polynomialPower sourceDiagonalComplementPolynomial
      (exponent / 2)
  have hhalf :
      SupportedQuaternionBlocks 5 half :=
    polynomialPower_supported
      sourceDiagonalComplement_supported
      (exponent / 2)
  unfold sourceDiagonalComplementMomentPolynomial
  split
  · exact supported_polyMul hhalf hhalf
  · exact supported_polyMul
      (supported_polyMul hhalf hhalf)
      sourceDiagonalComplement_supported

theorem sourceDiagonalShiftedTerm_supported
    (exponent : Nat) :
    SupportedQuaternionBlocks 5
      (sourceDiagonalShiftedTerm exponent) := by
  unfold sourceDiagonalShiftedTerm
  exact supported_polySmul_five _
    (sourceDiagonalComplementMomentPolynomial_supported
      exponent)

theorem sourceDiagonalFeynmanKacPartial_supported :
    ∀ order : Nat,
      SupportedQuaternionBlocks 5
        (sourceDiagonalFeynmanKacPartial order)
  | 0 => by
      intro term hterm
      exact False.elim (List.not_mem_nil hterm)
  | order + 1 =>
      supported_polyAdd_five
        (sourceDiagonalFeynmanKacPartial_supported
          order)
        (sourceDiagonalShiftedTerm_supported order)

theorem sourceKineticFeaturePolynomial_supported
    (feature : BF4KineticFeature) :
    SupportedQuaternionBlocks 5
      (sourceKineticFeaturePolynomial feature) := by
  apply supported_of_bool 5
  revert feature
  decide

theorem sourceFeatureWordPolynomial_supported :
    ∀ word : List BF4KineticFeature,
      SupportedQuaternionBlocks 5
        (sourceFeatureWordPolynomial word)
  | [] => supported_polyOne_five
  | feature :: rest =>
      supported_polyMul
        (sourceKineticFeaturePolynomial_supported
          feature)
        (sourceFeatureWordPolynomial_supported rest)

/-- The literal source-side holonomy integrand whose five-Haar value is one
existing BF4 Mehler half-amplitude. -/
def bf4HolonomyHalfIntegrand
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) : RatPoly :=
  polyMul
    (polyMul
      (sourceMehlerWavefunction state)
      (sourceDiagonalFeynmanKacPartial
        diagonalOrder))
    (sourceFeatureWordPolynomial word)

theorem bf4HolonomyHalfIntegrand_supported
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    SupportedQuaternionBlocks 5
      (bf4HolonomyHalfIntegrand
        diagonalOrder state word) := by
  exact supported_polyMul
    (supported_polyMul
      (sourceMehlerWavefunction_supported state)
      (sourceDiagonalFeynmanKacPartial_supported
        diagonalOrder))
    (sourceFeatureWordPolynomial_supported word)

/-- Canonical twenty-coordinate representative of the exact BF4 holonomy
half-integrand. -/
def bf4ExactHolonomyHalfPolynomial
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) : RatPoly :=
  canonicalQuaternionPolynomial 5
    (bf4HolonomyHalfIntegrand
      diagonalOrder state word)

theorem bf4ExactHolonomyHalfPolynomial_term_length
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature)
    (term : RatTerm)
    (hterm :
      term ∈
        bf4ExactHolonomyHalfPolynomial
          diagonalOrder state word) :
    term.1.length = 20 := by
  unfold bf4ExactHolonomyHalfPolynomial
    canonicalQuaternionPolynomial at hterm
  simp only [List.mem_map] at hterm
  rcases hterm with ⟨source, _, rfl⟩
  rw [canonicalQuaternionMonomial_length]

/-- The canonical holonomy half-polynomial has exactly the previously
constructed five-Haar half-amplitude. -/
theorem bf4ExactHolonomyHalfPolynomial_haar
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    quaternionHaar 5
        (bf4ExactHolonomyHalfPolynomial
          diagonalOrder state word) ≈
      bf4MehlerHalfAmplitude
        diagonalOrder state word := by
  unfold bf4ExactHolonomyHalfPolynomial
    bf4HolonomyHalfIntegrand
    bf4MehlerHalfAmplitude
  exact quaternionHaar_canonical 5 _
    (bf4HolonomyHalfIntegrand_supported
      diagonalOrder state word)

/-! ## 3. Exact reflected source/target gluing -/

/-- One reflected source/target feature channel as a literal polynomial on
five source plus five target holonomies. -/
def bf4ReflectedHolonomyWordPolynomial
    (diagonalOrder : Nat)
    (left right : EdgeLabelling)
    (word : List BF4KineticFeature) : RatPoly :=
  polySmul (bf4FeatureWordWeight word)
    (polyMul
      (bf4ExactHolonomyHalfPolynomial
        diagonalOrder left word)
      (shiftPolynomial 20
        (bf4ExactHolonomyHalfPolynomial
          diagonalOrder right word)))

/-- Exact conditional gluing for one feature channel: the ten-holonomy Haar
integral is its nonnegative weight times the two physical half-amplitudes. -/
theorem bf4ReflectedHolonomyWord_haar_eq_gramTerm
    (diagonalOrder : Nat)
    (left right : EdgeLabelling)
    (word : List BF4KineticFeature) :
    quaternionHaar 10
        (bf4ReflectedHolonomyWordPolynomial
          diagonalOrder left right word) ≈
      bf4FeatureWordWeight word *
        (bf4MehlerHalfAmplitude
            diagonalOrder left word *
          bf4MehlerHalfAmplitude
            diagonalOrder right word) := by
  unfold bf4ReflectedHolonomyWordPolynomial
  refine Q'.eqv_trans _
    (bf4FeatureWordWeight word *
      quaternionHaar 10
        (polyMul
          (bf4ExactHolonomyHalfPolynomial
            diagonalOrder left word)
          (shiftPolynomial 20
            (bf4ExactHolonomyHalfPolynomial
              diagonalOrder right word)))) _
    (quaternionHaar_polySmul
      10 (bf4FeatureWordWeight word) _) ?_
  refine Q'.mul_eqv_congr_left
    (bf4FeatureWordWeight word) _ _ ?_
  refine Q'.eqv_trans _
    (quaternionHaar 5
          (bf4ExactHolonomyHalfPolynomial
            diagonalOrder left word) *
        quaternionHaar 5
          (bf4ExactHolonomyHalfPolynomial
            diagonalOrder right word)) _
    (tenfoldHaar_source_target_factorization
      (bf4ExactHolonomyHalfPolynomial
        diagonalOrder left word)
      (bf4ExactHolonomyHalfPolynomial
        diagonalOrder right word)
      (bf4ExactHolonomyHalfPolynomial_term_length
        diagonalOrder left word)
      (bf4ExactHolonomyHalfPolynomial_term_length
        diagonalOrder right word)) ?_
  exact Q'.eqv_trans _
    (bf4MehlerHalfAmplitude diagonalOrder left word *
      quaternionHaar 5
        (bf4ExactHolonomyHalfPolynomial
          diagonalOrder right word)) _
    (Q'.mul_eqv_congr_right _ _ _
      (bf4ExactHolonomyHalfPolynomial_haar
        diagonalOrder left word))
    (Q'.mul_eqv_congr_left _ _ _
      (bf4ExactHolonomyHalfPolynomial_haar
        diagonalOrder right word))

/-- Sum of the literal reflected holonomy-channel polynomials over a
displayed finite word list. -/
def bf4GroupedHolonomyPolynomialOn
    (diagonalOrder : Nat)
    (left right : EdgeLabelling) :
    List (List BF4KineticFeature) → RatPoly
  | [] => polyZero
  | word :: rest =>
      polyAdd
        (bf4ReflectedHolonomyWordPolynomial
          diagonalOrder left right word)
        (bf4GroupedHolonomyPolynomialOn
          diagonalOrder left right rest)

/-- The positive finite grouped Feynman--Kac kernel as one polynomial before
the final ten-holonomy conditional Haar integration. -/
def bf4GroupedHolonomyGluingPolynomial
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : RatPoly :=
  bf4GroupedHolonomyPolynomialOn
    diagonalOrder left right
    (bf4FeatureWordsAtMost crossOrder)

private theorem bf4GroupedHolonomyPolynomialOn_haar
    (diagonalOrder : Nat)
    (left right : EdgeLabelling) :
    ∀ words : List (List BF4KineticFeature),
      quaternionHaar 10
          (bf4GroupedHolonomyPolynomialOn
            diagonalOrder left right words) ≈
        listQSum
          (fun word =>
            bf4FeatureWordWeight word *
              (bf4MehlerHalfAmplitude
                  diagonalOrder left word *
                bf4MehlerHalfAmplitude
                  diagonalOrder right word))
          words
  | [] => Q'.eqv_refl 0
  | word :: rest => by
      unfold bf4GroupedHolonomyPolynomialOn
        listQSum
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_append
          10
          (bf4ReflectedHolonomyWordPolynomial
            diagonalOrder left right word)
          (bf4GroupedHolonomyPolynomialOn
            diagonalOrder left right rest))
        (Q'.add_eqv_congr'
          (bf4ReflectedHolonomyWord_haar_eq_gramTerm
            diagonalOrder left right word)
          (bf4GroupedHolonomyPolynomialOn_haar
            diagonalOrder left right rest))

/-- **Exact grouped holonomy gluing identity.**  Integrating the literal
reflected source/target polynomial over all ten retained holonomies gives
exactly the existing all-spin positive feature Gram entry. -/
theorem bf4GroupedHolonomyGluing_haar_eq_mehlerGram
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    quaternionHaar 10
        (bf4GroupedHolonomyGluingPolynomial
          diagonalOrder crossOrder left right) ≈
      bf4MehlerGramNumerator
        diagonalOrder crossOrder left right := by
  unfold bf4GroupedHolonomyGluingPolynomial
    bf4MehlerGramNumerator weightedGram
  exact bf4GroupedHolonomyPolynomialOn_haar
    diagonalOrder left right
    (bf4FeatureWordsAtMost crossOrder)

/-! ## 4. Arbitrary signed packets are literal integral squares -/

/-- Finite signed state packet used to test the reflected kernel. -/
abbrev BF4HolonomyStatePacket :=
  List (Q' × EdgeLabelling)

/-- Linear combination of exact canonical half-polynomials in one displayed
feature channel. -/
def bf4PacketHalfPolynomial
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    BF4HolonomyStatePacket → RatPoly
  | [] => polyZero
  | weightedState :: rest =>
      polyAdd
        (polySmul weightedState.1
          (bf4ExactHolonomyHalfPolynomial
            diagonalOrder weightedState.2 word))
        (bf4PacketHalfPolynomial
          diagonalOrder word rest)

theorem bf4PacketHalfPolynomial_term_length
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      ∀ term,
        term ∈
            bf4PacketHalfPolynomial
              diagonalOrder word packet →
          term.1.length = 20
  | [], term, hterm =>
      False.elim (List.not_mem_nil hterm)
  | weightedState :: rest, term, hterm => by
      simp only [bf4PacketHalfPolynomial,
        polyAdd, List.mem_append, polySmul,
        List.mem_map] at hterm
      rcases hterm with
        ⟨source, hsource, rfl⟩ | hrest
      · exact
          bf4ExactHolonomyHalfPolynomial_term_length
            diagonalOrder weightedState.2 word
            source hsource
      · exact bf4PacketHalfPolynomial_term_length
          diagonalOrder word rest term hrest

/-- The Haar value of a packet half-polynomial is the corresponding linear
combination of exact BF4 half-amplitudes. -/
theorem bf4PacketHalfPolynomial_haar
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      quaternionHaar 5
          (bf4PacketHalfPolynomial
            diagonalOrder word packet) ≈
        listQSum
          (fun weightedState =>
            weightedState.1 *
              bf4MehlerHalfAmplitude
                diagonalOrder weightedState.2 word)
          packet
  | [] => Q'.eqv_refl 0
  | weightedState :: rest => by
      unfold bf4PacketHalfPolynomial listQSum
      refine Q'.eqv_trans _
        (quaternionHaar 5
              (polySmul weightedState.1
                (bf4ExactHolonomyHalfPolynomial
                  diagonalOrder weightedState.2 word)) +
            quaternionHaar 5
              (bf4PacketHalfPolynomial
                diagonalOrder word rest)) _
        (quaternionHaar_append 5 _ _) ?_
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (quaternionHaar_polySmul
            5 weightedState.1 _)
          (Q'.mul_eqv_congr_left
            weightedState.1 _ _
            (bf4ExactHolonomyHalfPolynomial_haar
              diagonalOrder weightedState.2 word)))
        (bf4PacketHalfPolynomial_haar
          diagonalOrder word rest)

/-- One weighted reflected square of a signed packet in a common feature
channel. -/
def bf4PacketReflectedSquarePolynomial
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : RatPoly :=
  let half :=
    bf4PacketHalfPolynomial
      diagonalOrder word packet
  polySmul (bf4FeatureWordWeight word)
    (polyMul half (shiftPolynomial 20 half))

/-- Sum of all displayed reflected packet squares before ten-holonomy Haar
integration. -/
def bf4PacketGroupedSquarePolynomialOn
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    List (List BF4KineticFeature) → RatPoly
  | [] => polyZero
  | word :: rest =>
      polyAdd
        (bf4PacketReflectedSquarePolynomial
          diagonalOrder packet word)
        (bf4PacketGroupedSquarePolynomialOn
          diagonalOrder packet rest)

def bf4PacketGroupedSquarePolynomial
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  bf4PacketGroupedSquarePolynomialOn
    diagonalOrder packet
    (bf4FeatureWordsAtMost crossOrder)

private theorem bf4PacketReflectedSquare_haar
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    quaternionHaar 10
        (bf4PacketReflectedSquarePolynomial
          diagonalOrder packet word) ≈
      bf4FeatureWordWeight word *
        (listQSum
            (fun weightedState =>
              weightedState.1 *
                bf4MehlerHalfAmplitude
                  diagonalOrder weightedState.2 word)
            packet *
          listQSum
            (fun weightedState =>
              weightedState.1 *
                bf4MehlerHalfAmplitude
                  diagonalOrder weightedState.2 word)
            packet) := by
  unfold bf4PacketReflectedSquarePolynomial
  let half :=
    bf4PacketHalfPolynomial
      diagonalOrder word packet
  refine Q'.eqv_trans _
    (bf4FeatureWordWeight word *
      quaternionHaar 10
        (polyMul half
          (shiftPolynomial 20 half))) _
    (quaternionHaar_polySmul
      10 (bf4FeatureWordWeight word) _) ?_
  refine Q'.mul_eqv_congr_left
    (bf4FeatureWordWeight word) _ _ ?_
  refine Q'.eqv_trans _
    (quaternionHaar 5 half *
      quaternionHaar 5 half) _
    (tenfoldHaar_source_target_factorization
      half half
      (bf4PacketHalfPolynomial_term_length
        diagonalOrder word packet)
      (bf4PacketHalfPolynomial_term_length
        diagonalOrder word packet)) ?_
  exact Q'.eqv_trans _
    (listQSum
          (fun weightedState =>
            weightedState.1 *
              bf4MehlerHalfAmplitude
                diagonalOrder weightedState.2 word)
          packet *
      quaternionHaar 5 half) _
    (Q'.mul_eqv_congr_right _ _ _
      (bf4PacketHalfPolynomial_haar
        diagonalOrder word packet))
    (Q'.mul_eqv_congr_left _ _ _
      (bf4PacketHalfPolynomial_haar
        diagonalOrder word packet))

private theorem bf4PacketGroupedSquarePolynomialOn_haar
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    ∀ words : List (List BF4KineticFeature),
      quaternionHaar 10
          (bf4PacketGroupedSquarePolynomialOn
            diagonalOrder packet words) ≈
        listQSum
          (fun word =>
            bf4FeatureWordWeight word *
              (listQSum
                  (fun weightedState =>
                    weightedState.1 *
                      bf4MehlerHalfAmplitude
                        diagonalOrder
                        weightedState.2 word)
                  packet *
                listQSum
                  (fun weightedState =>
                    weightedState.1 *
                      bf4MehlerHalfAmplitude
                        diagonalOrder
                        weightedState.2 word)
                  packet))
          words
  | [] => Q'.eqv_refl 0
  | word :: rest => by
      unfold bf4PacketGroupedSquarePolynomialOn
        listQSum
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_append
          10
          (bf4PacketReflectedSquarePolynomial
            diagonalOrder packet word)
          (bf4PacketGroupedSquarePolynomialOn
            diagonalOrder packet rest))
        (Q'.add_eqv_congr'
          (bf4PacketReflectedSquare_haar
            diagonalOrder packet word)
          (bf4PacketGroupedSquarePolynomialOn_haar
            diagonalOrder packet rest))

/-- The grouped packet integral is exactly the manifest channelwise
sum-of-squares expression. -/
theorem bf4PacketGroupedSquare_haar_eq_sos
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) ≈
      listQSum
        (fun word =>
          bf4FeatureWordWeight word *
            (listQSum
                (fun weightedState =>
                  weightedState.1 *
                    bf4MehlerHalfAmplitude
                      diagonalOrder
                      weightedState.2 word)
                packet *
              listQSum
                (fun weightedState =>
                  weightedState.1 *
                    bf4MehlerHalfAmplitude
                      diagonalOrder
                      weightedState.2 word)
                packet))
        (bf4FeatureWordsAtMost crossOrder) := by
  unfold bf4PacketGroupedSquarePolynomial
  exact bf4PacketGroupedSquarePolynomialOn_haar
    diagonalOrder packet
    (bf4FeatureWordsAtMost crossOrder)

/-- Canonical signed packet associated to a displayed finite state list and
coefficient function.  Repeated states remain repeated, exactly as in the
finite quadratic form. -/
def bf4HolonomyPacketOfStates
    (states : List EdgeLabelling)
    (coefficient : EdgeLabelling → Q') :
    BF4HolonomyStatePacket :=
  states.map fun state => (coefficient state, state)

private theorem bf4HolonomyPacketOfStates_linear
    (diagonalOrder : Nat)
    (coefficient : EdgeLabelling → Q')
    (word : List BF4KineticFeature) :
    ∀ states : List EdgeLabelling,
      listQSum
          (fun weightedState =>
            weightedState.1 *
              bf4MehlerHalfAmplitude
                diagonalOrder weightedState.2 word)
          (bf4HolonomyPacketOfStates
            states coefficient) ≈
        channelLinear states
          (bf4MehlerHalfAmplitude diagonalOrder)
          coefficient word
  | [] => Q'.eqv_refl 0
  | state :: rest => by
      unfold bf4HolonomyPacketOfStates
        channelLinear listQSum List.map
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (bf4HolonomyPacketOfStates_linear
          diagonalOrder coefficient word rest)

/-- **Finite Choi factorization.**  The literal grouped reflected
ten-holonomy integral of the packet associated to `states` is exactly the
complete quadratic form of the existing BF4 feature Gram.  Thus the entry
identity above and the packet integral-square identity describe the same
operator, not merely two separately positive constructions. -/
theorem bf4StatePacketGroupedSquare_haar_eq_weightedGramQuadratic
    (diagonalOrder crossOrder : Nat)
    (states : List EdgeLabelling)
    (coefficient : EdgeLabelling → Q') :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder
          (bf4HolonomyPacketOfStates
            states coefficient)) ≈
      weightedGramQuadratic
        states
        (bf4FeatureWordsAtMost crossOrder)
        bf4FeatureWordWeight
        (bf4MehlerHalfAmplitude diagonalOrder)
        coefficient := by
  refine Q'.eqv_trans _
    (listQSum
      (fun word =>
        bf4FeatureWordWeight word *
          (channelLinear states
              (bf4MehlerHalfAmplitude diagonalOrder)
              coefficient word *
            channelLinear states
              (bf4MehlerHalfAmplitude diagonalOrder)
              coefficient word))
      (bf4FeatureWordsAtMost crossOrder)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (bf4PacketGroupedSquare_haar_eq_sos
        diagonalOrder crossOrder
        (bf4HolonomyPacketOfStates
          states coefficient)) ?_
    apply listQSum_congr
    intro word
    exact Q'.mul_eqv_congr_left
      (bf4FeatureWordWeight word) _ _
      (Q'.eqv_trans _
        (channelLinear states
            (bf4MehlerHalfAmplitude diagonalOrder)
            coefficient word *
          listQSum
            (fun weightedState =>
              weightedState.1 *
                bf4MehlerHalfAmplitude
                  diagonalOrder weightedState.2 word)
            (bf4HolonomyPacketOfStates
              states coefficient)) _
        (Q'.mul_eqv_congr_right _ _ _
          (bf4HolonomyPacketOfStates_linear
            diagonalOrder coefficient word states))
        (Q'.mul_eqv_congr_left _ _ _
          (bf4HolonomyPacketOfStates_linear
            diagonalOrder coefficient word states)))
  · exact Q'.eqv_symm
      (weightedGramQuadratic_eq_sos
        states
        (bf4FeatureWordsAtMost crossOrder)
        bf4FeatureWordWeight
        (bf4MehlerHalfAmplitude diagonalOrder)
        coefficient)

/-- Appending nonnegative summands can only increase a constructive rational
list sum.  This is kept local because the physical content below is the
positive-semidefinite order statement, rather than the generic list fact. -/
private theorem listQSum_prefix_le_append
    {A : Type}
    (value : A → Q')
    (left right : List A)
    (hright :
      ∀ item, item ∈ right →
        (0 : Q') ≤ value item) :
    listQSum value left ≤
      listQSum value (left ++ right) := by
  have hrightSum :
      (0 : Q') ≤ listQSum value right :=
    listQSum_nonnegative_on value right hright
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg
      (listQSum value left)
      (listQSum value right)
      hrightSum)
    (Q'.ge_of_eqv
      (listQSum_append value left right))

/-- **Directed positive-kernel approximation.**  Increasing the kinetic
word cutoff by one adds a finite family of nonnegatively weighted reflected
packet squares.  Hence the grouped ten-holonomy kernels are monotone in
positive-semidefinite order, uniformly for every finite signed state packet.

This is stronger than entrywise diagonal monotonicity and is the exact order
needed for a constructive positive-kernel limit.  It does not supply the
missing uniform upper bound or Cauchy modulus. -/
theorem bf4PacketGroupedSquare_haar_cross_mono
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) ≤
      quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder (crossOrder + 1) packet) := by
  let value : List BF4KineticFeature → Q' :=
    fun word =>
      bf4FeatureWordWeight word *
        (listQSum
            (fun weightedState =>
              weightedState.1 *
                bf4MehlerHalfAmplitude
                  diagonalOrder weightedState.2 word)
            packet *
          listQSum
            (fun weightedState =>
              weightedState.1 *
                bf4MehlerHalfAmplitude
                  diagonalOrder weightedState.2 word)
            packet)
  have hprefix :
      listQSum value
          (bf4FeatureWordsAtMost crossOrder) ≤
        listQSum value
          (bf4FeatureWordsAtMost crossOrder ++
            bf4FeatureWordsExact (crossOrder + 1)) := by
    apply listQSum_prefix_le_append
    intro word _
    exact Q'.mul_nonneg _ _
      (bf4FeatureWordWeight_nonnegative word)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (bf4PacketGroupedSquare_haar_eq_sos
        diagonalOrder crossOrder packet)) ?_
  refine Q'.le_trans' _ _ _ hprefix ?_
  exact Q'.ge_of_eqv
    (bf4PacketGroupedSquare_haar_eq_sos
      diagonalOrder (crossOrder + 1) packet)

/-- **Certificate-free reflected packet positivity.**  Every finite signed
all-spin packet has a nonnegative grouped ten-holonomy integral because the
exact gluing identity rewrites it as a nonnegatively weighted sum of literal
rational squares. -/
theorem bf4PacketGroupedSquare_haar_nonnegative
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) := by
  have hsos :
      (0 : Q') ≤
        listQSum
          (fun word =>
            bf4FeatureWordWeight word *
              (listQSum
                  (fun weightedState =>
                    weightedState.1 *
                      bf4MehlerHalfAmplitude
                        diagonalOrder
                        weightedState.2 word)
                  packet *
                listQSum
                  (fun weightedState =>
                    weightedState.1 *
                      bf4MehlerHalfAmplitude
                        diagonalOrder
                        weightedState.2 word)
                  packet))
          (bf4FeatureWordsAtMost crossOrder) := by
    apply listQSum_nonnegative_on
    intro word _
    exact Q'.mul_nonneg _ _
      (bf4FeatureWordWeight_nonnegative word)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (bf4PacketGroupedSquare_haar_eq_sos
          diagonalOrder crossOrder packet)))

end YMGap.Continuum.BF4GroupedGramChoiKernel

#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.quaternionHaar_canonical
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4ExactHolonomyHalfPolynomial_haar
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4ReflectedHolonomyWord_haar_eq_gramTerm
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4GroupedHolonomyGluing_haar_eq_mehlerGram
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4PacketGroupedSquare_haar_eq_sos
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4StatePacketGroupedSquare_haar_eq_weightedGramQuadratic
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4PacketGroupedSquare_haar_cross_mono
#print axioms YMGap.Continuum.BF4GroupedGramChoiKernel.bf4PacketGroupedSquare_haar_nonnegative
