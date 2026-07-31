/-
# Aggregate factorial majorant for the grouped BF4 kinetic words

The positive grouped BF4 holonomy kernel is indexed by all ordered words in
the fifteen positive kinetic LDL features.  A pointwise bound on one word is
not enough for cutoff removal: the number of words grows exponentially.

This file performs the required all-word regrouping before taking a tail.
For one feature `f`, let

  a_f = featureWeight(f) * ‖featurePolynomial(f)‖₁²

and put `S = Σ_f a_f`.  The factorial word weight and finite Fubini give the
exact aggregate identity

  Σ_{|w|=n} wordMajorant(w) = Sⁿ / n!.

Thus the complete carrier growth is absorbed into one constructive
exponential majorant.  The next layer can multiply this scalar identity by
the packet/diagonal prefactor and feed it directly to `ExpNeg`'s explicit
factorial-tail modulus.

This is an analytic majorant for the exact positive feature carrier.  It
does not yet identify the resulting limit with the compact physical
endpoint.

## Axiom gate

Finite lists, exact `Q'` order/ring algebra, coefficient `L¹` norms, and
kernel reduction only.  No `Classical.*`, `native_decide`, `sorry`, custom
axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedGramChoiKernel
import YMGap.Continuum.BF4CompactActionShiftedLimit

namespace YMGap.Continuum.BF4GroupedHolonomyCrossMajorant

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.RatNat
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The aggregate scalar attached to the fifteen features -/

/-- Coefficient `L¹` size of one exact source-side kinetic feature. -/
def bf4KineticFeaturePolynomialL1
    (feature : BF4KineticFeature) : Q' :=
  polynomialCoefficientL1
    (sourceKineticFeaturePolynomial feature)

/-- One feature's contribution to the cross-word majorant. -/
def bf4KineticFeatureMajorantAtom
    (feature : BF4KineticFeature) : Q' :=
  bf4KineticFeatureWeight feature *
    (bf4KineticFeaturePolynomialL1 feature *
      bf4KineticFeaturePolynomialL1 feature)

/-- Aggregate cross-exponential majorant after summing the full fifteen
feature alphabet. -/
def bf4KineticCrossMajorant : Q' :=
  listQSum bf4KineticFeatureMajorantAtom
    bf4KineticFeatureAlphabet

theorem bf4KineticFeaturePolynomialL1_nonnegative
    (feature : BF4KineticFeature) :
    (0 : Q') ≤
      bf4KineticFeaturePolynomialL1 feature :=
  polynomialCoefficientL1_nonnegative _

theorem bf4KineticFeatureMajorantAtom_nonnegative
    (feature : BF4KineticFeature) :
    (0 : Q') ≤
      bf4KineticFeatureMajorantAtom feature := by
  exact Q'.mul_nonneg _ _
    (bf4KineticFeatureWeight_nonnegative feature)
    (Q'.mul_nonneg _ _
      (bf4KineticFeaturePolynomialL1_nonnegative
        feature)
      (bf4KineticFeaturePolynomialL1_nonnegative
        feature))

theorem bf4KineticCrossMajorant_nonnegative :
    (0 : Q') ≤ bf4KineticCrossMajorant := by
  unfold bf4KineticCrossMajorant
  apply listQSum_nonnegative_on
  intro feature _
  exact bf4KineticFeatureMajorantAtom_nonnegative
    feature

/-! ## 2. Word lengths and coefficient-norm products -/

/-- Every word in the exact-length enumeration has the displayed length. -/
theorem bf4FeatureWordsExact_word_length :
    ∀ length word,
      word ∈ bf4FeatureWordsExact length →
        word.length = length
  | 0, word, hword => by
      simp only [bf4FeatureWordsExact,
        List.mem_cons, List.not_mem_nil] at hword
      rcases hword with hword | hword
      · subst word
        rfl
      · exact False.elim hword
  | length + 1, word, hword => by
      simp only [bf4FeatureWordsExact,
        List.mem_flatMap, List.mem_map] at hword
      rcases hword with
        ⟨feature, _, rest, hrest, rfl⟩
      rw [List.length_cons,
        bf4FeatureWordsExact_word_length
          length rest hrest]

/-- Product of the coefficient `L¹` feature sizes in one ordered word. -/
def bf4FeatureWordPolynomialL1Product :
    List BF4KineticFeature → Q'
  | [] => 1
  | feature :: rest =>
      bf4KineticFeaturePolynomialL1 feature *
        bf4FeatureWordPolynomialL1Product rest

theorem bf4FeatureWordPolynomialL1Product_nonnegative :
    ∀ word,
      (0 : Q') ≤
        bf4FeatureWordPolynomialL1Product word
  | [] => Q'.zero_le_one
  | feature :: rest =>
      Q'.mul_nonneg _ _
        (bf4KineticFeaturePolynomialL1_nonnegative
          feature)
        (bf4FeatureWordPolynomialL1Product_nonnegative
          rest)

/-- The literal feature-word polynomial is dominated by the product of the
individual feature coefficient norms. -/
theorem sourceFeatureWordPolynomial_l1_le :
    ∀ word,
      polynomialCoefficientL1
          (sourceFeatureWordPolynomial word) ≤
        bf4FeatureWordPolynomialL1Product word
  | [] => by
      change Q'.abs (1 : Q') + 0 ≤ 1
      decide
  | feature :: rest => by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le
          (sourceKineticFeaturePolynomial feature)
          (sourceFeatureWordPolynomial rest))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (sourceFeatureWordPolynomial_l1_le rest)
          (bf4KineticFeaturePolynomialL1_nonnegative
            feature))

/-! ## 3. Exact all-word factorial collapse -/

/-- Scalar majorant of one complete reflected word channel. -/
def bf4FeatureWordMajorant
    (word : List BF4KineticFeature) : Q' :=
  bf4FeatureWordWeight word *
    (bf4FeatureWordPolynomialL1Product word *
      bf4FeatureWordPolynomialL1Product word)

theorem bf4FeatureWordMajorant_nonnegative
    (word : List BF4KineticFeature) :
    (0 : Q') ≤ bf4FeatureWordMajorant word := by
  exact Q'.mul_nonneg _ _
    (bf4FeatureWordWeight_nonnegative word)
    (Q'.mul_nonneg _ _
      (bf4FeatureWordPolynomialL1Product_nonnegative
        word)
      (bf4FeatureWordPolynomialL1Product_nonnegative
        word))

/-- Prepending one feature multiplies the word majorant by its atom and the
next reciprocal factorial factor. -/
theorem bf4FeatureWordMajorant_cons
    (feature : BF4KineticFeature)
    (rest : List BF4KineticFeature) :
    bf4FeatureWordMajorant (feature :: rest) ≈
      (bf4KineticFeatureMajorantAtom feature *
        Q'.invSucc rest.length) *
      bf4FeatureWordMajorant rest := by
  let weight :=
    bf4KineticFeatureWeight feature
  let reciprocal := Q'.invSucc rest.length
  let restWeight := bf4FeatureWordWeight rest
  let featureL1 :=
    bf4KineticFeaturePolynomialL1 feature
  let restL1 :=
    bf4FeatureWordPolynomialL1Product rest
  change
    ((weight * reciprocal) * restWeight) *
        ((featureL1 * restL1) *
          (featureL1 * restL1)) ≈
      ((weight * (featureL1 * featureL1)) *
          reciprocal) *
        (restWeight * (restL1 * restL1))
  q_ring

/-- Sum of all word majorants at one exact kinetic length. -/
def bf4FeatureWordMajorantSumExact
    (length : Nat) : Q' :=
  listQSum bf4FeatureWordMajorant
    (bf4FeatureWordsExact length)

private theorem bf4FeatureWordMajorant_map_cons_sum
    (length : Nat)
    (feature : BF4KineticFeature) :
    listQSum bf4FeatureWordMajorant
        ((bf4FeatureWordsExact length).map
          fun word => feature :: word) ≈
      (bf4KineticFeatureMajorantAtom feature *
        Q'.invSucc length) *
      bf4FeatureWordMajorantSumExact length := by
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun word =>
        (bf4KineticFeatureMajorantAtom feature *
          Q'.invSucc length) *
        bf4FeatureWordMajorant word)
      (bf4FeatureWordsExact length)) _ ?_ ?_
  · apply listQSum_congr_on
    intro word hword
    have hlength :=
      bf4FeatureWordsExact_word_length
        length word hword
    rw [← hlength]
    exact bf4FeatureWordMajorant_cons
      feature word
  · exact listQSum_mul_left
      (bf4KineticFeatureMajorantAtom feature *
        Q'.invSucc length)
      bf4FeatureWordMajorant
      (bf4FeatureWordsExact length)

private theorem bf4FeatureWordMajorantSumExact_succ
    (length : Nat) :
    bf4FeatureWordMajorantSumExact (length + 1) ≈
      (bf4KineticCrossMajorant *
        Q'.invSucc length) *
      bf4FeatureWordMajorantSumExact length := by
  change
    listQSum bf4FeatureWordMajorant
        (bf4KineticFeatureAlphabet.flatMap
          fun feature =>
            (bf4FeatureWordsExact length).map
              fun word => feature :: word) ≈
      (bf4KineticCrossMajorant *
          Q'.invSucc length) *
        bf4FeatureWordMajorantSumExact length
  calc
    _ ≈
        listQSum
          (fun feature =>
            listQSum bf4FeatureWordMajorant
              ((bf4FeatureWordsExact length).map
                fun word => feature :: word))
          bf4KineticFeatureAlphabet :=
      listQSum_flatMap
        bf4FeatureWordMajorant
        (fun feature =>
          (bf4FeatureWordsExact length).map
            fun word => feature :: word)
        bf4KineticFeatureAlphabet
    _ ≈
        listQSum
          (fun feature =>
            (bf4KineticFeatureMajorantAtom feature *
              Q'.invSucc length) *
            bf4FeatureWordMajorantSumExact length)
          bf4KineticFeatureAlphabet :=
      listQSum_congr
        (bf4FeatureWordMajorant_map_cons_sum
          length)
        bf4KineticFeatureAlphabet
    _ ≈
        listQSum
            (fun feature =>
              bf4KineticFeatureMajorantAtom feature *
                Q'.invSucc length)
            bf4KineticFeatureAlphabet *
          bf4FeatureWordMajorantSumExact length :=
      listQSum_mul_right
        (fun feature =>
          bf4KineticFeatureMajorantAtom feature *
            Q'.invSucc length)
        (bf4FeatureWordMajorantSumExact length)
        bf4KineticFeatureAlphabet
    _ ≈
        (bf4KineticCrossMajorant *
            Q'.invSucc length) *
          bf4FeatureWordMajorantSumExact length :=
      Q'.mul_eqv_congr_right _ _
        (bf4FeatureWordMajorantSumExact length)
        (listQSum_mul_right
          bf4KineticFeatureMajorantAtom
          (Q'.invSucc length)
          bf4KineticFeatureAlphabet)

/-- **All-label factorial collapse.**  After summing every ordered word of
length `n`, the exponential carrier growth is exactly the single factorial
term `Sⁿ/n!`, with `S = bf4KineticCrossMajorant`. -/
theorem bf4FeatureWordMajorantSumExact_eq_termAbs :
    ∀ length : Nat,
      bf4FeatureWordMajorantSumExact length ≈
        ExpNeg.termAbs
          bf4KineticCrossMajorant length
  | 0 => by
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | length + 1 => by
      refine Q'.eqv_trans _
        ((bf4KineticCrossMajorant *
            Q'.invSucc length) *
          bf4FeatureWordMajorantSumExact length) _
        (bf4FeatureWordMajorantSumExact_succ
          length) ?_
      refine Q'.eqv_trans _
        ((bf4KineticCrossMajorant *
            Q'.invSucc length) *
          ExpNeg.termAbs
            bf4KineticCrossMajorant length) _
        (Q'.mul_eqv_congr_left _ _ _
          (bf4FeatureWordMajorantSumExact_eq_termAbs
            length)) ?_
      change
        (bf4KineticCrossMajorant *
            Q'.invSucc length) *
            ExpNeg.termAbs
              bf4KineticCrossMajorant length ≈
          ExpNeg.termAbs
              bf4KineticCrossMajorant length *
            (bf4KineticCrossMajorant *
              Q'.invSucc length)
      exact Q'.mul_comm_eqv _ _

/-! ## 4. The exact packet half-amplitude is bounded by the word product -/

theorem polynomialCoefficientL1_polyAdd
    (left : RatPoly) :
    ∀ right : RatPoly,
      polynomialCoefficientL1
          (polyAdd left right) ≈
        polynomialCoefficientL1 left +
          polynomialCoefficientL1 right
  | right => by
      induction left with
      | nil =>
          exact Q'.eqv_symm
            (QPoly.q_zero_add_eqv
              (polynomialCoefficientL1 right))
      | cons term rest induction =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left
              (Q'.abs term.2) _ _ induction)
            (Q'.eqv_symm
              (Q'.add_assoc_eqv
                (Q'.abs term.2)
                (polynomialCoefficientL1 rest)
                (polynomialCoefficientL1 right)))

private theorem canonicalQuaternionPolynomial_l1
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      polynomialCoefficientL1
          (canonicalQuaternionPolynomial
            blocks polynomial) =
        polynomialCoefficientL1 polynomial
  | [] => rfl
  | term :: rest => by
      change
        Q'.abs term.2 +
            polynomialCoefficientL1
              (canonicalQuaternionPolynomial
                blocks rest) =
          Q'.abs term.2 +
            polynomialCoefficientL1 rest
      rw [canonicalQuaternionPolynomial_l1
        blocks rest]

/-- Coefficient-norm prefactor of a signed packet after inserting the
displayed diagonal Feynman--Kac partial, but before a kinetic word. -/
def bf4PacketDiagonalHalfL1Scale
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  listQSum
    (fun weightedState =>
      Q'.abs weightedState.1 *
        (polynomialCoefficientL1
            (sourceMehlerWavefunction
              weightedState.2) *
          polynomialCoefficientL1
            (sourceDiagonalFeynmanKacPartial
              diagonalOrder)))
    packet

theorem bf4PacketDiagonalHalfL1Scale_nonnegative
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet := by
  unfold bf4PacketDiagonalHalfL1Scale
  apply listQSum_nonnegative_on
  intro weightedState _
  exact Q'.mul_nonneg _ _
    (Q'.abs_nonneg weightedState.1)
    (Q'.mul_nonneg _ _
      (polynomialCoefficientL1_nonnegative _)
      (polynomialCoefficientL1_nonnegative _))

private theorem bf4HolonomyHalfIntegrand_l1_le
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    polynomialCoefficientL1
        (bf4HolonomyHalfIntegrand
          diagonalOrder state word) ≤
      (polynomialCoefficientL1
          (sourceMehlerWavefunction state) *
        polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial
            diagonalOrder)) *
      bf4FeatureWordPolynomialL1Product word := by
  let wave :=
    sourceMehlerWavefunction state
  let diagonal :=
    sourceDiagonalFeynmanKacPartial
      diagonalOrder
  let featureWord :=
    sourceFeatureWordPolynomial word
  have hleft :
      polynomialCoefficientL1
          (polyMul wave diagonal) ≤
        polynomialCoefficientL1 wave *
          polynomialCoefficientL1 diagonal :=
    polynomialCoefficientL1_mul_le wave diagonal
  have hword :
      polynomialCoefficientL1 featureWord ≤
        bf4FeatureWordPolynomialL1Product word :=
    sourceFeatureWordPolynomial_l1_le word
  have hleft0 :
      (0 : Q') ≤
        polynomialCoefficientL1
          (polyMul wave diagonal) :=
    polynomialCoefficientL1_nonnegative _
  have hwordProduct0 :
      (0 : Q') ≤
        bf4FeatureWordPolynomialL1Product word :=
    bf4FeatureWordPolynomialL1Product_nonnegative
      word
  exact Q'.le_trans' _ _ _
    (polynomialCoefficientL1_mul_le
      (polyMul wave diagonal) featureWord)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hword hleft0)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hleft hwordProduct0))

private theorem bf4ExactHolonomyHalfPolynomial_l1_le
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    polynomialCoefficientL1
        (bf4ExactHolonomyHalfPolynomial
          diagonalOrder state word) ≤
      (polynomialCoefficientL1
          (sourceMehlerWavefunction state) *
        polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial
            diagonalOrder)) *
      bf4FeatureWordPolynomialL1Product word := by
  unfold bf4ExactHolonomyHalfPolynomial
  rw [canonicalQuaternionPolynomial_l1]
  exact bf4HolonomyHalfIntegrand_l1_le
    diagonalOrder state word

/-- The complete signed packet half-polynomial is bounded by one
packet/diagonal scale times the multiplicative feature-word norm. -/
theorem bf4PacketHalfPolynomial_l1_le
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      polynomialCoefficientL1
          (bf4PacketHalfPolynomial
            diagonalOrder word packet) ≤
        bf4PacketDiagonalHalfL1Scale
            diagonalOrder packet *
          bf4FeatureWordPolynomialL1Product word
  | [] => by
      change (0 : Q') ≤
        0 *
          bf4FeatureWordPolynomialL1Product word
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv _))
  | weightedState :: rest => by
      let headBase :=
        Q'.abs weightedState.1 *
          (polynomialCoefficientL1
              (sourceMehlerWavefunction
                weightedState.2) *
            polynomialCoefficientL1
              (sourceDiagonalFeynmanKacPartial
                diagonalOrder))
      let wordProduct :=
        bf4FeatureWordPolynomialL1Product word
      have hhead :
          polynomialCoefficientL1
              (polySmul weightedState.1
                (bf4ExactHolonomyHalfPolynomial
                  diagonalOrder weightedState.2 word)) ≤
            headBase * wordProduct := by
        refine Q'.le_trans' _ _ _
          (polynomialCoefficientL1_smul_le
            weightedState.1
            (bf4ExactHolonomyHalfPolynomial
              diagonalOrder weightedState.2 word)) ?_
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (bf4ExactHolonomyHalfPolynomial_l1_le
              diagonalOrder weightedState.2 word)
            (Q'.abs_nonneg weightedState.1)) ?_
        exact Q'.ge_of_eqv
          (Q'.mul_assoc_eqv
            (Q'.abs weightedState.1)
            (polynomialCoefficientL1
                (sourceMehlerWavefunction
                  weightedState.2) *
              polynomialCoefficientL1
                (sourceDiagonalFeynmanKacPartial
                  diagonalOrder))
            wordProduct)
      have hrest :=
        bf4PacketHalfPolynomial_l1_le
          diagonalOrder word rest
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (polySmul weightedState.1
              (bf4ExactHolonomyHalfPolynomial
                diagonalOrder weightedState.2 word))
            (bf4PacketHalfPolynomial
              diagonalOrder word rest))) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead hrest) ?_
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (q_add_mul
            headBase
            (bf4PacketDiagonalHalfL1Scale
              diagonalOrder rest)
            wordProduct))

/-- Signed packet channel-linear form in one kinetic word. -/
def bf4PacketChannelLinear
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : Q' :=
  listQSum
    (fun weightedState =>
      weightedState.1 *
        bf4MehlerHalfAmplitude
          diagonalOrder weightedState.2 word)
    packet

/-- Haar contraction plus the coefficient norm bounds the exact signed
packet channel-linear form. -/
theorem bf4PacketChannelLinear_abs_le
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4PacketChannelLinear
          diagonalOrder packet word) ≤
      bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet *
        bf4FeatureWordPolynomialL1Product word := by
  have hhaar :=
    bf4PacketHalfPolynomial_haar
      diagonalOrder word packet
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.abs_eqv_congr hhaar))) ?_
  exact Q'.le_trans' _ _ _
    (quaternionHaar_abs_le_coefficientL1
      5
      (bf4PacketHalfPolynomial
        diagonalOrder word packet))
    (bf4PacketHalfPolynomial_l1_le
      diagonalOrder word packet)

private theorem negmul_self_eqv
    (value : Q') :
    ((-value) * (-value)) ≈ value * value := by
  refine Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv value (-value)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _
      (Q'.mul_neg_eqv value value)) ?_
  exact Q'.neg_neg_eqv (value * value)

private theorem abs_mul_self_eqv
    (value : Q') :
    Q'.abs value * Q'.abs value ≈
      value * value := by
  by_cases hvalue : (0 : Q') ≤ value
  · have habs : Q'.abs value = value := by
      unfold Q'.abs
      rw [if_pos hvalue]
    rw [habs]
    exact Q'.eqv_refl _
  · have habs : Q'.abs value = -value := by
      unfold Q'.abs
      rw [if_neg hvalue]
    rw [habs]
    exact negmul_self_eqv value

/-! ## 5. One exact-length packet increment has a factorial bound -/

/-- Manifest positive packet contribution of one kinetic word. -/
def bf4PacketWordSOS
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : Q' :=
  bf4FeatureWordWeight word *
    (bf4PacketChannelLinear
        diagonalOrder packet word *
      bf4PacketChannelLinear
        diagonalOrder packet word)

theorem bf4PacketWordSOS_nonnegative
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    (0 : Q') ≤
      bf4PacketWordSOS
        diagonalOrder packet word := by
  exact Q'.mul_nonneg _ _
    (bf4FeatureWordWeight_nonnegative word)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)

/-- A complete word channel is bounded by the packet scale squared times
the regrouped word majorant. -/
theorem bf4PacketWordSOS_le_majorant
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    bf4PacketWordSOS
        diagonalOrder packet word ≤
      (bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet *
        bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet) *
      bf4FeatureWordMajorant word := by
  let linear :=
    bf4PacketChannelLinear
      diagonalOrder packet word
  let scale :=
    bf4PacketDiagonalHalfL1Scale
      diagonalOrder packet
  let product :=
    bf4FeatureWordPolynomialL1Product word
  let bound := scale * product
  have hlinear :
      Q'.abs linear ≤ bound :=
    bf4PacketChannelLinear_abs_le
      diagonalOrder packet word
  have hscale0 : (0 : Q') ≤ scale :=
    bf4PacketDiagonalHalfL1Scale_nonnegative
      diagonalOrder packet
  have hproduct0 : (0 : Q') ≤ product :=
    bf4FeatureWordPolynomialL1Product_nonnegative
      word
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _ hscale0 hproduct0
  have hlinearSquare :
      linear * linear ≤ bound * bound := by
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (abs_mul_self_eqv linear)) ?_
    exact Q'.mul_le_mul_of_nonneg
      hlinear hlinear hbound0
      (Q'.abs_nonneg linear)
  unfold bf4PacketWordSOS
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hlinearSquare
      (bf4FeatureWordWeight_nonnegative word)) ?_
  change
    bf4FeatureWordWeight word *
        ((scale * product) * (scale * product)) ≤
      (scale * scale) *
        (bf4FeatureWordWeight word *
          (product * product))
  exact Q'.le_of_eqv (by q_ring)

/-- Packet SOS mass of all words at one exact kinetic length. -/
def bf4PacketCrossExactSOS
    (diagonalOrder length : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  listQSum
    (bf4PacketWordSOS diagonalOrder packet)
    (bf4FeatureWordsExact length)

/-- **Aggregate exact-length packet bound.**  All ordered labels at length
`n` are paid at once by the single factorial term `Sⁿ/n!`. -/
theorem bf4PacketCrossExactSOS_le_factorial
    (diagonalOrder length : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketCrossExactSOS
        diagonalOrder length packet ≤
      (bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet *
        bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet) *
      ExpNeg.termAbs
        bf4KineticCrossMajorant length := by
  let squareScale :=
    bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet *
      bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet
  unfold bf4PacketCrossExactSOS
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (bf4PacketWordSOS diagonalOrder packet)
      (fun word =>
        squareScale *
          bf4FeatureWordMajorant word)
      (bf4FeatureWordsExact length)
      (fun word _ =>
        bf4PacketWordSOS_le_majorant
          diagonalOrder packet word)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_mul_left
        squareScale
        bf4FeatureWordMajorant
        (bf4FeatureWordsExact length))) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left squareScale _ _
      (bf4FeatureWordMajorantSumExact_eq_termAbs
        length))

/-! ## 6. Constructive removal of the kinetic-word cutoff -/

/-- Manifest packet SOS partial through kinetic length `crossOrder`. -/
def bf4PacketCrossSOSPartial
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  listQSum
    (bf4PacketWordSOS diagonalOrder packet)
    (bf4FeatureWordsAtMost crossOrder)

/-- Every manifest packet SOS partial is nonnegative. -/
theorem bf4PacketCrossSOSPartial_nonnegative
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketCrossSOSPartial
        diagonalOrder crossOrder packet := by
  unfold bf4PacketCrossSOSPartial
  apply listQSum_nonnegative_on
  intro word _
  exact bf4PacketWordSOS_nonnegative
    diagonalOrder packet word

/-- The rational SOS partial is exactly the grouped ten-holonomy integral. -/
theorem bf4PacketGroupedSquare_haar_eq_crossSOSPartial
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) ≈
      bf4PacketCrossSOSPartial
        diagonalOrder crossOrder packet := by
  exact bf4PacketGroupedSquare_haar_eq_sos
    diagonalOrder crossOrder packet

/-- Raising the cross cutoff by one appends exactly one full word shell. -/
theorem bf4PacketCrossSOSPartial_succ
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketCrossSOSPartial
        diagonalOrder (crossOrder + 1) packet ≈
      bf4PacketCrossSOSPartial
          diagonalOrder crossOrder packet +
        bf4PacketCrossExactSOS
          diagonalOrder (crossOrder + 1) packet := by
  unfold bf4PacketCrossSOSPartial
    bf4PacketCrossExactSOS
  change
    listQSum
        (bf4PacketWordSOS diagonalOrder packet)
        (bf4FeatureWordsAtMost crossOrder ++
          bf4FeatureWordsExact (crossOrder + 1)) ≈
      listQSum
          (bf4PacketWordSOS diagonalOrder packet)
          (bf4FeatureWordsAtMost crossOrder) +
        listQSum
          (bf4PacketWordSOS diagonalOrder packet)
          (bf4FeatureWordsExact (crossOrder + 1))
  exact listQSum_append
    (bf4PacketWordSOS diagonalOrder packet)
    (bf4FeatureWordsAtMost crossOrder)
    (bf4FeatureWordsExact (crossOrder + 1))

/-- Every exact kinetic shell is nonnegative. -/
theorem bf4PacketCrossExactSOS_nonnegative
    (diagonalOrder length : Nat)
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketCrossExactSOS
        diagonalOrder length packet := by
  unfold bf4PacketCrossExactSOS
  apply listQSum_nonnegative_on
  intro word _
  exact bf4PacketWordSOS_nonnegative
    diagonalOrder packet word

/-- The positive packet partials are directed in the cross cutoff. -/
theorem bf4PacketCrossSOSPartial_add_mono
    (diagonalOrder start : Nat)
    (packet : BF4HolonomyStatePacket) :
    ∀ distance : Nat,
      bf4PacketCrossSOSPartial
          diagonalOrder start packet ≤
        bf4PacketCrossSOSPartial
          diagonalOrder (start + distance) packet
  | 0 => Q'.le_refl' _
  | distance + 1 => by
      have hinduction :=
        bf4PacketCrossSOSPartial_add_mono
          diagonalOrder start packet distance
      have hshell0 :=
        bf4PacketCrossExactSOS_nonnegative
          diagonalOrder (start + distance + 1) packet
      have hstep :
          bf4PacketCrossSOSPartial
              diagonalOrder (start + distance) packet ≤
            bf4PacketCrossSOSPartial
              diagonalOrder (start + distance + 1) packet := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg
            (bf4PacketCrossSOSPartial
              diagonalOrder (start + distance) packet)
            (bf4PacketCrossExactSOS
              diagonalOrder (start + distance + 1)
              packet)
            hshell0) ?_
        exact Q'.ge_of_eqv
          (bf4PacketCrossSOSPartial_succ
            diagonalOrder (start + distance) packet)
      exact Q'.le_trans' _ _ _ hinduction hstep

/-- A whole cross-cutoff block is dominated by the regrouped factorial
block.  The first omitted shell has length `start + 1`. -/
theorem bf4PacketCrossSOSPartial_block_upper
    (diagonalOrder start : Nat)
    (packet : BF4HolonomyStatePacket) :
    ∀ distance : Nat,
      bf4PacketCrossSOSPartial
          diagonalOrder (start + distance) packet ≤
        bf4PacketCrossSOSPartial
            diagonalOrder start packet +
          (bf4PacketDiagonalHalfL1Scale
              diagonalOrder packet *
            bf4PacketDiagonalHalfL1Scale
              diagonalOrder packet) *
            ExpNeg.blockAbs
              bf4KineticCrossMajorant
              (start + 1) distance
  | 0 => by
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (bf4PacketDiagonalHalfL1Scale_nonnegative
              diagonalOrder packet)
            (bf4PacketDiagonalHalfL1Scale_nonnegative
              diagonalOrder packet))
          (Q'.le_refl' 0))
  | distance + 1 => by
      let squareScale :=
        bf4PacketDiagonalHalfL1Scale
            diagonalOrder packet *
          bf4PacketDiagonalHalfL1Scale
            diagonalOrder packet
      have hinduction :=
        bf4PacketCrossSOSPartial_block_upper
          diagonalOrder start packet distance
      have hshell :=
        bf4PacketCrossExactSOS_le_factorial
          diagonalOrder (start + distance + 1) packet
      have hstep :
          bf4PacketCrossSOSPartial
              diagonalOrder
              ((start + distance) + 1) packet ≤
            bf4PacketCrossSOSPartial
                diagonalOrder (start + distance) packet +
              squareScale *
                ExpNeg.termAbs
                  bf4KineticCrossMajorant
                  (start + distance + 1) := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (bf4PacketCrossSOSPartial_succ
              diagonalOrder (start + distance) packet)) ?_
        exact Q'.add_le_add_left _ _ _ hshell
      refine Q'.le_trans' _ _ _ hstep ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ hinduction) ?_
      have hindex :
          start + distance + 1 =
            start + 1 + distance := by
        omega
      rw [hindex]
      dsimp [squareScale]
      change
        (bf4PacketCrossSOSPartial
            diagonalOrder start packet +
          (bf4PacketDiagonalHalfL1Scale
              diagonalOrder packet *
            bf4PacketDiagonalHalfL1Scale
              diagonalOrder packet) *
            ExpNeg.blockAbs
              bf4KineticCrossMajorant
              (start + 1) distance) +
            (bf4PacketDiagonalHalfL1Scale
                diagonalOrder packet *
              bf4PacketDiagonalHalfL1Scale
                diagonalOrder packet) *
              ExpNeg.termAbs
                bf4KineticCrossMajorant
                (start + 1 + distance) ≤
          bf4PacketCrossSOSPartial
              diagonalOrder start packet +
            (bf4PacketDiagonalHalfL1Scale
                diagonalOrder packet *
              bf4PacketDiagonalHalfL1Scale
                diagonalOrder packet) *
              (ExpNeg.blockAbs
                  bf4KineticCrossMajorant
                  (start + 1) distance +
                ExpNeg.termAbs
                  bf4KineticCrossMajorant
                  (start + 1 + distance))
      exact Q'.le_of_eqv (by q_ring)

/-- Explicit kinetic-word cutoff modulus for one diagonal order and finite
signed packet.  The packet prefactor is paid constructively by an
`invSucc` denominator. -/
def bf4PacketCrossModulus
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') : Nat :=
  let scale :=
    bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet *
      bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  max
    (halfRatioCutoff bf4KineticCrossMajorant)
    (ExpNeg.termAbsModulus
      bf4KineticCrossMajorant
      (HalfPow.half * delta))

/-- Constructive Cauchy estimate for the grouped packet kernel as the full
kinetic-word cutoff is removed, at fixed diagonal order. -/
theorem bf4PacketCrossSOSPartial_cauchy
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm :
      bf4PacketCrossModulus
          diagonalOrder packet epsilon ≤ m)
    (hn :
      bf4PacketCrossModulus
          diagonalOrder packet epsilon ≤ n) :
    bf4PacketCrossSOSPartial diagonalOrder m packet ≤
          bf4PacketCrossSOSPartial diagonalOrder n packet +
            epsilon ∧
      bf4PacketCrossSOSPartial diagonalOrder n packet ≤
          bf4PacketCrossSOSPartial diagonalOrder m packet +
            epsilon := by
  let scale :=
    bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet *
      bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet
  let actionL1 := bf4KineticCrossMajorant
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  have hhalfScale0 :
      (0 : Q') ≤
        bf4PacketDiagonalHalfL1Scale
          diagonalOrder packet :=
    bf4PacketDiagonalHalfL1Scale_nonnegative
      diagonalOrder packet
  have hscale0 : (0 : Q') ≤ scale :=
    Q'.mul_nonneg _ _ hhalfScale0 hhalfScale0
  have haction0 : (0 : Q') ≤ actionL1 :=
    bf4KineticCrossMajorant_nonnegative
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hdeltaPos : (0 : Q') < delta :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos scale.num.toNat)
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_of_lt hdeltaPos
  have hhalfDeltaPos :
      (0 : Q') < HalfPow.half * delta :=
    ExpNeg.half_mul_pos delta hdeltaPos
  have dir :
      ∀ smaller larger : Nat,
        bf4PacketCrossModulus
            diagonalOrder packet epsilon ≤ smaller →
        smaller ≤ larger →
        bf4PacketCrossSOSPartial
              diagonalOrder larger packet ≤
            bf4PacketCrossSOSPartial
                diagonalOrder smaller packet + epsilon ∧
          bf4PacketCrossSOSPartial
              diagonalOrder smaller packet ≤
            bf4PacketCrossSOSPartial
                diagonalOrder larger packet + epsilon := by
    intro smaller larger hsmaller horder
    obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le horder
    have hcutAtSmaller :
        halfRatioCutoff actionL1 ≤ smaller :=
      Nat.le_trans
        (Nat.le_max_left _ _) hsmaller
    have hcut :
        halfRatioCutoff actionL1 ≤ smaller + 1 := by
      omega
    have hmodulusAtSmaller :
        ExpNeg.termAbsModulus
            actionL1 (HalfPow.half * delta) ≤
          smaller :=
      Nat.le_trans
        (Nat.le_max_right _ _) hsmaller
    have hterm :
        ExpNeg.termAbs actionL1 (smaller + 1) ≤
          HalfPow.half * delta :=
      ExpNeg.termAbs_le_of_modulus_le
        actionL1 (HalfPow.half * delta)
        haction0 hhalfDeltaPos (smaller + 1)
        (by omega)
    have htail :
        ExpNeg.blockAbs
            actionL1 (smaller + 1) distance ≤
          delta :=
      ExpNeg.expNeg_tail_bound
        actionL1 haction0 delta hdelta0
        (smaller + 1) hcut hterm distance
    have hscaled :
        scale *
            ExpNeg.blockAbs
              actionL1 (smaller + 1) distance ≤
          epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          htail hscale0)
        (ExpNeg.mul_le_of_mul_invSucc_toNat
          scale epsilon hscale0 hepsilon0)
    have hupper :=
      bf4PacketCrossSOSPartial_block_upper
        diagonalOrder smaller packet distance
    have hmono :=
      bf4PacketCrossSOSPartial_add_mono
        diagonalOrder smaller packet distance
    exact
      ⟨Q'.le_trans' _ _ _ hupper
        (Q'.add_le_add_left _ _ _ hscaled),
       Q'.le_trans' _ _ _ hmono
        (Q'.add_le_self_of_nonneg _ _ hepsilon0)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact
      ⟨(dir m n hm hmn).2,
       (dir m n hm hmn).1⟩
  · exact
      ⟨(dir n m hn hnm).1,
       (dir n m hn hnm).2⟩

/-- **Located grouped BF4 cross limit.**  At every fixed diagonal
Feynman--Kac order and for every finite signed physical packet, the exact
positive ten-Haar kernel has a constructive real limit as all kinetic words
are restored. -/
def bf4PacketGroupedSquareCrossLimit
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    CReal where
  approx :=
    fun crossOrder =>
      bf4PacketCrossSOSPartial
        diagonalOrder crossOrder packet
  cauchy := by
    intro epsilon hepsilon
    exact
      ⟨bf4PacketCrossModulus
          diagonalOrder packet epsilon,
       fun m n hm hn =>
        bf4PacketCrossSOSPartial_cauchy
          diagonalOrder packet epsilon hepsilon
          m n hm hn⟩

@[simp] theorem bf4PacketGroupedSquareCrossLimit_approx
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    (bf4PacketGroupedSquareCrossLimit
      diagonalOrder packet).approx crossOrder =
        bf4PacketCrossSOSPartial
          diagonalOrder crossOrder packet :=
  rfl

/-- Every approximation to the located cross limit is represented by the
literal grouped ten-holonomy polynomial at that cutoff. -/
theorem bf4PacketGroupedSquare_haar_eq_crossLimit_approx
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) ≈
      (bf4PacketGroupedSquareCrossLimit
        diagonalOrder packet).approx crossOrder :=
  bf4PacketGroupedSquare_haar_eq_crossSOSPartial
    diagonalOrder crossOrder packet

/-- Positive-semidefinite order survives the located cross limit: every
finite signed packet has a nonnegative limiting quadratic form. -/
theorem bf4PacketGroupedSquareCrossLimit_nonnegative
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    CReal.ofQ' 0 ≤
      bf4PacketGroupedSquareCrossLimit
        diagonalOrder packet := by
  apply CReal.ofQ'_le_of_approx_ge
  intro crossOrder
  exact bf4PacketCrossSOSPartial_nonnegative
    diagonalOrder crossOrder packet

end YMGap.Continuum.BF4GroupedHolonomyCrossMajorant

#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4FeatureWordsExact_word_length
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.sourceFeatureWordPolynomial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4FeatureWordMajorant_cons
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4FeatureWordMajorantSumExact_eq_termAbs
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketHalfPolynomial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketChannelLinear_abs_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketCrossExactSOS_le_factorial
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketCrossSOSPartial_block_upper
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketCrossSOSPartial_cauchy
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketGroupedSquareCrossLimit
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketGroupedSquare_haar_eq_crossLimit_approx
#print axioms YMGap.Continuum.BF4GroupedHolonomyCrossMajorant.bf4PacketGroupedSquareCrossLimit_nonnegative
