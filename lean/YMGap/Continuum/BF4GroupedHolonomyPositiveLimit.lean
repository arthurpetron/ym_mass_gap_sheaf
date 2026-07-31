/-
# Diagonal factorial control for the grouped BF4 holonomy endpoint

`BF4GroupedHolonomyCrossMajorant` removes the full kinetic-word cutoff at
each fixed diagonal Feynman--Kac order.  A joint two-parameter limit also
needs a diagonal estimate which is independent of the kinetic carrier.

This file proves that estimate at the coefficient-`L¹` level.  If `E` is
the literal positive one-sided BF4 complement and `D = ‖E‖₁`, then

  ‖E^n / n!‖₁ ≤ D^n / n!.

The parity-arranged square/square-times-`E` representative used to preserve
complete positivity is treated literally.  Consequently every omitted
diagonal block is bounded by `ExpNeg.blockAbs D`, and every finite diagonal
partial has one explicit rational upper bound.

The second half of the file closes that nonlinear obstruction.  It expands
the exact diagonal shell inside each packet half-amplitude, factors the
difference of the resulting squares, regroups every kinetic label before
estimating, and obtains diagonal and cross moduli which are uniform in the
other cutoff.  These moduli construct a joint located `CReal`; the endpoint
is independent of every explicitly cofinal two-cutoff schedule and retains
its literal grouped Haar/SOS and positivity identifications.

## Axiom gate

Finite polynomial algebra, exact `Q'` inequalities, and explicit factorial
tails only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
import YMGap.Continuum.ExpProductFloor

namespace YMGap.Continuum.BF4GroupedHolonomyPositiveLimit

set_option maxRecDepth 2000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.ExpProductFloor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
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

/-! ## 1. Literal parity-arranged diagonal moment bound -/

/-- Coefficient norm of the normalized positive one-sided complement. -/
def bf4SourceDiagonalComplementL1 : Q' :=
  polynomialCoefficientL1
    sourceDiagonalComplementPolynomial

theorem bf4SourceDiagonalComplementL1_nonnegative :
    (0 : Q') ≤ bf4SourceDiagonalComplementL1 :=
  polynomialCoefficientL1_nonnegative _

private theorem qpow_nonnegative_local
    (value : Q') (hvalue : (0 : Q') ≤ value) :
    ∀ exponent : Nat,
      (0 : Q') ≤ qpow value exponent
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | exponent + 1 =>
      Q'.mul_nonneg _ _
        (qpow_nonnegative_local value hvalue exponent)
        hvalue

/-- The CP-preserving parity representative of the `n`-th complement
moment has the same scalar exponential growth as a literal power. -/
theorem sourceDiagonalComplementMomentPolynomial_l1_le
    (exponent : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalComplementMomentPolynomial
          exponent) ≤
      qpow bf4SourceDiagonalComplementL1 exponent := by
  let d := bf4SourceDiagonalComplementL1
  let halfIndex := exponent / 2
  let factor :=
    polynomialPower
      sourceDiagonalComplementPolynomial halfIndex
  let bound := qpow d halfIndex
  have hd0 : (0 : Q') ≤ d :=
    bf4SourceDiagonalComplementL1_nonnegative
  have hfactor0 :
      (0 : Q') ≤
        polynomialCoefficientL1 factor :=
    polynomialCoefficientL1_nonnegative factor
  have hbound0 : (0 : Q') ≤ bound :=
    qpow_nonnegative_local d hd0 halfIndex
  have hfactor :
      polynomialCoefficientL1 factor ≤ bound :=
    polynomialCoefficientL1_polynomialPower_le
      sourceDiagonalComplementPolynomial halfIndex
  unfold sourceDiagonalComplementMomentPolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    have hproduct :
        polynomialCoefficientL1
            (polyMul factor factor) ≤
          bound * bound := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le factor factor)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _
            hfactor hfactor0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            hfactor hbound0))
    refine Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv ?_)
    unfold bound
    rw [← hexponent]
    exact Q'.eqv_symm
      (qpow_add d halfIndex halfIndex)
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    have hfactorSquare :
        polynomialCoefficientL1
            (polyMul factor factor) ≤
          bound * bound := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le factor factor)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _
            hfactor hfactor0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            hfactor hbound0))
    have hproduct :
        polynomialCoefficientL1
            (polyMul (polyMul factor factor)
              sourceDiagonalComplementPolynomial) ≤
          (bound * bound) * d := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le
          (polyMul factor factor)
          sourceDiagonalComplementPolynomial)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          hfactorSquare hd0)
    refine Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv ?_)
    unfold bound
    refine Q'.eqv_trans _
      (qpow d (halfIndex + halfIndex) * d) _
      (Q'.mul_eqv_congr_right _ _ d
        (Q'.eqv_symm
          (qpow_add d halfIndex halfIndex))) ?_
    have hpower :
        qpow d (halfIndex + halfIndex) * d =
          qpow d (halfIndex + halfIndex + 1) :=
      rfl
    rw [hpower, hexponent]
    exact Q'.eqv_refl _

/-- Each literal positive diagonal shell is bounded by the matching scalar
factorial term. -/
theorem sourceDiagonalShiftedTerm_l1_le
    (exponent : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalShiftedTerm exponent) ≤
      ExpNeg.termAbs
        bf4SourceDiagonalComplementL1 exponent := by
  let unitTerm := ExpNeg.termAbs 1 exponent
  let d := bf4SourceDiagonalComplementL1
  have hunit0 : (0 : Q') ≤ unitTerm :=
    ExpNeg.termAbs_nonneg 1 (by decide) exponent
  have habsUnit : Q'.abs unitTerm = unitTerm := by
    unfold Q'.abs
    rw [if_pos hunit0]
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_smul_le
      unitTerm
      (sourceDiagonalComplementMomentPolynomial
        exponent)) ?_
  rw [habsUnit]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (sourceDiagonalComplementMomentPolynomial_l1_le
        exponent)
      hunit0) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv unitTerm
        (qpow d exponent))
      (Q'.eqv_symm
        (termAbs_eq_qpow_mul_unit d exponent)))

/-! ## 2. Partial and omitted-block estimates -/

/-- The coefficient norm of the positive diagonal partial is bounded by
the scalar positive exponential partial. -/
theorem sourceDiagonalFeynmanKacPartial_l1_le :
    ∀ order : Nat,
      polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial order) ≤
        ExpNeg.partialSumAbs
          bf4SourceDiagonalComplementL1 order
  | 0 => Q'.le_refl' 0
  | order + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (sourceDiagonalFeynmanKacPartial order)
            (sourceDiagonalShiftedTerm order))) ?_
      exact Q'.add_le_add
        (sourceDiagonalFeynmanKacPartial_l1_le order)
        (sourceDiagonalShiftedTerm_l1_le order)

/-- Scalar coefficient mass of the omitted diagonal shells
`[start,start+distance)`. -/
def bf4SourceDiagonalL1Block
    (start : Nat) : Nat → Q'
  | 0 => 0
  | distance + 1 =>
      bf4SourceDiagonalL1Block start distance +
        polynomialCoefficientL1
          (sourceDiagonalShiftedTerm
            (start + distance))

/-- Every omitted diagonal block is dominated by the corresponding
factorial block. -/
theorem bf4SourceDiagonalL1Block_le
    (start : Nat) :
    ∀ distance : Nat,
      bf4SourceDiagonalL1Block start distance ≤
        ExpNeg.blockAbs
          bf4SourceDiagonalComplementL1
          start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 => by
      exact Q'.add_le_add
        (bf4SourceDiagonalL1Block_le
          start distance)
        (sourceDiagonalShiftedTerm_l1_le
          (start + distance))

/-- Explicit coefficient-`L¹` modulus for every omitted diagonal block. -/
def bf4SourceDiagonalL1Modulus
    (epsilon : Q') : Nat :=
  max
    (halfRatioCutoff bf4SourceDiagonalComplementL1)
    (ExpNeg.termAbsModulus
      bf4SourceDiagonalComplementL1
      (HalfPow.half * epsilon))

theorem bf4SourceDiagonalL1Block_le_of_modulus
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start distance : Nat)
    (hstart :
      bf4SourceDiagonalL1Modulus epsilon ≤ start) :
    bf4SourceDiagonalL1Block start distance ≤
      epsilon := by
  have hd0 :
      (0 : Q') ≤ bf4SourceDiagonalComplementL1 :=
    bf4SourceDiagonalComplementL1_nonnegative
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hhalfEpsilon :
      (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hcut :
      halfRatioCutoff bf4SourceDiagonalComplementL1 ≤
        start :=
    Nat.le_trans
      (Nat.le_max_left _ _) hstart
  have hterm :
      ExpNeg.termAbs
          bf4SourceDiagonalComplementL1 start ≤
        HalfPow.half * epsilon :=
    ExpNeg.termAbs_le_of_modulus_le
      bf4SourceDiagonalComplementL1
      (HalfPow.half * epsilon)
      hd0 hhalfEpsilon start
      (Nat.le_trans
        (Nat.le_max_right _ _) hstart)
  exact Q'.le_trans' _ _ _
    (bf4SourceDiagonalL1Block_le start distance)
    (ExpNeg.expNeg_tail_bound
      bf4SourceDiagonalComplementL1 hd0
      epsilon hepsilon0 start hcut hterm distance)

/-! ## 3. One rational bound for every diagonal partial -/

/-- The standard rational positive-exponential bound controls every finite
positive partial, not only an eventual tail. -/
theorem partialSumAbs_le_expPosBound
    (value : Q') (hvalue : (0 : Q') ≤ value)
    (order : Nat) :
    ExpNeg.partialSumAbs value order ≤
      expPosBound value := by
  let cutoff := halfRatioCutoff value
  rcases Nat.le_total order cutoff with horder | hcutoff
  · obtain ⟨distance, hdistance⟩ :=
      Nat.exists_eq_add_of_le horder
    have hmono :
        ExpNeg.partialSumAbs value order ≤
          ExpNeg.partialSumAbs value cutoff := by
      rw [hdistance]
      exact ExpPos.partialSumAbs_mono
        value hvalue order distance
    refine Q'.le_trans' _ _ _ hmono ?_
    unfold expPosBound cutoff
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.zero_le_add _ _
        (ExpNeg.termAbs_nonneg value hvalue
          (halfRatioCutoff value))
        (ExpNeg.termAbs_nonneg value hvalue
          (halfRatioCutoff value)))
  · obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le hcutoff
    have hterm0 :
        (0 : Q') ≤
          ExpNeg.termAbs value cutoff :=
      ExpNeg.termAbs_nonneg value hvalue cutoff
    have htail :
        ExpNeg.blockAbs value cutoff distance ≤
          ExpNeg.termAbs value cutoff +
            ExpNeg.termAbs value cutoff := by
      have hpair0 :
          (0 : Q') ≤
            ExpNeg.termAbs value cutoff +
              ExpNeg.termAbs value cutoff :=
        Q'.zero_le_add _ _ hterm0 hterm0
      have hhalfPair :
          HalfPow.half *
              (ExpNeg.termAbs value cutoff +
                ExpNeg.termAbs value cutoff) ≈
            ExpNeg.termAbs value cutoff :=
        Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv HalfPow.half
            (ExpNeg.termAbs value cutoff)
            (ExpNeg.termAbs value cutoff))
          (ExpNeg.two_halves
            (ExpNeg.termAbs value cutoff))
      exact ExpNeg.blockAbs_le
        value HalfPow.half
        (ExpNeg.termAbs value cutoff +
          ExpNeg.termAbs value cutoff)
        hvalue cutoff HalfPow.half_nonneg hpair0
        (ExpNeg.x_invSucc_le_half
          value hvalue cutoff (Nat.le_refl _))
        (ExpNeg.expNeg_recurrence value cutoff
          (ExpNeg.termAbs value cutoff +
            ExpNeg.termAbs value cutoff)
          (Q'.ge_of_eqv hhalfPair))
        distance
    exact Q'.le_trans' _ _ _
      (ExpPos.partialSumAbs_le_add_blockAbs
        value cutoff distance)
      (Q'.add_le_add_left _ _ _ htail)

/-- Uniform rational coefficient-norm bound for every positive diagonal
Feynman--Kac partial. -/
theorem sourceDiagonalFeynmanKacPartial_l1_uniform
    (order : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalFeynmanKacPartial order) ≤
      expPosBound bf4SourceDiagonalComplementL1 := by
  exact Q'.le_trans' _ _ _
    (sourceDiagonalFeynmanKacPartial_l1_le order)
    (partialSumAbs_le_expPosBound
      bf4SourceDiagonalComplementL1
      bf4SourceDiagonalComplementL1_nonnegative
      order)

/-! ## 4. Exact diagonal-shell decomposition on packet half-amplitudes -/

/-- Literal polynomial containing exactly the diagonal shells with indices
`[start,start+distance)`. -/
def bf4SourceDiagonalBlockPolynomial
    (start : Nat) : Nat → RatPoly
  | 0 => polyZero
  | distance + 1 =>
      polyAdd
        (bf4SourceDiagonalBlockPolynomial start distance)
        (sourceDiagonalShiftedTerm
          (start + distance))

/-- A later positive diagonal partial is the earlier partial plus its
literal omitted block. -/
theorem sourceDiagonalFeynmanKacPartial_add_block
    (start : Nat) :
    ∀ distance : Nat,
      sourceDiagonalFeynmanKacPartial
          (start + distance) =
        polyAdd
          (sourceDiagonalFeynmanKacPartial start)
          (bf4SourceDiagonalBlockPolynomial
            start distance)
  | 0 => by
      simp [polyAdd, polyZero,
        bf4SourceDiagonalBlockPolynomial]
  | distance + 1 => by
      change
        polyAdd
            (sourceDiagonalFeynmanKacPartial
              (start + distance))
            (sourceDiagonalShiftedTerm
              (start + distance)) =
          polyAdd
            (sourceDiagonalFeynmanKacPartial start)
            (polyAdd
              (bf4SourceDiagonalBlockPolynomial
                start distance)
              (sourceDiagonalShiftedTerm
                (start + distance)))
      rw [sourceDiagonalFeynmanKacPartial_add_block
        start distance]
      exact List.append_assoc _ _ _

/-- The coefficient norm of the literal diagonal block is bounded by the
scalar shell-mass block defined above. -/
theorem bf4SourceDiagonalBlockPolynomial_l1_le
    (start : Nat) :
    ∀ distance : Nat,
      polynomialCoefficientL1
          (bf4SourceDiagonalBlockPolynomial
            start distance) ≤
        bf4SourceDiagonalL1Block start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (bf4SourceDiagonalBlockPolynomial
              start distance)
            (sourceDiagonalShiftedTerm
              (start + distance)))) ?_
      exact Q'.add_le_add
        (bf4SourceDiagonalBlockPolynomial_l1_le
          start distance)
        (Q'.le_refl' _)

/-- One five-Haar half-amplitude with an arbitrary diagonal insertion. -/
def bf4DiagonalInsertionHalfAmplitude
    (diagonal : RatPoly)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) : Q' :=
  quaternionHaar 5
    (polyMul
      (polyMul
        (sourceMehlerWavefunction state)
        diagonal)
      (sourceFeatureWordPolynomial word))

@[simp] theorem bf4DiagonalInsertionHalfAmplitude_partial
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    bf4DiagonalInsertionHalfAmplitude
        (sourceDiagonalFeynmanKacPartial
          diagonalOrder)
        state word =
      bf4MehlerHalfAmplitude
        diagonalOrder state word :=
  rfl

private theorem polyMul_add_left_exact
    (left right third : RatPoly) :
    polyMul (polyAdd left right) third =
      polyAdd
        (polyMul left third)
        (polyMul right third) := by
  simp [polyAdd, polyMul]

/-- Exact Haar linearity in the inserted diagonal polynomial. -/
theorem bf4DiagonalInsertionHalfAmplitude_add
    (left right : RatPoly)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    bf4DiagonalInsertionHalfAmplitude
        (polyAdd left right) state word ≈
      bf4DiagonalInsertionHalfAmplitude
          left state word +
        bf4DiagonalInsertionHalfAmplitude
          right state word := by
  let wave := sourceMehlerWavefunction state
  let featureWord := sourceFeatureWordPolynomial word
  unfold bf4DiagonalInsertionHalfAmplitude
  refine Q'.eqv_trans _
    (quaternionHaar 5
      (polyMul wave
        (polyMul (polyAdd left right)
          featureWord))) _
    (quaternionHaar_polyMul_assoc
      5 wave (polyAdd left right) featureWord) ?_
  rw [polyMul_add_left_exact]
  refine Q'.eqv_trans _
    (quaternionHaar 5
        (polyMul wave
          (polyMul left featureWord)) +
      quaternionHaar 5
        (polyMul wave
          (polyMul right featureWord))) _
    (quaternionHaar_polyMul_add_right
      5 wave
      (polyMul left featureWord)
      (polyMul right featureWord)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        5 wave left featureWord))
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        5 wave right featureWord))

/-- Coefficient norm bounds one arbitrary-insertion half-amplitude. -/
theorem bf4DiagonalInsertionHalfAmplitude_abs_le
    (diagonal : RatPoly)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4DiagonalInsertionHalfAmplitude
          diagonal state word) ≤
      (polynomialCoefficientL1
          (sourceMehlerWavefunction state) *
        polynomialCoefficientL1 diagonal) *
      bf4FeatureWordPolynomialL1Product word := by
  let wave := sourceMehlerWavefunction state
  let featureWord := sourceFeatureWordPolynomial word
  have hfirst :
      polynomialCoefficientL1
          (polyMul wave diagonal) ≤
        polynomialCoefficientL1 wave *
          polynomialCoefficientL1 diagonal :=
    polynomialCoefficientL1_mul_le wave diagonal
  have hword :
      polynomialCoefficientL1 featureWord ≤
        bf4FeatureWordPolynomialL1Product word :=
    sourceFeatureWordPolynomial_l1_le word
  have hfirst0 :
      (0 : Q') ≤
        polynomialCoefficientL1
          (polyMul wave diagonal) :=
    polynomialCoefficientL1_nonnegative _
  have hwordProduct0 :
      (0 : Q') ≤
        bf4FeatureWordPolynomialL1Product word :=
    bf4FeatureWordPolynomialL1Product_nonnegative
      word
  unfold bf4DiagonalInsertionHalfAmplitude
  exact Q'.le_trans' _ _ _
    (quaternionHaar_abs_le_coefficientL1
      5 (polyMul (polyMul wave diagonal)
        featureWord))
    (Q'.le_trans' _ _ _
      (polynomialCoefficientL1_mul_le
        (polyMul wave diagonal) featureWord)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          hword hfirst0)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          hfirst hwordProduct0)))

/-- Boundary-wave coefficient scale of a finite signed packet, before any
diagonal or kinetic insertion. -/
def bf4PacketWaveL1Scale
    (packet : BF4HolonomyStatePacket) : Q' :=
  listQSum
    (fun weightedState =>
      Q'.abs weightedState.1 *
        polynomialCoefficientL1
          (sourceMehlerWavefunction
            weightedState.2))
    packet

theorem bf4PacketWaveL1Scale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ bf4PacketWaveL1Scale packet := by
  unfold bf4PacketWaveL1Scale
  apply listQSum_nonnegative_on
  intro weightedState _
  exact Q'.mul_nonneg _ _
    (Q'.abs_nonneg weightedState.1)
    (polynomialCoefficientL1_nonnegative _)

/-- Signed packet linear form with an arbitrary diagonal insertion. -/
def bf4PacketDiagonalInsertionLinear
    (diagonal : RatPoly)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : Q' :=
  listQSum
    (fun weightedState =>
      weightedState.1 *
        bf4DiagonalInsertionHalfAmplitude
          diagonal weightedState.2 word)
    packet

@[simp] theorem bf4PacketDiagonalInsertionLinear_partial
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    bf4PacketDiagonalInsertionLinear
        (sourceDiagonalFeynmanKacPartial
          diagonalOrder)
        packet word =
      bf4PacketChannelLinear
        diagonalOrder packet word :=
  rfl

/-- Packet-level arbitrary-insertion bound. -/
theorem bf4PacketDiagonalInsertionLinear_abs_le
    (diagonal : RatPoly)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4PacketDiagonalInsertionLinear
          diagonal packet word) ≤
      bf4PacketWaveL1Scale packet *
        (polynomialCoefficientL1 diagonal *
          bf4FeatureWordPolynomialL1Product word) := by
  induction packet with
  | nil =>
      unfold bf4PacketDiagonalInsertionLinear
        bf4PacketWaveL1Scale listQSum
      unfold Q'.abs
      rw [if_pos (Q'.le_refl' 0)]
      exact Q'.mul_nonneg _ _
        (Q'.le_refl' 0)
        (Q'.mul_nonneg _ _
          (polynomialCoefficientL1_nonnegative
            diagonal)
          (bf4FeatureWordPolynomialL1Product_nonnegative
            word))
  | cons weightedState rest induction =>
      let diagonalL1 :=
        polynomialCoefficientL1 diagonal
      let wordProduct :=
        bf4FeatureWordPolynomialL1Product word
      let headBase :=
        Q'.abs weightedState.1 *
          polynomialCoefficientL1
            (sourceMehlerWavefunction
              weightedState.2)
      let factor := diagonalL1 * wordProduct
      have hhead :
          Q'.abs
              (weightedState.1 *
                bf4DiagonalInsertionHalfAmplitude
                  diagonal weightedState.2 word) ≤
            headBase * factor := by
        refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le
            weightedState.1
            (bf4DiagonalInsertionHalfAmplitude
              diagonal weightedState.2 word)) ?_
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (bf4DiagonalInsertionHalfAmplitude_abs_le
              diagonal weightedState.2 word)
            (Q'.abs_nonneg weightedState.1)) ?_
        exact Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (Q'.abs weightedState.1) _ _
              (Q'.mul_assoc_eqv
                (polynomialCoefficientL1
                  (sourceMehlerWavefunction
                    weightedState.2))
                diagonalL1 wordProduct))
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (Q'.abs weightedState.1)
                (polynomialCoefficientL1
                  (sourceMehlerWavefunction
                    weightedState.2))
                factor)))
      unfold bf4PacketDiagonalInsertionLinear
        bf4PacketWaveL1Scale listQSum
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (weightedState.1 *
            bf4DiagonalInsertionHalfAmplitude
              diagonal weightedState.2 word)
          (bf4PacketDiagonalInsertionLinear
            diagonal rest word)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead induction) ?_
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (q_add_mul
            headBase
            (bf4PacketWaveL1Scale rest)
            factor))

/-- The existing diagonal packet scale is controlled by the wave scale
times the diagonal coefficient norm. -/
theorem bf4PacketDiagonalHalfL1Scale_le
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet ≤
      bf4PacketWaveL1Scale packet *
        polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial
            diagonalOrder) := by
  unfold bf4PacketDiagonalHalfL1Scale
    bf4PacketWaveL1Scale
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (listQSum
          (fun weightedState =>
            (Q'.abs weightedState.1 *
              polynomialCoefficientL1
                (sourceMehlerWavefunction
                  weightedState.2)) *
            polynomialCoefficientL1
              (sourceDiagonalFeynmanKacPartial
                diagonalOrder))
          packet) _
      (listQSum_congr
        (fun weightedState =>
          Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (Q'.abs weightedState.1)
              (polynomialCoefficientL1
                (sourceMehlerWavefunction
                  weightedState.2))
              (polynomialCoefficientL1
                (sourceDiagonalFeynmanKacPartial
                  diagonalOrder))))
        packet)
      (listQSum_mul_right
        (fun weightedState =>
          Q'.abs weightedState.1 *
            polynomialCoefficientL1
              (sourceMehlerWavefunction
                weightedState.2))
        (polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial
            diagonalOrder))
        packet))

/-- Packet linearity in an arbitrary diagonal insertion.  This is the
exact finite-packet bridge from the additive polynomial shell to the
nonlinear SOS comparison below. -/
theorem bf4PacketDiagonalInsertionLinear_add
    (left right : RatPoly)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    bf4PacketDiagonalInsertionLinear
        (polyAdd left right) packet word ≈
      bf4PacketDiagonalInsertionLinear
          left packet word +
        bf4PacketDiagonalInsertionLinear
          right packet word := by
  unfold bf4PacketDiagonalInsertionLinear
  refine Q'.eqv_trans _
    (listQSum
      (fun weightedState =>
        weightedState.1 *
            bf4DiagonalInsertionHalfAmplitude
              left weightedState.2 word +
          weightedState.1 *
            bf4DiagonalInsertionHalfAmplitude
              right weightedState.2 word)
      packet) _ ?_ ?_
  · apply listQSum_congr
    intro weightedState
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left weightedState.1 _ _
        (bf4DiagonalInsertionHalfAmplitude_add
          left right weightedState.2 word))
      (Q'.mul_add_eqv
        weightedState.1
        (bf4DiagonalInsertionHalfAmplitude
          left weightedState.2 word)
        (bf4DiagonalInsertionHalfAmplitude
          right weightedState.2 word))
  · exact listQSum_add _ _ packet

/-- The literal packet contribution of a finite diagonal shell. -/
def bf4PacketDiagonalBlockLinear
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : Q' :=
  bf4PacketDiagonalInsertionLinear
    (bf4SourceDiagonalBlockPolynomial start distance)
    packet word

/-- Exact channel decomposition under an increase of diagonal cutoff. -/
theorem bf4PacketChannelLinear_add_block
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    bf4PacketChannelLinear
        (start + distance) packet word ≈
      bf4PacketChannelLinear start packet word +
        bf4PacketDiagonalBlockLinear
          start distance packet word := by
  change
    bf4PacketDiagonalInsertionLinear
        (sourceDiagonalFeynmanKacPartial
          (start + distance)) packet word ≈
      bf4PacketDiagonalInsertionLinear
          (sourceDiagonalFeynmanKacPartial start)
          packet word +
        bf4PacketDiagonalInsertionLinear
          (bf4SourceDiagonalBlockPolynomial
            start distance) packet word
  rw [sourceDiagonalFeynmanKacPartial_add_block]
  exact bf4PacketDiagonalInsertionLinear_add
    (sourceDiagonalFeynmanKacPartial start)
    (bf4SourceDiagonalBlockPolynomial start distance)
    packet word

/-- One rational packet scale which controls every diagonal cutoff. -/
def bf4PacketUniformHalfL1Scale
    (packet : BF4HolonomyStatePacket) : Q' :=
  bf4PacketWaveL1Scale packet *
    expPosBound bf4SourceDiagonalComplementL1

theorem bf4PacketUniformHalfL1Scale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketUniformHalfL1Scale packet :=
  Q'.mul_nonneg _ _
    (bf4PacketWaveL1Scale_nonnegative packet)
    (Q'.le_of_lt
      (expPosBound_pos
        bf4SourceDiagonalComplementL1
        bf4SourceDiagonalComplementL1_nonnegative))

/-- Every diagonal packet norm lies below the same cutoff-independent
scale. -/
theorem bf4PacketDiagonalHalfL1Scale_le_uniform
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketDiagonalHalfL1Scale
        diagonalOrder packet ≤
      bf4PacketUniformHalfL1Scale packet := by
  exact Q'.le_trans' _ _ _
    (bf4PacketDiagonalHalfL1Scale_le
      diagonalOrder packet)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (sourceDiagonalFeynmanKacPartial_l1_uniform
        diagonalOrder)
      (bf4PacketWaveL1Scale_nonnegative packet))

/-- The actual packet channel is uniformly bounded at every diagonal
cutoff. -/
theorem bf4PacketChannelLinear_abs_le_uniform
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4PacketChannelLinear
          diagonalOrder packet word) ≤
      bf4PacketUniformHalfL1Scale packet *
        bf4FeatureWordPolynomialL1Product word := by
  exact Q'.le_trans' _ _ _
    (bf4PacketChannelLinear_abs_le
      diagonalOrder packet word)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (bf4PacketDiagonalHalfL1Scale_le_uniform
        diagonalOrder packet)
      (bf4FeatureWordPolynomialL1Product_nonnegative
        word))

/-- A packet shell insertion is paid by its literal coefficient norm. -/
theorem bf4PacketDiagonalBlockLinear_abs_le
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4PacketDiagonalBlockLinear
          start distance packet word) ≤
      (bf4PacketWaveL1Scale packet *
        polynomialCoefficientL1
          (bf4SourceDiagonalBlockPolynomial
            start distance)) *
        bf4FeatureWordPolynomialL1Product word := by
  exact Q'.le_trans' _ _ _
    (bf4PacketDiagonalInsertionLinear_abs_le
      (bf4SourceDiagonalBlockPolynomial
        start distance)
      packet word)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (bf4PacketWaveL1Scale packet)
          (polynomialCoefficientL1
            (bf4SourceDiagonalBlockPolynomial
              start distance))
          (bf4FeatureWordPolynomialL1Product
            word))))

/-! ## 5. Nonlinear shell control before the all-label sum -/

/-- Additive cancellation in the exact arrangement generated by expanding
a difference of squares. -/
private theorem add_reassoc_cancel_local
    (outer middle residual : Q') :
    (outer + middle) + ((-middle) + residual) ≈
      outer + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      outer middle ((-middle) + residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left outer _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          middle (-middle) residual))) ?_
  have hcancel :
      middle + (-middle) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv middle (-middle))
      (Q'.neg_add_self_eqv middle)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left outer _ _
      (Q'.add_eqv_congr_right
        (middle + (-middle)) 0 residual
        hcancel)) ?_
  exact Q'.add_eqv_congr_left outer _ _
    (QPoly.q_zero_add_eqv residual)

/-- Cancellation of the earlier summand after substituting an additive
increment. -/
private theorem add_increment_neg_base_local
    (base increment : Q') :
    (base + increment) + (-base) ≈ increment := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      base increment (-base)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left base _ _
      (Q'.add_comm_eqv increment (-base))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv
        base (-base) increment)) ?_
  have hcancel :
      base + (-base) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv base (-base))
      (Q'.neg_add_self_eqv base)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (base + (-base)) 0 increment
      hcancel) ?_
  exact QPoly.q_zero_add_eqv increment

/-- Difference-of-squares bound in the constructive rational setoid.  The
increment is supplied by an exact additive decomposition, not subtraction
or decidable equality of reduced rationals. -/
private theorem abs_square_sub_le_of_add
    (earlier later increment : Q')
    (hadd : later ≈ earlier + increment) :
    Q'.abs
        (later * later + (-(earlier * earlier))) ≤
      Q'.abs increment *
        (Q'.abs later + Q'.abs earlier) := by
  have hfactor :
      later * later + (-(earlier * earlier)) ≈
        (later + (-earlier)) *
          (later + earlier) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv
        later (-earlier) (later + earlier)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_add_eqv later later earlier)
        (Q'.mul_add_eqv
          (-earlier) later earlier)) ?_
    have hnegativeCross :
        (-earlier) * later ≈
          -(later * earlier) :=
      Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv earlier later)
        (Q'.neg_eqv_congr
          (earlier * later)
          (later * earlier)
          (Q'.mul_comm_eqv earlier later))
    have hnegativeSquare :
        (-earlier) * earlier ≈
          -(earlier * earlier) :=
      Q'.neg_mul_eqv earlier earlier
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_refl
          (later * later +
            later * earlier))
        (Q'.add_eqv_congr'
          hnegativeCross hnegativeSquare)) ?_
    exact add_reassoc_cancel_local
      (later * later)
      (later * earlier)
      (-(earlier * earlier))
  have hincrement :
      later + (-earlier) ≈ increment := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        later (earlier + increment)
        (-earlier) hadd)
      (add_increment_neg_base_local
        earlier increment)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr hfactor)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le
      (later + (-earlier))
      (later + earlier)) ?_
  exact Q'.mul_le_mul_of_nonneg
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr hincrement))
    (ExpNeg.abs_add_le later earlier)
    (Q'.abs_nonneg increment)
    (Q'.abs_nonneg (later + earlier))

/-- Uniform scalar paid by a diagonal shell before the word majorant. -/
def bf4PacketDiagonalWordErrorScale
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  (bf4PacketWaveL1Scale packet *
    polynomialCoefficientL1
      (bf4SourceDiagonalBlockPolynomial
        start distance)) *
    (bf4PacketUniformHalfL1Scale packet +
      bf4PacketUniformHalfL1Scale packet)

theorem bf4PacketDiagonalWordErrorScale_nonnegative
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketDiagonalWordErrorScale
        start distance packet := by
  unfold bf4PacketDiagonalWordErrorScale
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (bf4PacketWaveL1Scale_nonnegative packet)
      (polynomialCoefficientL1_nonnegative _))
    (Q'.zero_le_add _ _
      (bf4PacketUniformHalfL1Scale_nonnegative packet)
      (bf4PacketUniformHalfL1Scale_nonnegative packet))

/-- Pointwise nonlinear estimate: the change of one complete positive word
channel is bounded by its all-label majorant times the diagonal shell
scale. -/
theorem bf4PacketWordSOS_diagonal_block_abs_le
    (start distance : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    Q'.abs
        (bf4PacketWordSOS
            (start + distance) packet word +
          (-bf4PacketWordSOS
            start packet word)) ≤
      bf4PacketDiagonalWordErrorScale
          start distance packet *
        bf4FeatureWordMajorant word := by
  let earlier :=
    bf4PacketChannelLinear start packet word
  let later :=
    bf4PacketChannelLinear
      (start + distance) packet word
  let increment :=
    bf4PacketDiagonalBlockLinear
      start distance packet word
  let waveScale := bf4PacketWaveL1Scale packet
  let blockL1 :=
    polynomialCoefficientL1
      (bf4SourceDiagonalBlockPolynomial
        start distance)
  let shellScale := waveScale * blockL1
  let uniform :=
    bf4PacketUniformHalfL1Scale packet
  let product :=
    bf4FeatureWordPolynomialL1Product word
  let weight := bf4FeatureWordWeight word
  have hdecompose : later ≈ earlier + increment :=
    bf4PacketChannelLinear_add_block
      start distance packet word
  have hincrement :
      Q'.abs increment ≤ shellScale * product :=
    bf4PacketDiagonalBlockLinear_abs_le
      start distance packet word
  have hearlier :
      Q'.abs earlier ≤ uniform * product :=
    bf4PacketChannelLinear_abs_le_uniform
      start packet word
  have hlater :
      Q'.abs later ≤ uniform * product :=
    bf4PacketChannelLinear_abs_le_uniform
      (start + distance) packet word
  have hshell0 : (0 : Q') ≤ shellScale :=
    Q'.mul_nonneg _ _
      (bf4PacketWaveL1Scale_nonnegative packet)
      (polynomialCoefficientL1_nonnegative _)
  have hproduct0 : (0 : Q') ≤ product :=
    bf4FeatureWordPolynomialL1Product_nonnegative word
  have huniform0 : (0 : Q') ≤ uniform :=
    bf4PacketUniformHalfL1Scale_nonnegative packet
  have hsquare :
      Q'.abs
          (later * later +
            (-(earlier * earlier))) ≤
        (shellScale * product) *
          ((uniform * product) +
            (uniform * product)) := by
    refine Q'.le_trans' _ _ _
      (abs_square_sub_le_of_add
        earlier later increment hdecompose) ?_
    exact Q'.mul_le_mul_of_nonneg
      hincrement
      (Q'.add_le_add hlater hearlier)
      (Q'.mul_nonneg _ _ hshell0 hproduct0)
      (Q'.zero_le_add _ _
        (Q'.abs_nonneg later)
        (Q'.abs_nonneg earlier))
  have hweightFactor :
      weight * (later * later) +
          (-(weight * (earlier * earlier))) ≈
        weight *
          (later * later +
            (-(earlier * earlier))) := by
    q_ring
  unfold bf4PacketWordSOS
  change
    Q'.abs
        (weight * (later * later) +
          (-(weight * (earlier * earlier)))) ≤
      bf4PacketDiagonalWordErrorScale
          start distance packet *
        (weight * (product * product))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr hweightFactor)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le
      weight
      (later * later +
        (-(earlier * earlier)))) ?_
  rw [ExpNeg.abs_of_nonneg
    (bf4FeatureWordWeight_nonnegative word)]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hsquare
      (bf4FeatureWordWeight_nonnegative word)) ?_
  unfold bf4PacketDiagonalWordErrorScale
  dsimp [shellScale, waveScale, blockL1,
    uniform, product, weight]
  exact Q'.le_of_eqv (by ring_qeqv)

/-! ## 6. Simultaneous summation of every retained word label -/

/-- Scalar majorant mass of every word through the displayed kinetic
cutoff. -/
def bf4FeatureWordMajorantSumAtMost
    (crossOrder : Nat) : Q' :=
  listQSum bf4FeatureWordMajorant
    (bf4FeatureWordsAtMost crossOrder)

/-- The all-word majorant through cutoff `c` is exactly the positive
exponential partial through order `c+1`. -/
theorem bf4FeatureWordMajorantSumAtMost_eq_partialSumAbs :
    ∀ crossOrder : Nat,
      bf4FeatureWordMajorantSumAtMost crossOrder ≈
        ExpNeg.partialSumAbs
          bf4KineticCrossMajorant
          (crossOrder + 1)
  | 0 => by
      change
        bf4FeatureWordMajorantSumExact 0 ≈
          ExpNeg.partialSumAbs
            bf4KineticCrossMajorant 1
      exact bf4FeatureWordMajorantSumExact_eq_termAbs 0
  | crossOrder + 1 => by
      change
        listQSum bf4FeatureWordMajorant
            (bf4FeatureWordsAtMost crossOrder ++
              bf4FeatureWordsExact
                (crossOrder + 1)) ≈
          ExpNeg.partialSumAbs
            bf4KineticCrossMajorant
            (crossOrder + 2)
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          bf4FeatureWordMajorant
          (bf4FeatureWordsAtMost crossOrder)
          (bf4FeatureWordsExact
            (crossOrder + 1))) ?_
      change
        bf4FeatureWordMajorantSumAtMost crossOrder +
            bf4FeatureWordMajorantSumExact
              (crossOrder + 1) ≈
          ExpNeg.partialSumAbs
              bf4KineticCrossMajorant
              (crossOrder + 1) +
            ExpNeg.termAbs
              bf4KineticCrossMajorant
              (crossOrder + 1)
      exact Q'.add_eqv_congr'
        (bf4FeatureWordMajorantSumAtMost_eq_partialSumAbs
          crossOrder)
        (bf4FeatureWordMajorantSumExact_eq_termAbs
          (crossOrder + 1))

/-- A single rational exponential bound controls the total majorant mass
at every kinetic cutoff. -/
theorem bf4FeatureWordMajorantSumAtMost_le_uniform
    (crossOrder : Nat) :
    bf4FeatureWordMajorantSumAtMost crossOrder ≤
      expPosBound bf4KineticCrossMajorant := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (bf4FeatureWordMajorantSumAtMost_eq_partialSumAbs
        crossOrder))
    (partialSumAbs_le_expPosBound
      bf4KineticCrossMajorant
      bf4KineticCrossMajorant_nonnegative
      (crossOrder + 1))

/-- **Quantitative all-label nonlinear diagonal bound.**  The word cutoff
has disappeared from the right-hand side: every retained source/target
label is regrouped before the diagonal shell is estimated. -/
theorem bf4PacketCrossSOSPartial_diagonal_block_abs_le
    (start distance crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    Q'.abs
        (bf4PacketCrossSOSPartial
            (start + distance) crossOrder packet +
          (-bf4PacketCrossSOSPartial
            start crossOrder packet)) ≤
      bf4PacketDiagonalWordErrorScale
          start distance packet *
        expPosBound bf4KineticCrossMajorant := by
  let errorScale :=
    bf4PacketDiagonalWordErrorScale
      start distance packet
  unfold bf4PacketCrossSOSPartial
  refine Q'.le_trans' _ _ _
    (abs_listQSum_sub_le
      (bf4PacketWordSOS
        (start + distance) packet)
      (bf4PacketWordSOS start packet)
      (bf4FeatureWordsAtMost crossOrder)) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun word =>
        Q'.abs
          (bf4PacketWordSOS
              (start + distance) packet word +
            (-bf4PacketWordSOS
              start packet word)))
      (fun word =>
        errorScale *
          bf4FeatureWordMajorant word)
      (bf4FeatureWordsAtMost crossOrder)
      (fun word _ =>
        bf4PacketWordSOS_diagonal_block_abs_le
          start distance packet word)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_mul_left
        errorScale
        bf4FeatureWordMajorant
        (bf4FeatureWordsAtMost crossOrder))) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (bf4FeatureWordMajorantSumAtMost_le_uniform
      crossOrder)
    (bf4PacketDiagonalWordErrorScale_nonnegative
      start distance packet)

/-! ## 7. A diagonal modulus uniform in the kinetic cutoff -/

/-- Cutoff-independent scalar multiplying the omitted diagonal shell
mass. -/
def bf4PacketDiagonalCauchyScale
    (packet : BF4HolonomyStatePacket) : Q' :=
  (bf4PacketWaveL1Scale packet *
    (bf4PacketUniformHalfL1Scale packet +
      bf4PacketUniformHalfL1Scale packet)) *
    expPosBound bf4KineticCrossMajorant

theorem bf4PacketDiagonalCauchyScale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤
      bf4PacketDiagonalCauchyScale packet := by
  unfold bf4PacketDiagonalCauchyScale
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (bf4PacketWaveL1Scale_nonnegative packet)
      (Q'.zero_le_add _ _
        (bf4PacketUniformHalfL1Scale_nonnegative packet)
        (bf4PacketUniformHalfL1Scale_nonnegative packet)))
    (Q'.le_of_lt
      (expPosBound_pos
        bf4KineticCrossMajorant
        bf4KineticCrossMajorant_nonnegative))

/-- Four-factor reassociation used to place a scalar tail mass at the far
right without expanding any concrete BF4 coefficient definitions. -/
private theorem mul_four_swap_second_last
    (first second third fourth : Q') :
    ((first * second) * third) * fourth ≈
      ((first * third) * fourth) * second := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ fourth
      (Q'.mul_assoc_eqv first second third)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ fourth
      (Q'.mul_eqv_congr_left first _ _
        (Q'.mul_comm_eqv second third))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ fourth
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          first third second))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (first * third) second fourth) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (first * third) _ _
      (Q'.mul_comm_eqv second fourth)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv
      (first * third) fourth second)

/-- The all-label nonlinear change is the universal packet coefficient
times the scalar omitted diagonal mass. -/
theorem bf4PacketCrossSOSPartial_diagonal_block_abs_le_scaled
    (start distance crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    Q'.abs
        (bf4PacketCrossSOSPartial
            (start + distance) crossOrder packet +
          (-bf4PacketCrossSOSPartial
            start crossOrder packet)) ≤
      bf4PacketDiagonalCauchyScale packet *
        bf4SourceDiagonalL1Block start distance := by
  let wave := bf4PacketWaveL1Scale packet
  let uniform := bf4PacketUniformHalfL1Scale packet
  let polynomialBlock :=
    polynomialCoefficientL1
      (bf4SourceDiagonalBlockPolynomial
        start distance)
  let scalarBlock :=
    bf4SourceDiagonalL1Block start distance
  let crossBound :=
    expPosBound bf4KineticCrossMajorant
  have hwave0 : (0 : Q') ≤ wave :=
    bf4PacketWaveL1Scale_nonnegative packet
  have huniformSum0 :
      (0 : Q') ≤ uniform + uniform :=
    Q'.zero_le_add _ _
      (bf4PacketUniformHalfL1Scale_nonnegative packet)
      (bf4PacketUniformHalfL1Scale_nonnegative packet)
  have hcross0 : (0 : Q') ≤ crossBound :=
    Q'.le_of_lt
      (expPosBound_pos
        bf4KineticCrossMajorant
        bf4KineticCrossMajorant_nonnegative)
  have hblock :
      polynomialBlock ≤ scalarBlock :=
    bf4SourceDiagonalBlockPolynomial_l1_le
      start distance
  have herrorScale :
      bf4PacketDiagonalWordErrorScale
          start distance packet ≤
        (wave * scalarBlock) *
          (uniform + uniform) := by
    unfold bf4PacketDiagonalWordErrorScale
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hblock hwave0)
      huniformSum0
  refine Q'.le_trans' _ _ _
    (bf4PacketCrossSOSPartial_diagonal_block_abs_le
      start distance crossOrder packet) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      herrorScale hcross0) ?_
  change
    ((wave * scalarBlock) *
        (uniform + uniform)) * crossBound ≤
      ((wave * (uniform + uniform)) *
        crossBound) * scalarBlock
  exact Q'.le_of_eqv
    (mul_four_swap_second_last
      wave scalarBlock
      (uniform + uniform) crossBound)

/-- Explicit diagonal Cauchy modulus after paying the complete nonlinear
packet/carrier coefficient with one constructive reciprocal. -/
def bf4PacketDiagonalModulus
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') : Nat :=
  let scale :=
    bf4PacketDiagonalCauchyScale packet
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  bf4SourceDiagonalL1Modulus delta

/-- Absolute diagonal convergence estimate, uniform in the kinetic-word
cutoff. -/
theorem bf4PacketCrossSOSPartial_diagonal_abs_le_of_modulus
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start distance crossOrder : Nat)
    (hstart :
      bf4PacketDiagonalModulus
          packet epsilon ≤ start) :
    Q'.abs
        (bf4PacketCrossSOSPartial
            (start + distance) crossOrder packet +
          (-bf4PacketCrossSOSPartial
            start crossOrder packet)) ≤
      epsilon := by
  let scale :=
    bf4PacketDiagonalCauchyScale packet
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  have hscale0 : (0 : Q') ≤ scale :=
    bf4PacketDiagonalCauchyScale_nonnegative packet
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hdeltaPos : (0 : Q') < delta :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos scale.num.toNat)
  have hblock :
      bf4SourceDiagonalL1Block
          start distance ≤ delta :=
    bf4SourceDiagonalL1Block_le_of_modulus
      delta hdeltaPos start distance hstart
  refine Q'.le_trans' _ _ _
    (bf4PacketCrossSOSPartial_diagonal_block_abs_le_scaled
      start distance crossOrder packet) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hblock hscale0) ?_
  exact ExpNeg.mul_le_of_mul_invSucc_toNat
    scale epsilon hscale0 hepsilon0

/-- Two-sided diagonal Cauchy estimate, simultaneously valid at every
kinetic cutoff. -/
theorem bf4PacketCrossSOSPartial_diagonal_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (crossOrder m n : Nat)
    (hm :
      bf4PacketDiagonalModulus
          packet epsilon ≤ m)
    (hn :
      bf4PacketDiagonalModulus
          packet epsilon ≤ n) :
    bf4PacketCrossSOSPartial m crossOrder packet ≤
          bf4PacketCrossSOSPartial n crossOrder packet +
            epsilon ∧
      bf4PacketCrossSOSPartial n crossOrder packet ≤
          bf4PacketCrossSOSPartial m crossOrder packet +
            epsilon := by
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le hmn
    have habs :=
      bf4PacketCrossSOSPartial_diagonal_abs_le_of_modulus
        packet epsilon hepsilon
        m distance crossOrder hm
    exact
      ⟨ExpNeg.le_add_of_abs_sub_le
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (Q'.eqv_symm
                (ExpNeg.abs_sub_comm
                  (bf4PacketCrossSOSPartial
                    (m + distance) crossOrder packet)
                  (bf4PacketCrossSOSPartial
                    m crossOrder packet))))
            habs),
       ExpNeg.le_add_of_abs_sub_le habs⟩
  · obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le hnm
    have habs :=
      bf4PacketCrossSOSPartial_diagonal_abs_le_of_modulus
        packet epsilon hepsilon
        n distance crossOrder hn
    exact
      ⟨ExpNeg.le_add_of_abs_sub_le habs,
       ExpNeg.le_add_of_abs_sub_le
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (Q'.eqv_symm
                (ExpNeg.abs_sub_comm
                  (bf4PacketCrossSOSPartial
                    (n + distance) crossOrder packet)
                  (bf4PacketCrossSOSPartial
                    n crossOrder packet))))
            habs)⟩

/-! ## 8. One cross-word modulus for every diagonal cutoff -/

/-- Nonnegativity of a finite positive factorial block. -/
private theorem blockAbs_nonnegative_local
    (value : Q') (hvalue : (0 : Q') ≤ value)
    (start : Nat) :
    ∀ distance : Nat,
      (0 : Q') ≤
        ExpNeg.blockAbs value start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 =>
      Q'.zero_le_add _ _
        (blockAbs_nonnegative_local
          value hvalue start distance)
        (ExpNeg.termAbs_nonneg
          value hvalue (start + distance))

/-- The exact all-word shell estimate with the diagonal cutoff removed
from its prefactor. -/
theorem bf4PacketCrossExactSOS_le_factorial_uniform
    (diagonalOrder length : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketCrossExactSOS
        diagonalOrder length packet ≤
      (bf4PacketUniformHalfL1Scale packet *
        bf4PacketUniformHalfL1Scale packet) *
      ExpNeg.termAbs
        bf4KineticCrossMajorant length := by
  let diagonalScale :=
    bf4PacketDiagonalHalfL1Scale
      diagonalOrder packet
  let uniform :=
    bf4PacketUniformHalfL1Scale packet
  have hscale :
      diagonalScale ≤ uniform :=
    bf4PacketDiagonalHalfL1Scale_le_uniform
      diagonalOrder packet
  have hdiagonal0 : (0 : Q') ≤ diagonalScale :=
    bf4PacketDiagonalHalfL1Scale_nonnegative
      diagonalOrder packet
  have huniform0 : (0 : Q') ≤ uniform :=
    bf4PacketUniformHalfL1Scale_nonnegative packet
  have hsquare :
      diagonalScale * diagonalScale ≤
        uniform * uniform :=
    Q'.mul_le_mul_of_nonneg
      hscale hscale huniform0 hdiagonal0
  exact Q'.le_trans' _ _ _
    (bf4PacketCrossExactSOS_le_factorial
      diagonalOrder length packet)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      hsquare
      (ExpNeg.termAbs_nonneg
        bf4KineticCrossMajorant
        bf4KineticCrossMajorant_nonnegative
        length))

/-- Uniform version of the complete cross-cutoff block bound. -/
theorem bf4PacketCrossSOSPartial_block_upper_uniform
    (diagonalOrder start distance : Nat)
    (packet : BF4HolonomyStatePacket) :
    bf4PacketCrossSOSPartial
        diagonalOrder (start + distance) packet ≤
      bf4PacketCrossSOSPartial
          diagonalOrder start packet +
        (bf4PacketUniformHalfL1Scale packet *
          bf4PacketUniformHalfL1Scale packet) *
          ExpNeg.blockAbs
            bf4KineticCrossMajorant
            (start + 1) distance := by
  let diagonalScale :=
    bf4PacketDiagonalHalfL1Scale
      diagonalOrder packet
  let uniform :=
    bf4PacketUniformHalfL1Scale packet
  let tail :=
    ExpNeg.blockAbs
      bf4KineticCrossMajorant
      (start + 1) distance
  have hscale :
      diagonalScale ≤ uniform :=
    bf4PacketDiagonalHalfL1Scale_le_uniform
      diagonalOrder packet
  have hdiagonal0 : (0 : Q') ≤ diagonalScale :=
    bf4PacketDiagonalHalfL1Scale_nonnegative
      diagonalOrder packet
  have huniform0 : (0 : Q') ≤ uniform :=
    bf4PacketUniformHalfL1Scale_nonnegative packet
  have hsquare :
      diagonalScale * diagonalScale ≤
        uniform * uniform :=
    Q'.mul_le_mul_of_nonneg
      hscale hscale huniform0 hdiagonal0
  have htail0 : (0 : Q') ≤ tail :=
    blockAbs_nonnegative_local
      bf4KineticCrossMajorant
      bf4KineticCrossMajorant_nonnegative
      (start + 1) distance
  refine Q'.le_trans' _ _ _
    (bf4PacketCrossSOSPartial_block_upper
      diagonalOrder start packet distance) ?_
  exact Q'.add_le_add_left _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      hsquare htail0)

/-- Cross-word cutoff modulus valid simultaneously for all diagonal
Feynman--Kac orders. -/
def bf4PacketUniformCrossModulus
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') : Nat :=
  let scale :=
    bf4PacketUniformHalfL1Scale packet *
      bf4PacketUniformHalfL1Scale packet
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  max
    (halfRatioCutoff bf4KineticCrossMajorant)
    (ExpNeg.termAbsModulus
      bf4KineticCrossMajorant
      (HalfPow.half * delta))

/-- Two-sided cross-word Cauchy estimate with no dependence on the
diagonal cutoff. -/
theorem bf4PacketCrossSOSPartial_uniform_cross_cauchy
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm :
      bf4PacketUniformCrossModulus
          packet epsilon ≤ m)
    (hn :
      bf4PacketUniformCrossModulus
          packet epsilon ≤ n) :
    bf4PacketCrossSOSPartial diagonalOrder m packet ≤
          bf4PacketCrossSOSPartial diagonalOrder n packet +
            epsilon ∧
      bf4PacketCrossSOSPartial diagonalOrder n packet ≤
          bf4PacketCrossSOSPartial diagonalOrder m packet +
            epsilon := by
  let uniform :=
    bf4PacketUniformHalfL1Scale packet
  let scale := uniform * uniform
  let actionL1 := bf4KineticCrossMajorant
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  have huniform0 : (0 : Q') ≤ uniform :=
    bf4PacketUniformHalfL1Scale_nonnegative packet
  have hscale0 : (0 : Q') ≤ scale :=
    Q'.mul_nonneg _ _ huniform0 huniform0
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
        bf4PacketUniformCrossModulus
            packet epsilon ≤ smaller →
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
      bf4PacketCrossSOSPartial_block_upper_uniform
        diagonalOrder smaller distance packet
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

/-! ## 9. Joint cofinal limit and schedule independence -/

/-- Two half-tolerance comparisons compose to one full-tolerance
comparison. -/
private theorem le_add_halves_trans
    (first middle last epsilon : Q')
    (hfirst :
      first ≤ middle + HalfPow.half * epsilon)
    (hlast :
      middle ≤ last + HalfPow.half * epsilon) :
    first ≤ last + epsilon := by
  refine Q'.le_trans' _ _ _ hfirst ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right
      middle
      (last + HalfPow.half * epsilon)
      (HalfPow.half * epsilon)
      hlast) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        last
        (HalfPow.half * epsilon)
        (HalfPow.half * epsilon))
      (Q'.add_eqv_congr_left last _ _
        (ExpNeg.two_halves epsilon)))

/-- Common modulus for changing both diagonal and kinetic-word cutoffs. -/
def bf4PacketJointModulus
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') : Nat :=
  max
    (bf4PacketDiagonalModulus
      packet (HalfPow.half * epsilon))
    (bf4PacketUniformCrossModulus
      packet (HalfPow.half * epsilon))

/-- Full two-parameter Cauchy estimate.  Both endpoints may use unrelated
diagonal and cross cutoffs; only common cofinality is required. -/
theorem bf4PacketCrossSOSPartial_joint_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (diagonal₁ cross₁ diagonal₂ cross₂ : Nat)
    (hdiagonal₁ :
      bf4PacketJointModulus packet epsilon ≤ diagonal₁)
    (hcross₁ :
      bf4PacketJointModulus packet epsilon ≤ cross₁)
    (hdiagonal₂ :
      bf4PacketJointModulus packet epsilon ≤ diagonal₂)
    (hcross₂ :
      bf4PacketJointModulus packet epsilon ≤ cross₂) :
    bf4PacketCrossSOSPartial
        diagonal₁ cross₁ packet ≤
          bf4PacketCrossSOSPartial
              diagonal₂ cross₂ packet + epsilon ∧
      bf4PacketCrossSOSPartial
        diagonal₂ cross₂ packet ≤
          bf4PacketCrossSOSPartial
              diagonal₁ cross₁ packet + epsilon := by
  let halfEpsilon := HalfPow.half * epsilon
  have hhalfPositive : (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hdiagonalMod₁ :
      bf4PacketDiagonalModulus
          packet halfEpsilon ≤ diagonal₁ :=
    Nat.le_trans
      (Nat.le_max_left _ _) hdiagonal₁
  have hdiagonalMod₂ :
      bf4PacketDiagonalModulus
          packet halfEpsilon ≤ diagonal₂ :=
    Nat.le_trans
      (Nat.le_max_left _ _) hdiagonal₂
  have hcrossMod₁ :
      bf4PacketUniformCrossModulus
          packet halfEpsilon ≤ cross₁ :=
    Nat.le_trans
      (Nat.le_max_right _ _) hcross₁
  have hcrossMod₂ :
      bf4PacketUniformCrossModulus
          packet halfEpsilon ≤ cross₂ :=
    Nat.le_trans
      (Nat.le_max_right _ _) hcross₂
  have hdiagonal :=
    bf4PacketCrossSOSPartial_diagonal_cauchy
      packet halfEpsilon hhalfPositive cross₁
      diagonal₁ diagonal₂
      hdiagonalMod₁ hdiagonalMod₂
  have hcross :=
    bf4PacketCrossSOSPartial_uniform_cross_cauchy
      diagonal₂ packet halfEpsilon hhalfPositive
      cross₁ cross₂ hcrossMod₁ hcrossMod₂
  exact
    ⟨le_add_halves_trans
        (bf4PacketCrossSOSPartial
          diagonal₁ cross₁ packet)
        (bf4PacketCrossSOSPartial
          diagonal₂ cross₁ packet)
        (bf4PacketCrossSOSPartial
          diagonal₂ cross₂ packet)
        epsilon hdiagonal.1 hcross.1,
     le_add_halves_trans
        (bf4PacketCrossSOSPartial
          diagonal₂ cross₂ packet)
        (bf4PacketCrossSOSPartial
          diagonal₂ cross₁ packet)
        (bf4PacketCrossSOSPartial
          diagonal₁ cross₁ packet)
        epsilon hcross.2 hdiagonal.2⟩

/-- Diagonal cofinal approximation `(d,c)=(n,n)`. -/
def bf4PacketJointSOSPartial
    (packet : BF4HolonomyStatePacket)
    (stage : Nat) : Q' :=
  bf4PacketCrossSOSPartial stage stage packet

/-- **Located joint grouped BF4 limit.**  Both the positive diagonal
Feynman--Kac expansion and the complete kinetic-word expansion have now
been removed in one constructive real. -/
def bf4PacketGroupedSquareJointLimit
    (packet : BF4HolonomyStatePacket) :
    CReal where
  approx := bf4PacketJointSOSPartial packet
  cauchy := by
    intro epsilon hepsilon
    refine
      ⟨bf4PacketJointModulus packet epsilon,
       fun m n hm hn => ?_⟩
    exact bf4PacketCrossSOSPartial_joint_cauchy
      packet epsilon hepsilon
      m m n n hm hm hn hn

@[simp] theorem bf4PacketGroupedSquareJointLimit_approx
    (packet : BF4HolonomyStatePacket)
    (stage : Nat) :
    (bf4PacketGroupedSquareJointLimit packet).approx stage =
      bf4PacketCrossSOSPartial stage stage packet :=
  rfl

/-- A constructive pair of cofinal cutoff schedules. -/
structure BF4GroupedCofinalSchedule where
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  diagonal_cofinal :
    ∀ stage, stage ≤ diagonalOrder stage
  cross_cofinal :
    ∀ stage, stage ≤ crossOrder stage

/-- The grouped BF4 limit along an arbitrary explicitly cofinal schedule. -/
def bf4PacketGroupedSquareScheduledLimit
    (schedule : BF4GroupedCofinalSchedule)
    (packet : BF4HolonomyStatePacket) :
    CReal where
  approx :=
    fun stage =>
      bf4PacketCrossSOSPartial
        (schedule.diagonalOrder stage)
        (schedule.crossOrder stage)
        packet
  cauchy := by
    intro epsilon hepsilon
    refine
      ⟨bf4PacketJointModulus packet epsilon,
       fun m n hm hn => ?_⟩
    exact bf4PacketCrossSOSPartial_joint_cauchy
      packet epsilon hepsilon
      (schedule.diagonalOrder m)
      (schedule.crossOrder m)
      (schedule.diagonalOrder n)
      (schedule.crossOrder n)
      (Nat.le_trans hm
        (schedule.diagonal_cofinal m))
      (Nat.le_trans hm
        (schedule.cross_cofinal m))
      (Nat.le_trans hn
        (schedule.diagonal_cofinal n))
      (Nat.le_trans hn
        (schedule.cross_cofinal n))

/-- Cofinal schedules cannot change the resulting joint endpoint. -/
theorem bf4PacketGroupedSquareScheduledLimit_equiv_joint
    (schedule : BF4GroupedCofinalSchedule)
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (bf4PacketGroupedSquareScheduledLimit
        schedule packet)
      (bf4PacketGroupedSquareJointLimit packet) := by
  intro epsilon hepsilon
  refine
    ⟨bf4PacketJointModulus packet epsilon,
     fun stage hstage => ?_⟩
  exact bf4PacketCrossSOSPartial_joint_cauchy
    packet epsilon hepsilon
    (schedule.diagonalOrder stage)
    (schedule.crossOrder stage)
    stage stage
    (Nat.le_trans hstage
      (schedule.diagonal_cofinal stage))
    (Nat.le_trans hstage
      (schedule.cross_cofinal stage))
    hstage hstage

/-- Every approximation to the joint endpoint is still the literal grouped
ten-Haar contraction at the matching two cutoffs. -/
theorem bf4PacketGroupedSquare_haar_eq_jointLimit_approx
    (packet : BF4HolonomyStatePacket)
    (stage : Nat) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          stage stage packet) ≈
      (bf4PacketGroupedSquareJointLimit
        packet).approx stage :=
  bf4PacketGroupedSquare_haar_eq_crossSOSPartial
    stage stage packet

/-- Complete positivity survives simultaneous removal of both cutoffs. -/
theorem bf4PacketGroupedSquareJointLimit_nonnegative
    (packet : BF4HolonomyStatePacket) :
    CReal.ofQ' 0 ≤
      bf4PacketGroupedSquareJointLimit packet := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact bf4PacketCrossSOSPartial_nonnegative
    stage stage packet

end YMGap.Continuum.BF4GroupedHolonomyPositiveLimit

#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalFeynmanKacPartial_add_block
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4DiagonalInsertionHalfAmplitude_add
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketDiagonalInsertionLinear_abs_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketChannelLinear_add_block
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketWordSOS_diagonal_block_abs_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketCrossSOSPartial_diagonal_block_abs_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketCrossSOSPartial_diagonal_cauchy
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketCrossSOSPartial_uniform_cross_cauchy
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketCrossSOSPartial_joint_cauchy
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketGroupedSquareJointLimit
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketGroupedSquareScheduledLimit_equiv_joint
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketGroupedSquare_haar_eq_jointLimit_approx
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4PacketGroupedSquareJointLimit_nonnegative
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalComplementMomentPolynomial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalShiftedTerm_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalFeynmanKacPartial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4SourceDiagonalL1Block_le_of_modulus
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalFeynmanKacPartial_l1_uniform
