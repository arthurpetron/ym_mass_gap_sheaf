/-
# Arbitrary-orientation cutoff-one positive channels

The local cutoff-one Haar dispatcher retains the literal orientation of every
fundamental occurrence.  The existing positive operator kernels, by contrast,
use the balanced conventions `F R`, `F R F R`, and `F F F R R R`.  This leaf
connects the two descriptions without enumerating Boolean assignments.

For valence two we first prove a missing structural normalization theorem by
raw fundamental pseudoreality and partial-Haar functoriality.  At valences four
and six the corresponding normalization is already part of the dispatcher.
In all three cases the normalized matrix indices are packaged in semantic
operator coordinates and the balanced kernel is replaced by its exact positive
channel resolution.  The only sign left outside the positive resolution is the
single accumulated epsilon sign already present in the honest Haar kernel.

The final section compiles the same occurrence-orientation masks to symbolic
Boolean-tensor wirings.  It proves that the transported bivalent, four-valent,
and six-valent channel tensors retain their exact Gram norms.  Thus arbitrary
orientation changes the channel vectors by a certified signed isometry; it
does not change any positive inverse-Gram weight or local trace mass.

This is a local `N3` theorem.  It does not claim that the plaquette contraction
is a coordinate permutation.  `N4` must instead compile the exact endpoint
factor-incidence graph and apply the degree-two graphical Cauchy--Finner
bound; the cap/cup pattern rules out a single global dot-product wiring.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOccurrenceBoolTensorTransport
import YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor
import YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher

namespace YMGap.Continuum.SU2QuaternionCutoffOneOrientedPositiveChannels

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization
open YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
open YMGap.Continuum.SU2QuaternionFourValentOperatorKernel
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge
open YMGap.Continuum.SU2QuaternionSixValentOperatorKernel
open YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor
open YMGap.Continuum.SU2QuaternionOccurrenceBoolTensorTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Structural bivalent normalization -/

/-- Epsilon parity for forcing the first bivalent occurrence forward and the
second reverse. -/
def orientedBivalentNormalizationNegative
    (first second : FundamentalOccurrence) : Bool :=
  signXor (forwardNormalizationNegative first)
    (reverseNormalizationNegative second)

/-- The orientation-normalized bivalent Haar kernel, retaining the exact
epsilon sign of the literal two-occurrence word. -/
def orientedBivalentNormalizedHaarKernel
    (first second : FundamentalOccurrence) : RationalComplex :=
  signedRationalComplex
    (orientedBivalentNormalizationNegative first second)
    (orientedBivalentHaarKernel first.toForward second.toReverse)

/-- A literal arbitrary bivalent word is raw-equal to its signed `F R`
normal form.  Only the two coefficient factors are inspected. -/
theorem orientedBivalentFundamentalTerm_eq_signed_normalized
    (block : Nat) (first second : FundamentalOccurrence) :
    orientedBivalentFundamentalTerm block first second =
      signedComplexRatPoly
        (orientedBivalentNormalizationNegative first second)
        (orientedBivalentFundamentalTerm block
          first.toForward second.toReverse) := by
  unfold orientedBivalentFundamentalTerm
    orientedBivalentNormalizationNegative
  rw [fundamentalOccurrenceCoefficient_eq_signed_toForward block first,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block second,
    signedComplexRatPoly_mul]

/-- The total arbitrary-orientation bivalent Haar kernel is exactly its signed
balanced normal form.  The proof passes through the already verified partial
Haar theorem, so no Boolean coordinate family is split. -/
theorem orientedBivalentHaarKernel_eqv_signed_normalized
    (first second : FundamentalOccurrence) :
    RationalComplexEqv
      (orientedBivalentHaarKernel first second)
      (orientedBivalentNormalizedHaarKernel first second) := by
  unfold orientedBivalentNormalizedHaarKernel
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (integrated_orientedBivalentFundamentalTerm_projector
        0 first second)) ?_
  rw [orientedBivalentFundamentalTerm_eq_signed_normalized]
  refine rationalComplexEqv_trans
    (integratedComplexCoefficientSum_signed 0
      (orientedBivalentNormalizationNegative first second)
      (orientedBivalentFundamentalTerm 0
        first.toForward second.toReverse)) ?_
  exact signedRationalComplex_congr _
    (integrated_orientedBivalentFundamentalTerm_projector
      0 first.toForward second.toReverse)

/-! ## 2. Normalized semantic operator coordinates -/

/-- Semantic target after forward normalization is the stored forward row. -/
theorem normalizeOccurrence_forward_operatorTarget
    (occurrence : FundamentalOccurrence) :
    (normalizeOccurrence .forward occurrence).operatorTarget =
      occurrence.toForward.row := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- Semantic source after forward normalization is the stored forward
column. -/
theorem normalizeOccurrence_forward_operatorSource
    (occurrence : FundamentalOccurrence) :
    (normalizeOccurrence .forward occurrence).operatorSource =
      occurrence.toForward.column := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- Semantic target after reverse normalization is the stored reverse
column, because reverse coefficients store the transpose. -/
theorem normalizeOccurrence_reverse_operatorTarget
    (occurrence : FundamentalOccurrence) :
    (normalizeOccurrence .reverse occurrence).operatorTarget =
      occurrence.toReverse.column := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- Semantic source after reverse normalization is the stored reverse row. -/
theorem normalizeOccurrence_reverse_operatorSource
    (occurrence : FundamentalOccurrence) :
    (normalizeOccurrence .reverse occurrence).operatorSource =
      occurrence.toReverse.row := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- Target operator coordinate of an arbitrary bivalent word after forcing
its occurrence pattern to `F R`. -/
def orientedBivalentTargetIndex
    (first second : FundamentalOccurrence) : BivalentOperatorIndex :=
  ⟨(normalizeOccurrence .forward first).operatorTarget,
    (normalizeOccurrence .reverse second).operatorTarget⟩

/-- Source operator coordinate of the same normalized bivalent word. -/
def orientedBivalentSourceIndex
    (first second : FundamentalOccurrence) : BivalentOperatorIndex :=
  ⟨(normalizeOccurrence .forward first).operatorSource,
    (normalizeOccurrence .reverse second).operatorSource⟩

/-- The balanced kernel selected by the normalized occurrences is
definitionally the packaged bivalent operator kernel.  Only the two
orientation constructors are split; their Boolean indices remain symbolic. -/
theorem orientedBivalentBalancedKernel_eq_operatorKernel
    (first second : FundamentalOccurrence) :
    orientedBivalentHaarKernel first.toForward second.toReverse =
      bivalentOperatorKernelAt .forward
        (orientedBivalentTargetIndex first second)
        (orientedBivalentSourceIndex first second) := by
  unfold orientedBivalentTargetIndex orientedBivalentSourceIndex
  simp only [normalizeOccurrence_forward_operatorTarget,
    normalizeOccurrence_reverse_operatorTarget,
    normalizeOccurrence_forward_operatorSource,
    normalizeOccurrence_reverse_operatorSource]
  rcases first with ⟨firstOrientation, firstRow, firstColumn⟩
  rcases second with ⟨secondOrientation, secondRow, secondColumn⟩
  cases firstOrientation <;> cases secondOrientation <;> rfl

/-- Target two-leg operator coordinate of an arbitrary four-word after the
literal-position normalization `F R F R`. -/
def orientedFourTargetIndex
    (first second third fourth : FundamentalOccurrence) :
    TwoLegOperatorIndex where
  firstOutput := (normalizeOccurrence .forward first).operatorTarget
  firstInput := (normalizeOccurrence .reverse second).operatorTarget
  secondOutput := (normalizeOccurrence .forward third).operatorTarget
  secondInput := (normalizeOccurrence .reverse fourth).operatorTarget

/-- Source two-leg operator coordinate of the normalized four-word. -/
def orientedFourSourceIndex
    (first second third fourth : FundamentalOccurrence) :
    TwoLegOperatorIndex where
  firstOutput := (normalizeOccurrence .forward first).operatorSource
  firstInput := (normalizeOccurrence .reverse second).operatorSource
  secondOutput := (normalizeOccurrence .forward third).operatorSource
  secondInput := (normalizeOccurrence .reverse fourth).operatorSource

/-- The normalized fourth-moment entry is exactly the packaged balanced
four-valent operator kernel at the preceding semantic indices. -/
theorem orientedFourBalancedKernel_eq_operatorKernel
    (first second third fourth : FundamentalOccurrence) :
    orientedFourFundamentalHaarProjector
        first.toForward.row first.toForward.column
        third.toForward.row third.toForward.column
        second.toReverse.row second.toReverse.column
        fourth.toReverse.row fourth.toReverse.column =
      fourValentOperatorKernel
        (orientedFourTargetIndex first second third fourth)
        (orientedFourSourceIndex first second third fourth) := by
  unfold orientedFourTargetIndex orientedFourSourceIndex
  simp only [normalizeOccurrence_forward_operatorTarget,
    normalizeOccurrence_reverse_operatorTarget,
    normalizeOccurrence_forward_operatorSource,
    normalizeOccurrence_reverse_operatorSource]
  rfl

/-- Target three-leg operator coordinate of an arbitrary six-word after the
canonical normalization `F F F R R R`. -/
def orientedSixTargetIndex
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    ThreeLegOperatorIndex where
  firstOutput := (normalizeOccurrence .forward first).operatorTarget
  firstInput := (normalizeOccurrence .reverse fourth).operatorTarget
  secondOutput := (normalizeOccurrence .forward second).operatorTarget
  secondInput := (normalizeOccurrence .reverse fifth).operatorTarget
  thirdOutput := (normalizeOccurrence .forward third).operatorTarget
  thirdInput := (normalizeOccurrence .reverse sixth).operatorTarget

/-- Source three-leg operator coordinate of the normalized six-word. -/
def orientedSixSourceIndex
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    ThreeLegOperatorIndex where
  firstOutput := (normalizeOccurrence .forward first).operatorSource
  firstInput := (normalizeOccurrence .reverse fourth).operatorSource
  secondOutput := (normalizeOccurrence .forward second).operatorSource
  secondInput := (normalizeOccurrence .reverse fifth).operatorSource
  thirdOutput := (normalizeOccurrence .forward third).operatorSource
  thirdInput := (normalizeOccurrence .reverse sixth).operatorSource

/-- The normalized sixth-moment entry is exactly the packaged balanced
six-valent operator kernel. -/
theorem orientedSixBalancedKernel_eq_operatorKernel
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    orientedSixFundamentalHaarProjector
        first.toForward.row first.toForward.column
        second.toForward.row second.toForward.column
        third.toForward.row third.toForward.column
        fourth.toReverse.row fourth.toReverse.column
        fifth.toReverse.row fifth.toReverse.column
        sixth.toReverse.row sixth.toReverse.column =
      balancedSixValentOperatorKernel
        (orientedSixTargetIndex first second third fourth fifth sixth)
        (orientedSixSourceIndex first second third fourth fifth sixth) := by
  unfold orientedSixTargetIndex orientedSixSourceIndex
  simp only [normalizeOccurrence_forward_operatorTarget,
    normalizeOccurrence_reverse_operatorTarget,
    normalizeOccurrence_forward_operatorSource,
    normalizeOccurrence_reverse_operatorSource]
  rfl

/-! ## 3. Positive resolutions for all arbitrary even words -/

/-- The positive scalar-channel resolution selected by an arbitrary bivalent
word, with its honest accumulated epsilon sign retained outside. -/
def orientedBivalentPositiveChannelKernel
    (first second : FundamentalOccurrence) : RationalComplex :=
  signedRationalComplex
    (orientedBivalentNormalizationNegative first second)
    (bivalentOperatorPositiveChannelKernel
      (orientedBivalentTargetIndex first second)
      (orientedBivalentSourceIndex first second))

/-- Exact arbitrary-orientation bivalent positive-channel resolution. -/
theorem orientedBivalentHaarKernel_eqv_positiveChannel
    (first second : FundamentalOccurrence) :
    RationalComplexEqv
      (orientedBivalentHaarKernel first second)
      (orientedBivalentPositiveChannelKernel first second) := by
  refine rationalComplexEqv_trans
    (orientedBivalentHaarKernel_eqv_signed_normalized first second) ?_
  unfold orientedBivalentNormalizedHaarKernel
    orientedBivalentPositiveChannelKernel
  rw [orientedBivalentBalancedKernel_eq_operatorKernel]
  exact signedRationalComplex_congr _
    (bivalentOperatorKernelAt_eqv_positiveChannel .forward
      (orientedBivalentTargetIndex first second)
      (orientedBivalentSourceIndex first second))

/-- The positive singlet/triplet resolution selected by an arbitrary
four-word, retaining the exact epsilon parity of its literal orientations. -/
def orientedFourPositiveChannelKernel
    (first second third fourth : FundamentalOccurrence) : RationalComplex :=
  signedRationalComplex
    (orientedFourNormalizationNegative first second third fourth)
    (fourValentOperatorPositiveChannelKernel
      (orientedFourTargetIndex first second third fourth)
      (orientedFourSourceIndex first second third fourth))

/-- Exact arbitrary-orientation four-valent positive-channel resolution. -/
theorem orientedFourNormalizedHaarProjector_eqv_positiveChannel
    (first second third fourth : FundamentalOccurrence) :
    RationalComplexEqv
      (orientedFourNormalizedHaarProjector first second third fourth)
      (orientedFourPositiveChannelKernel first second third fourth) := by
  unfold orientedFourNormalizedHaarProjector
    orientedFourPositiveChannelKernel
  rw [orientedFourBalancedKernel_eq_operatorKernel]
  exact signedRationalComplex_congr _
    (fourValentOperatorKernel_eqv_positiveChannel
      (orientedFourTargetIndex first second third fourth)
      (orientedFourSourceIndex first second third fourth))

/-- The five positive Temperley--Lieb channels selected by an arbitrary
six-word, again retaining only its exact accumulated epsilon parity. -/
def orientedSixPositiveChannelKernel
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    RationalComplex :=
  signedRationalComplex
    (orientedSixNormalizationNegative
      first second third fourth fifth sixth)
    (balancedSixValentOperatorTLPositive
      (orientedSixTargetIndex first second third fourth fifth sixth)
      (orientedSixSourceIndex first second third fourth fifth sixth))

/-- Exact arbitrary-orientation six-valent positive-channel resolution. -/
theorem orientedSixNormalizedHaarProjector_eqv_positiveChannel
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    RationalComplexEqv
      (orientedSixNormalizedHaarProjector
        first second third fourth fifth sixth)
      (orientedSixPositiveChannelKernel
        first second third fourth fifth sixth) := by
  unfold orientedSixNormalizedHaarProjector
    orientedSixPositiveChannelKernel
  rw [orientedSixBalancedKernel_eq_operatorKernel]
  exact signedRationalComplex_congr _
    (balancedSixValentOperatorKernel_eqv_positive
      (orientedSixTargetIndex first second third fourth fifth sixth)
      (orientedSixSourceIndex first second third fourth fifth sixth))

/-- One total orientation-aware positive-channel value for all seven cutoff-
one local valences.  Odd words retain their exact zero and the empty word its
normalized unit. -/
def cutoffOneOrientedPositiveChannelKernel :
    CutoffOneHaarWord → RationalComplex
  | .v0 => rationalComplexOne
  | .v1 _ => rationalComplexZero
  | .v2 first second =>
      orientedBivalentPositiveChannelKernel first second
  | .v3 _ _ _ => rationalComplexZero
  | .v4 first second third fourth =>
      orientedFourPositiveChannelKernel first second third fourth
  | .v5 _ _ _ _ _ => rationalComplexZero
  | .v6 first second third fourth fifth sixth =>
      orientedSixPositiveChannelKernel
        first second third fourth fifth sixth

/-- **Total local `N3` resolution.**  Every honest cutoff-one Haar kernel is
exactly its orientation-transported positive-channel resolution. -/
theorem cutoffOneHaarKernel_eqv_orientedPositiveChannels
    (word : CutoffOneHaarWord) :
    RationalComplexEqv
      (cutoffOneHaarKernel word)
      (cutoffOneOrientedPositiveChannelKernel word) := by
  cases word with
  | v0 => exact rationalComplexEqv_refl _
  | v1 first => exact rationalComplexEqv_refl _
  | v2 first second =>
      exact orientedBivalentHaarKernel_eqv_positiveChannel first second
  | v3 first second third => exact rationalComplexEqv_refl _
  | v4 first second third fourth =>
      exact orientedFourNormalizedHaarProjector_eqv_positiveChannel
        first second third fourth
  | v5 first second third fourth fifth =>
      exact rationalComplexEqv_refl _
  | v6 first second third fourth fifth sixth =>
      exact orientedSixNormalizedHaarProjector_eqv_positiveChannel
        first second third fourth fifth sixth

/-! ## 4. The same orientation transports as certified Gram isometries -/

/-- One desired balanced orientation paired with the literal occurrence that
must be transported to it. -/
abbrev OrientationTransportEntry :=
  FundamentalLinkOrientation × FundamentalOccurrence

/-- Coordinatewise mismatch mask of a list of orientation transports. -/
def orientationTransportMask :
    List OrientationTransportEntry → List Bool
  | [] => []
  | (desired, occurrence) :: entries =>
      orientationMismatch desired occurrence.orientation ::
        orientationTransportMask entries

/-- Raw semantic target word, in the same order as the transport list. -/
def orientationTransportTargetBits :
    List OrientationTransportEntry → List Bool
  | [] => []
  | (_, occurrence) :: entries =>
      occurrence.operatorTarget :: orientationTransportTargetBits entries

/-- Raw semantic source word, in the same order as the transport list. -/
def orientationTransportSourceBits :
    List OrientationTransportEntry → List Bool
  | [] => []
  | (_, occurrence) :: entries =>
      occurrence.operatorSource :: orientationTransportSourceBits entries

/-- Exact-shape target word carried by an orientation-transport list.  Its
index is definitionally the mask length, so downstream tensor evaluation
requires no equality transport. -/
def orientationTransportTargetWord :
    (entries : List OrientationTransportEntry) →
      BoolWord (orientationTransportMask entries).length
  | [] => ()
  | (_, occurrence) :: entries =>
      (occurrence.operatorTarget, orientationTransportTargetWord entries)

/-- Exact-shape source word carried by the same transport list. -/
def orientationTransportSourceWord :
    (entries : List OrientationTransportEntry) →
      BoolWord (orientationTransportMask entries).length
  | [] => ()
  | (_, occurrence) :: entries =>
      (occurrence.operatorSource, orientationTransportSourceWord entries)

/-- Forgetting the exact-shape target word recovers the semantic target
coordinate list. -/
theorem orientationTransportTargetWord_toList :
    ∀ entries : List OrientationTransportEntry,
      BoolWord.toList (orientationTransportMask entries).length
          (orientationTransportTargetWord entries) =
        orientationTransportTargetBits entries
  | [] => rfl
  | (_, occurrence) :: entries => by
      change occurrence.operatorTarget ::
          BoolWord.toList (orientationTransportMask entries).length
            (orientationTransportTargetWord entries) =
        occurrence.operatorTarget :: orientationTransportTargetBits entries
      rw [orientationTransportTargetWord_toList entries]

/-- Forgetting the exact-shape source word recovers the semantic source
coordinate list. -/
theorem orientationTransportSourceWord_toList :
    ∀ entries : List OrientationTransportEntry,
      BoolWord.toList (orientationTransportMask entries).length
          (orientationTransportSourceWord entries) =
        orientationTransportSourceBits entries
  | [] => rfl
  | (_, occurrence) :: entries => by
      change occurrence.operatorSource ::
          BoolWord.toList (orientationTransportMask entries).length
            (orientationTransportSourceWord entries) =
        occurrence.operatorSource :: orientationTransportSourceBits entries
      rw [orientationTransportSourceWord_toList entries]

/-- Target word after each occurrence has been normalized to its desired
balanced orientation. -/
def orientationTransportNormalizedTargetBits :
    List OrientationTransportEntry → List Bool
  | [] => []
  | (desired, occurrence) :: entries =>
      (normalizeOccurrence desired occurrence).operatorTarget ::
        orientationTransportNormalizedTargetBits entries

/-- Source word after the same occurrencewise normalization. -/
def orientationTransportNormalizedSourceBits :
    List OrientationTransportEntry → List Bool
  | [] => []
  | (desired, occurrence) :: entries =>
      (normalizeOccurrence desired occurrence).operatorSource ::
        orientationTransportNormalizedSourceBits entries

/-- The Boolean sign parity accumulated by a list of occurrence
normalizations. -/
def orientationTransportParity :
    List OrientationTransportEntry → Bool
  | [] => false
  | (desired, occurrence) :: entries =>
      signXor
        (match desired with
          | .forward => forwardNormalizationNegative occurrence
          | .reverse => reverseNormalizationNegative occurrence)
        (orientationTransportParity entries)

/-- Product of the exact rational pseudoreality signs attached to a list of
occurrence normalizations. -/
def orientationTransportSignProduct :
    List OrientationTransportEntry → Q'
  | [] => 1
  | (desired, occurrence) :: entries =>
      occurrenceNormalizationSign desired occurrence *
        orientationTransportSignProduct entries

/-- Rational representative of one accumulated Boolean sign. -/
def rationalOrientationSign : Bool → Q'
  | false => 1
  | true => -1

private theorem q_mul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Rational signs turn Boolean exclusive-or into multiplication. -/
theorem rationalOrientationSign_signXor (left right : Bool) :
    rationalOrientationSign (signXor left right) ≈
      rationalOrientationSign left * rationalOrientationSign right := by
  cases left <;> cases right <;> decide

/-- The Boolean sign stored by the raw normalizer represents exactly the
rational sign stored by the occurrence epsilon transport.  Only one
occurrence is inspected, independently of every other link leg. -/
theorem rationalOrientationSign_occurrence
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    rationalOrientationSign
        (match desired with
          | .forward => forwardNormalizationNegative occurrence
          | .reverse => reverseNormalizationNegative occurrence) ≈
      occurrenceNormalizationSign desired occurrence := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases desired <;> cases orientation <;>
    cases row <;> cases column <;> decide

/-- XOR accumulation and multiplication of occurrence signs agree for an
arbitrary structurally supplied transport list. -/
theorem rationalOrientationSign_transportParity :
    ∀ entries : List OrientationTransportEntry,
      rationalOrientationSign (orientationTransportParity entries) ≈
        orientationTransportSignProduct entries
  | [] => Q'.eqv_refl 1
  | (desired, occurrence) :: entries => by
      refine Q'.eqv_trans _ _ _
        (rationalOrientationSign_signXor
          (match desired with
            | .forward => forwardNormalizationNegative occurrence
            | .reverse => reverseNormalizationNegative occurrence)
          (orientationTransportParity entries)) ?_
      exact q_mul_congr_local
        (rationalOrientationSign_occurrence desired occurrence)
        (rationalOrientationSign_transportParity entries)

/-- Normalizing one occurrence complements its semantic target coordinate
exactly when its orientation mismatches the desired convention. -/
theorem complementIf_orientationMismatch_operatorTarget
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    complementIf
        (orientationMismatch desired occurrence.orientation)
        occurrence.operatorTarget =
      (normalizeOccurrence desired occurrence).operatorTarget := by
  rw [normalizeOccurrence_eq_operatorOccurrence]
  cases desired <;> rfl

/-- The analogous statement for the semantic source coordinate. -/
theorem complementIf_orientationMismatch_operatorSource
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    complementIf
        (orientationMismatch desired occurrence.orientation)
        occurrence.operatorSource =
      (normalizeOccurrence desired occurrence).operatorSource := by
  rw [normalizeOccurrence_eq_operatorOccurrence]
  cases desired <;> rfl

/-- Applying the compiled list mask to the raw target word gives precisely
the normalized target word. -/
theorem applyEpsilonMask_orientationTransportTargetBits :
    ∀ entries : List OrientationTransportEntry,
      applyEpsilonMask
          (orientationTransportMask entries)
          (orientationTransportTargetBits entries) =
        orientationTransportNormalizedTargetBits entries
  | [] => rfl
  | (desired, occurrence) :: entries => by
      change
        complementIf
              (orientationMismatch desired occurrence.orientation)
              occurrence.operatorTarget ::
            applyEpsilonMask
              (orientationTransportMask entries)
              (orientationTransportTargetBits entries) =
          (normalizeOccurrence desired occurrence).operatorTarget ::
            orientationTransportNormalizedTargetBits entries
      rw [complementIf_orientationMismatch_operatorTarget,
        applyEpsilonMask_orientationTransportTargetBits entries]

/-- Applying the same mask to the raw source word gives its normalized source
word. -/
theorem applyEpsilonMask_orientationTransportSourceBits :
    ∀ entries : List OrientationTransportEntry,
      applyEpsilonMask
          (orientationTransportMask entries)
          (orientationTransportSourceBits entries) =
        orientationTransportNormalizedSourceBits entries
  | [] => rfl
  | (desired, occurrence) :: entries => by
      change
        complementIf
              (orientationMismatch desired occurrence.orientation)
              occurrence.operatorSource ::
            applyEpsilonMask
              (orientationTransportMask entries)
              (orientationTransportSourceBits entries) =
          (normalizeOccurrence desired occurrence).operatorSource ::
            orientationTransportNormalizedSourceBits entries
      rw [complementIf_orientationMismatch_operatorSource,
        applyEpsilonMask_orientationTransportSourceBits entries]

/-- The target-mask sign times the source-mask sign is exactly the product of
the occurrence pseudoreality signs.  This is the structural step that splits
the old exterior normalization sign between the two sides of a rank-one
channel kernel. -/
theorem epsilonMaskSign_target_mul_source :
    ∀ entries : List OrientationTransportEntry,
      epsilonMaskSign
          (orientationTransportMask entries)
          (orientationTransportTargetBits entries) *
        epsilonMaskSign
          (orientationTransportMask entries)
          (orientationTransportSourceBits entries) ≈
      orientationTransportSignProduct entries
  | [] => Q'.one_mul_eqv 1
  | (desired, occurrence) :: entries => by
      cases hmismatch :
          orientationMismatch desired occurrence.orientation with
      | false =>
          simp only [orientationTransportMask,
            orientationTransportTargetBits,
            orientationTransportSourceBits, epsilonMaskSign,
            occurrenceNormalizationSign, hmismatch,
            orientationTransportSignProduct]
          exact Q'.eqv_trans _ _ _
            (epsilonMaskSign_target_mul_source entries)
            (Q'.eqv_symm
              (Q'.one_mul_eqv
                (orientationTransportSignProduct entries)))
      | true =>
          simp only [orientationTransportMask,
            orientationTransportTargetBits,
            orientationTransportSourceBits, epsilonMaskSign,
            occurrenceNormalizationSign, hmismatch,
            orientationTransportSignProduct]
          refine Q'.eqv_trans _ _ _
            (mul4_rearrange
              (epsilonCoordinateSign occurrence.operatorTarget)
              (epsilonMaskSign
                (orientationTransportMask entries)
                (orientationTransportTargetBits entries))
              (epsilonCoordinateSign occurrence.operatorSource)
              (epsilonMaskSign
                (orientationTransportMask entries)
                (orientationTransportSourceBits entries))) ?_
          exact q_mul_congr_local
            (Q'.eqv_symm
              (FundamentalOccurrence.fundamentalDualitySign_operatorCoordinates
                occurrence))
            (epsilonMaskSign_target_mul_source entries)

/-- The Boolean parity of a transport list is therefore exactly the product
of its target and source epsilon-mask signs. -/
theorem rationalOrientationSign_eqv_targetSourceMaskSigns
    (entries : List OrientationTransportEntry) :
    rationalOrientationSign (orientationTransportParity entries) ≈
      epsilonMaskSign
          (orientationTransportMask entries)
          (orientationTransportTargetBits entries) *
        epsilonMaskSign
          (orientationTransportMask entries)
          (orientationTransportSourceBits entries) :=
  Q'.eqv_trans _ _ _
    (rationalOrientationSign_transportParity entries)
    (Q'.eqv_symm (epsilonMaskSign_target_mul_source entries))

/-- Multiplying the two pointwise epsilon-transport laws factors the mask
sign between target and source without enumerating either Boolean word. -/
theorem epsilonMask_eval_product_local
    (mask : List Bool)
    (target source : BoolWord mask.length)
    (x : BoolTensor mask.length) :
    BoolTensor.eval mask.length ((SignedBoolWiring.epsilonMask mask).act x)
          (BoolWord.toList mask.length target) *
        BoolTensor.eval mask.length ((SignedBoolWiring.epsilonMask mask).act x)
          (BoolWord.toList mask.length source) ≈
      (epsilonMaskSign mask (BoolWord.toList mask.length target) *
          epsilonMaskSign mask (BoolWord.toList mask.length source)) *
        (BoolTensor.eval mask.length x
            (applyEpsilonMask mask
              (BoolWord.toList mask.length target)) *
          BoolTensor.eval mask.length x
            (applyEpsilonMask mask
              (BoolWord.toList mask.length source))) := by
  refine Q'.eqv_trans _ _ _
    (q_mul_congr_local
      (SignedBoolWiring.epsilonMask_eval mask target x)
      (SignedBoolWiring.epsilonMask_eval mask source x)) ?_
  exact mul4_rearrange
    (epsilonMaskSign mask (BoolWord.toList mask.length target))
    (BoolTensor.eval mask.length x
      (applyEpsilonMask mask (BoolWord.toList mask.length target)))
    (epsilonMaskSign mask (BoolWord.toList mask.length source))
    (BoolTensor.eval mask.length x
      (applyEpsilonMask mask (BoolWord.toList mask.length source)))

/-! ### Fixed valence transport lists -/

def orientedBivalentTransportEntries
    (first second : FundamentalOccurrence) :
    List OrientationTransportEntry :=
  [(.forward, first), (.reverse, second)]

/-- The four-valent transport list is in channel-tensor order.  This is the
essential positional swap `[1,3,2,4]` from literal `F R F R` order. -/
def orientedFourTransportEntries
    (first second third fourth : FundamentalOccurrence) :
    List OrientationTransportEntry :=
  [(.forward, first), (.forward, third),
    (.reverse, second), (.reverse, fourth)]

def orientedSixTransportEntries
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    List OrientationTransportEntry :=
  [(.forward, first), (.forward, second), (.forward, third),
    (.reverse, fourth), (.reverse, fifth), (.reverse, sixth)]

private theorem signXor_false_right (value : Bool) :
    signXor value false = value := by
  cases value <;> rfl

private theorem signXor_assoc (first second third : Bool) :
    signXor (signXor first second) third =
      signXor first (signXor second third) := by
  cases first <;> cases second <;> cases third <;> rfl

private theorem signXor_swap_middle
    (first second third : Bool) :
    signXor first (signXor second third) =
      signXor second (signXor first third) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- The bivalent normalizer parity is the parity of its tensor-ordered
transport list. -/
theorem orientedBivalentNormalizationNegative_eq_transportParity
    (first second : FundamentalOccurrence) :
    orientedBivalentNormalizationNegative first second =
      orientationTransportParity
        (orientedBivalentTransportEntries first second) := by
  unfold orientedBivalentNormalizationNegative
    orientedBivalentTransportEntries
  simp only [orientationTransportParity, signXor_false_right]

/-- The four-valent normalizer parity is unchanged by the required middle
swap from literal order to channel-tensor order `[1,3,2,4]`. -/
theorem orientedFourNormalizationNegative_eq_transportParity
    (first second third fourth : FundamentalOccurrence) :
    orientedFourNormalizationNegative first second third fourth =
      orientationTransportParity
        (orientedFourTransportEntries first second third fourth) := by
  unfold orientedFourNormalizationNegative orientedFourTransportEntries
  simp only [orientationTransportParity, signXor_false_right]
  rw [signXor_assoc]
  rw [signXor_swap_middle
    (reverseNormalizationNegative second)
    (forwardNormalizationNegative third)
    (reverseNormalizationNegative fourth)]

/-- The six-valent left-associated normalizer parity is the same XOR as the
right-recursive tensor-order transport list. -/
theorem orientedSixNormalizationNegative_eq_transportParity
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    orientedSixNormalizationNegative
        first second third fourth fifth sixth =
      orientationTransportParity
        (orientedSixTransportEntries
          first second third fourth fifth sixth) := by
  unfold orientedSixNormalizationNegative orientedSixTransportEntries
  simp only [orientationTransportParity, signXor_false_right]
  repeat rw [signXor_assoc]

/-- The first component of an explicitly signed rational-complex value is
the corresponding rational sign times its original first component. -/
theorem signedRationalComplex_fst_eqv_rationalOrientationSign_mul
    (negative : Bool) (value : RationalComplex) :
    (signedRationalComplex negative value).1 ≈
      rationalOrientationSign negative * value.1 := by
  cases negative with
  | false => exact Q'.eqv_symm (Q'.one_mul_eqv value.1)
  | true =>
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 value.1)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv value.1)))

/-- Signing a pure-real rational-complex value keeps its imaginary component
equivalent to zero. -/
theorem signedRationalComplex_pureReal
    (negative : Bool) (value : Q') :
    (signedRationalComplex negative (value, 0)).2 ≈ 0 := by
  cases negative with
  | false => exact Q'.eqv_refl 0
  | true =>
      change Q'.eqv (-(0 : Q')) 0
      decide

/-- Bivalent epsilon mask in the channel tensor order `(output,input)`. -/
def orientedBivalentChannelMask
    (first second : FundamentalOccurrence) : List Bool :=
  orientationTransportMask
    (orientedBivalentTransportEntries first second)

/-- Four-valent mask in output-first/input-second order.  The literal
`F R F R` positions are therefore reordered as `[1,3,2,4]`. -/
def orientedFourChannelMask
    (first second third fourth : FundamentalOccurrence) : List Bool :=
  orientationTransportMask
    (orientedFourTransportEntries first second third fourth)

/-- Six-valent mask in the canonical output-output-output-input-input-input
order, which already agrees with the literal `F F F R R R` positions. -/
def orientedSixChannelMask
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    List Bool :=
  orientationTransportMask
    (orientedSixTransportEntries
      first second third fourth fifth sixth)

/-- Signed bivalent channel transport compiled from the occurrence mask. -/
def orientedBivalentChannelWiring
    (first second : FundamentalOccurrence) : SignedBoolWiring 2 :=
  SignedBoolWiring.epsilonMask
    (orientedBivalentChannelMask first second)

/-- Signed four-valent channel transport, including the frozen positional
order `[1,3,2,4]` in the mask itself. -/
def orientedFourChannelWiring
    (first second third fourth : FundamentalOccurrence) :
    SignedBoolWiring 4 :=
  SignedBoolWiring.epsilonMask
    (orientedFourChannelMask first second third fourth)

/-- Signed six-valent channel transport. -/
def orientedSixChannelWiring
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    SignedBoolWiring 6 :=
  SignedBoolWiring.epsilonMask
    (orientedSixChannelMask first second third fourth fifth sixth)

/-- Arbitrary-orientation bivalent invariant tensor. -/
def orientedBivalentChannelBoolTensor
    (first second : FundamentalOccurrence) : BoolTensor 2 :=
  (orientedBivalentChannelWiring first second).act
    bivalentInvariantDeltaBoolTensor

/-- Arbitrary-orientation four-valent channel tensor. -/
def orientedFourChannelBoolTensor
    (first second third fourth : FundamentalOccurrence)
    (channel : FourValentOperatorBoolChannel) : BoolTensor 4 :=
  (orientedFourChannelWiring first second third fourth).act
    (fourValentOperatorChannelBoolTensor channel)

/-- Arbitrary-orientation six-valent TL-channel tensor. -/
def orientedSixChannelBoolTensor
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (channel : SixValentTLChannel) : BoolTensor 6 :=
  (orientedSixChannelWiring first second third fourth fifth sixth).act
    (sixValentOperatorChannelBoolTensor channel)

/-! ### Pointwise target/source sign factorization -/

/-- At valence two, multiplying the transported target and source channel
values absorbs the former exterior bivalent normalization sign exactly. -/
theorem orientedBivalentChannelWiring_eval_product
    (first second : FundamentalOccurrence) (x : BoolTensor 2) :
    BoolTensor.eval 2
          ((orientedBivalentChannelWiring first second).act x)
          (orientationTransportTargetBits
            (orientedBivalentTransportEntries first second)) *
        BoolTensor.eval 2
          ((orientedBivalentChannelWiring first second).act x)
          (orientationTransportSourceBits
            (orientedBivalentTransportEntries first second)) ≈
      rationalOrientationSign
          (orientedBivalentNormalizationNegative first second) *
        (BoolTensor.eval 2 x
            (orientationTransportNormalizedTargetBits
              (orientedBivalentTransportEntries first second)) *
          BoolTensor.eval 2 x
            (orientationTransportNormalizedSourceBits
              (orientedBivalentTransportEntries first second))) := by
  have h := epsilonMask_eval_product_local
    (orientedBivalentChannelMask first second)
    (orientationTransportTargetWord
      (orientedBivalentTransportEntries first second))
    (orientationTransportSourceWord
      (orientedBivalentTransportEntries first second)) x
  unfold orientedBivalentChannelMask at h
  rw [orientationTransportTargetWord_toList,
    orientationTransportSourceWord_toList,
    applyEpsilonMask_orientationTransportTargetBits,
    applyEpsilonMask_orientationTransportSourceBits] at h
  have hsign :
      epsilonMaskSign
            (orientationTransportMask
              (orientedBivalentTransportEntries first second))
            (orientationTransportTargetBits
              (orientedBivalentTransportEntries first second)) *
          epsilonMaskSign
            (orientationTransportMask
              (orientedBivalentTransportEntries first second))
            (orientationTransportSourceBits
              (orientedBivalentTransportEntries first second)) ≈
        rationalOrientationSign
          (orientedBivalentNormalizationNegative first second) := by
    apply Q'.eqv_symm
    rw [orientedBivalentNormalizationNegative_eq_transportParity]
    exact rationalOrientationSign_eqv_targetSourceMaskSigns
      (orientedBivalentTransportEntries first second)
  unfold orientedBivalentChannelWiring orientedBivalentChannelMask
  exact Q'.eqv_trans _ _ _ h
    (q_mul_congr_local hsign (Q'.eqv_refl _))

/-- The same pointwise factorization for every four-coordinate symbolic
channel, with the `[1,3,2,4]` tensor order already built into the transport
list. -/
theorem orientedFourChannelWiring_eval_product
    (first second third fourth : FundamentalOccurrence)
    (x : BoolTensor 4) :
    BoolTensor.eval 4
          ((orientedFourChannelWiring
            first second third fourth).act x)
          (orientationTransportTargetBits
            (orientedFourTransportEntries
              first second third fourth)) *
        BoolTensor.eval 4
          ((orientedFourChannelWiring
            first second third fourth).act x)
          (orientationTransportSourceBits
            (orientedFourTransportEntries
              first second third fourth)) ≈
      rationalOrientationSign
          (orientedFourNormalizationNegative
            first second third fourth) *
        (BoolTensor.eval 4 x
            (orientationTransportNormalizedTargetBits
              (orientedFourTransportEntries
                first second third fourth)) *
          BoolTensor.eval 4 x
            (orientationTransportNormalizedSourceBits
              (orientedFourTransportEntries
                first second third fourth))) := by
  have h := epsilonMask_eval_product_local
    (orientedFourChannelMask first second third fourth)
    (orientationTransportTargetWord
      (orientedFourTransportEntries first second third fourth))
    (orientationTransportSourceWord
      (orientedFourTransportEntries first second third fourth)) x
  unfold orientedFourChannelMask at h
  rw [orientationTransportTargetWord_toList,
    orientationTransportSourceWord_toList,
    applyEpsilonMask_orientationTransportTargetBits,
    applyEpsilonMask_orientationTransportSourceBits] at h
  have hsign :
      epsilonMaskSign
            (orientationTransportMask
              (orientedFourTransportEntries
                first second third fourth))
            (orientationTransportTargetBits
              (orientedFourTransportEntries
                first second third fourth)) *
          epsilonMaskSign
            (orientationTransportMask
              (orientedFourTransportEntries
                first second third fourth))
            (orientationTransportSourceBits
              (orientedFourTransportEntries
                first second third fourth)) ≈
        rationalOrientationSign
          (orientedFourNormalizationNegative
            first second third fourth) := by
    apply Q'.eqv_symm
    rw [orientedFourNormalizationNegative_eq_transportParity]
    exact rationalOrientationSign_eqv_targetSourceMaskSigns
      (orientedFourTransportEntries first second third fourth)
  unfold orientedFourChannelWiring orientedFourChannelMask
  exact Q'.eqv_trans _ _ _ h
    (q_mul_congr_local hsign (Q'.eqv_refl _))

/-- The pointwise six-valent factorization is structural in the six-coordinate
tensor; none of its sixty-four assignments is exposed. -/
theorem orientedSixChannelWiring_eval_product
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (x : BoolTensor 6) :
    BoolTensor.eval 6
          ((orientedSixChannelWiring
            first second third fourth fifth sixth).act x)
          (orientationTransportTargetBits
            (orientedSixTransportEntries
              first second third fourth fifth sixth)) *
        BoolTensor.eval 6
          ((orientedSixChannelWiring
            first second third fourth fifth sixth).act x)
          (orientationTransportSourceBits
            (orientedSixTransportEntries
              first second third fourth fifth sixth)) ≈
      rationalOrientationSign
          (orientedSixNormalizationNegative
            first second third fourth fifth sixth) *
        (BoolTensor.eval 6 x
            (orientationTransportNormalizedTargetBits
              (orientedSixTransportEntries
                first second third fourth fifth sixth)) *
          BoolTensor.eval 6 x
            (orientationTransportNormalizedSourceBits
              (orientedSixTransportEntries
                first second third fourth fifth sixth))) := by
  have h := epsilonMask_eval_product_local
    (orientedSixChannelMask
      first second third fourth fifth sixth)
    (orientationTransportTargetWord
      (orientedSixTransportEntries
        first second third fourth fifth sixth))
    (orientationTransportSourceWord
      (orientedSixTransportEntries
        first second third fourth fifth sixth)) x
  unfold orientedSixChannelMask at h
  rw [orientationTransportTargetWord_toList,
    orientationTransportSourceWord_toList,
    applyEpsilonMask_orientationTransportTargetBits,
    applyEpsilonMask_orientationTransportSourceBits] at h
  have hsign :
      epsilonMaskSign
            (orientationTransportMask
              (orientedSixTransportEntries
                first second third fourth fifth sixth))
            (orientationTransportTargetBits
              (orientedSixTransportEntries
                first second third fourth fifth sixth)) *
          epsilonMaskSign
            (orientationTransportMask
              (orientedSixTransportEntries
                first second third fourth fifth sixth))
            (orientationTransportSourceBits
              (orientedSixTransportEntries
                first second third fourth fifth sixth)) ≈
        rationalOrientationSign
          (orientedSixNormalizationNegative
            first second third fourth fifth sixth) := by
    apply Q'.eqv_symm
    rw [orientedSixNormalizationNegative_eq_transportParity]
    exact rationalOrientationSign_eqv_targetSourceMaskSigns
      (orientedSixTransportEntries
        first second third fourth fifth sixth)
  unfold orientedSixChannelWiring orientedSixChannelMask
  exact Q'.eqv_trans _ _ _ h
    (q_mul_congr_local hsign (Q'.eqv_refl _))

/-! ### Rank-one resolutions using the transported channel vectors -/

private theorem q_add_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem scalar_weight_swap (sign weight value : Q') :
    sign * (weight * value) ≈ weight * (sign * value) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv sign weight value)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (sign * weight) (weight * sign) value
      (Q'.mul_comm_eqv sign weight)) ?_
  exact Q'.mul_assoc_eqv weight sign value

private theorem weight_value_sign_swap (weight value sign : Q') :
    (weight * value) * sign ≈ weight * (sign * value) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv weight value sign) ?_
  exact Q'.mul_eqv_congr_left weight _ _
    (Q'.mul_comm_eqv value sign)

/-- Target value of the transported bivalent invariant vector at the raw
semantic occurrence coordinates. -/
def orientedBivalentTransportedTargetValue
    (first second : FundamentalOccurrence) : Q' :=
  BoolTensor.eval 2
    (orientedBivalentChannelBoolTensor first second)
    (orientationTransportTargetBits
      (orientedBivalentTransportEntries first second))

/-- Source value of the same transported bivalent invariant vector. -/
def orientedBivalentTransportedSourceValue
    (first second : FundamentalOccurrence) : Q' :=
  BoolTensor.eval 2
    (orientedBivalentChannelBoolTensor first second)
    (orientationTransportSourceBits
      (orientedBivalentTransportEntries first second))

/-- Positive rank-one bivalent resolution after the epsilon sign has been
absorbed into the target and source copies of one transported vector. -/
def orientedBivalentTransportedPositiveScalar
    (first second : FundamentalOccurrence) : Q' :=
  bivalentInvariantChannelWeight *
    (orientedBivalentTransportedTargetValue first second *
      orientedBivalentTransportedSourceValue first second)

/-- Target coordinate of one transported four-valent channel. -/
def orientedFourTransportedTargetValue
    (first second third fourth : FundamentalOccurrence)
    (channel : FourValentOperatorBoolChannel) : Q' :=
  BoolTensor.eval 4
    (orientedFourChannelBoolTensor
      first second third fourth channel)
    (orientationTransportTargetBits
      (orientedFourTransportEntries first second third fourth))

/-- Source coordinate of one transported four-valent channel. -/
def orientedFourTransportedSourceValue
    (first second third fourth : FundamentalOccurrence)
    (channel : FourValentOperatorBoolChannel) : Q' :=
  BoolTensor.eval 4
    (orientedFourChannelBoolTensor
      first second third fourth channel)
    (orientationTransportSourceBits
      (orientedFourTransportEntries first second third fourth))

/-- Positive singlet/triplet resolution formed from the same transported
channel vector on its target and source sides. -/
def orientedFourTransportedPositiveScalar
    (first second third fourth : FundamentalOccurrence) : Q' :=
  orientedFourTransportedTargetValue
      first second third fourth .singlet *
    orientedFourTransportedSourceValue
      first second third fourth .singlet +
  oneThird *
    (orientedFourTransportedTargetValue
        first second third fourth .triplet *
      orientedFourTransportedSourceValue
        first second third fourth .triplet)

/-- Target coordinate of one transported six-valent TL channel. -/
def orientedSixTransportedTargetValue
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (channel : SixValentTLChannel) : Q' :=
  BoolTensor.eval 6
    (orientedSixChannelBoolTensor
      first second third fourth fifth sixth channel)
    (orientationTransportTargetBits
      (orientedSixTransportEntries
        first second third fourth fifth sixth))

/-- Source coordinate of the same transported TL channel. -/
def orientedSixTransportedSourceValue
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (channel : SixValentTLChannel) : Q' :=
  BoolTensor.eval 6
    (orientedSixChannelBoolTensor
      first second third fourth fifth sixth channel)
    (orientationTransportSourceBits
      (orientedSixTransportEntries
        first second third fourth fifth sixth))

/-- Five-channel positive resolution formed from transported TL vectors. -/
def orientedSixTransportedPositiveScalar
    (first second third fourth fifth sixth : FundamentalOccurrence) : Q' :=
  sixValentTLChannelSum (fun channel =>
    sixValentTLChannelInverseWeight channel *
      (orientedSixTransportedTargetValue
          first second third fourth fifth sixth channel *
        orientedSixTransportedSourceValue
          first second third fourth fifth sixth channel))

/-- In normalized bivalent coordinates the symbolic delta tensor is exactly
the operator-kernel invariant coordinate. -/
theorem bivalentStandardChannelProduct_eq_normalizedEval
    (first second : FundamentalOccurrence) :
    bivalentInvariantDelta
          (orientedBivalentTargetIndex first second) *
        bivalentInvariantDelta
          (orientedBivalentSourceIndex first second) =
      BoolTensor.eval 2 bivalentInvariantDeltaBoolTensor
          (orientationTransportNormalizedTargetBits
            (orientedBivalentTransportEntries first second)) *
        BoolTensor.eval 2 bivalentInvariantDeltaBoolTensor
          (orientationTransportNormalizedSourceBits
            (orientedBivalentTransportEntries first second)) := rfl

/-- The four-valent symbolic channel values at the normalized words are the
existing packaged operator-channel coordinates. -/
theorem fourStandardChannelProduct_eq_normalizedEval
    (first second third fourth : FundamentalOccurrence)
    (channel : FourValentOperatorBoolChannel) :
    fourValentOperatorBoolChannelCoordinate channel
          (orientedFourTargetIndex first second third fourth) *
        fourValentOperatorBoolChannelCoordinate channel
          (orientedFourSourceIndex first second third fourth) =
      BoolTensor.eval 4 (fourValentOperatorChannelBoolTensor channel)
          (orientationTransportNormalizedTargetBits
            (orientedFourTransportEntries
              first second third fourth)) *
        BoolTensor.eval 4 (fourValentOperatorChannelBoolTensor channel)
          (orientationTransportNormalizedSourceBits
            (orientedFourTransportEntries
              first second third fourth)) := by
  cases channel <;> rfl

/-- The corresponding six-valent identification is structural in the frozen
TL channel and does not expand its Boolean coordinate table. -/
theorem sixStandardChannelProduct_eq_normalizedEval
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (channel : SixValentTLChannel) :
    sixValentOperatorChannelCoordinate channel
          (orientedSixTargetIndex
            first second third fourth fifth sixth) *
        sixValentOperatorChannelCoordinate channel
          (orientedSixSourceIndex
            first second third fourth fifth sixth) =
      BoolTensor.eval 6 (sixValentOperatorChannelBoolTensor channel)
          (orientationTransportNormalizedTargetBits
            (orientedSixTransportEntries
              first second third fourth fifth sixth)) *
        BoolTensor.eval 6 (sixValentOperatorChannelBoolTensor channel)
          (orientationTransportNormalizedSourceBits
            (orientedSixTransportEntries
              first second third fourth fifth sixth)) := by
  rfl

/-- The arbitrary bivalent Haar kernel is one positive-weight rank-one term
in a single transported invariant vector; no exterior sign remains. -/
theorem orientedBivalentHaarKernel_fst_eqv_transportedPositive
    (first second : FundamentalOccurrence) :
    (orientedBivalentHaarKernel first second).1 ≈
      orientedBivalentTransportedPositiveScalar first second := by
  refine Q'.eqv_trans _ _ _
    (orientedBivalentHaarKernel_eqv_positiveChannel first second).1 ?_
  unfold orientedBivalentPositiveChannelKernel
  refine Q'.eqv_trans _ _ _
    (signedRationalComplex_fst_eqv_rationalOrientationSign_mul
      (orientedBivalentNormalizationNegative first second)
      (bivalentOperatorPositiveChannelKernel
        (orientedBivalentTargetIndex first second)
        (orientedBivalentSourceIndex first second))) ?_
  unfold bivalentOperatorPositiveChannelKernel
    bivalentOperatorPositiveChannelScalar
    orientedBivalentTransportedPositiveScalar
    orientedBivalentTransportedTargetValue
    orientedBivalentTransportedSourceValue
    orientedBivalentChannelBoolTensor
  rw [bivalentStandardChannelProduct_eq_normalizedEval]
  refine Q'.eqv_trans _ _ _
    (scalar_weight_swap
      (rationalOrientationSign
        (orientedBivalentNormalizationNegative first second))
      bivalentInvariantChannelWeight
      (BoolTensor.eval 2 bivalentInvariantDeltaBoolTensor
          (orientationTransportNormalizedTargetBits
            (orientedBivalentTransportEntries first second)) *
        BoolTensor.eval 2 bivalentInvariantDeltaBoolTensor
          (orientationTransportNormalizedSourceBits
            (orientedBivalentTransportEntries first second)))) ?_
  exact Q'.mul_eqv_congr_left bivalentInvariantChannelWeight _ _
    (Q'.eqv_symm
      (orientedBivalentChannelWiring_eval_product
        first second bivalentInvariantDeltaBoolTensor))

/-- The arbitrary four-valent kernel is the sum of the two positive weights
`1,1/3` times target/source products of the same transported singlet and
triplet vectors. -/
theorem orientedFourNormalizedHaarProjector_fst_eqv_transportedPositive
    (first second third fourth : FundamentalOccurrence) :
    (orientedFourNormalizedHaarProjector
        first second third fourth).1 ≈
      orientedFourTransportedPositiveScalar
        first second third fourth := by
  refine Q'.eqv_trans _ _ _
    (orientedFourNormalizedHaarProjector_eqv_positiveChannel
      first second third fourth).1 ?_
  unfold orientedFourPositiveChannelKernel
  refine Q'.eqv_trans _ _ _
    (signedRationalComplex_fst_eqv_rationalOrientationSign_mul
      (orientedFourNormalizationNegative
        first second third fourth)
      (fourValentOperatorPositiveChannelKernel
        (orientedFourTargetIndex first second third fourth)
        (orientedFourSourceIndex first second third fourth))) ?_
  unfold fourValentOperatorPositiveChannelKernel
    fourValentOperatorPositiveChannelScalar
  have hsinglet := fourStandardChannelProduct_eq_normalizedEval
    first second third fourth .singlet
  change
    twoLegOperatorSingletCoordinate
          (orientedFourTargetIndex first second third fourth) *
        twoLegOperatorSingletCoordinate
          (orientedFourSourceIndex first second third fourth) = _
    at hsinglet
  have htriplet := fourStandardChannelProduct_eq_normalizedEval
    first second third fourth .triplet
  change
    twoLegOperatorTripletCoordinate
          (orientedFourTargetIndex first second third fourth) *
        twoLegOperatorTripletCoordinate
          (orientedFourSourceIndex first second third fourth) = _
    at htriplet
  rw [hsinglet, htriplet]
  let sign := rationalOrientationSign
    (orientedFourNormalizationNegative first second third fourth)
  let singletProduct :=
    BoolTensor.eval 4
        (fourValentOperatorChannelBoolTensor .singlet)
        (orientationTransportNormalizedTargetBits
          (orientedFourTransportEntries first second third fourth)) *
      BoolTensor.eval 4
        (fourValentOperatorChannelBoolTensor .singlet)
        (orientationTransportNormalizedSourceBits
          (orientedFourTransportEntries first second third fourth))
  let tripletProduct :=
    BoolTensor.eval 4
        (fourValentOperatorChannelBoolTensor .triplet)
        (orientationTransportNormalizedTargetBits
          (orientedFourTransportEntries first second third fourth)) *
      BoolTensor.eval 4
        (fourValentOperatorChannelBoolTensor .triplet)
        (orientationTransportNormalizedSourceBits
          (orientedFourTransportEntries first second third fourth))
  refine Q'.eqv_trans _
    (sign * singletProduct + sign * (oneThird * tripletProduct)) _
    (Q'.mul_add_eqv sign singletProduct (oneThird * tripletProduct)) ?_
  unfold orientedFourTransportedPositiveScalar
    orientedFourTransportedTargetValue
    orientedFourTransportedSourceValue
    orientedFourChannelBoolTensor
  exact q_add_congr_local
    (Q'.eqv_symm
      (orientedFourChannelWiring_eval_product
        first second third fourth
        (fourValentOperatorChannelBoolTensor .singlet)))
    (Q'.eqv_trans _ _ _
      (scalar_weight_swap sign oneThird tripletProduct)
      (Q'.mul_eqv_congr_left oneThird _ _
        (Q'.eqv_symm
          (orientedFourChannelWiring_eval_product
            first second third fourth
            (fourValentOperatorChannelBoolTensor .triplet)))))

/-- The arbitrary six-valent kernel is the five-channel positive sum formed
from transported TL vectors.  The proof moves the one global sign through the
frozen shallow channel sum, never through a sixty-four-entry coordinate
expansion. -/
theorem orientedSixNormalizedHaarProjector_fst_eqv_transportedPositive
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    (orientedSixNormalizedHaarProjector
        first second third fourth fifth sixth).1 ≈
      orientedSixTransportedPositiveScalar
        first second third fourth fifth sixth := by
  refine Q'.eqv_trans _ _ _
    (orientedSixNormalizedHaarProjector_eqv_positiveChannel
      first second third fourth fifth sixth).1 ?_
  unfold orientedSixPositiveChannelKernel
  refine Q'.eqv_trans _ _ _
    (signedRationalComplex_fst_eqv_rationalOrientationSign_mul
      (orientedSixNormalizationNegative
        first second third fourth fifth sixth)
      (balancedSixValentOperatorTLPositive
        (orientedSixTargetIndex
          first second third fourth fifth sixth)
        (orientedSixSourceIndex
          first second third fourth fifth sixth))) ?_
  unfold balancedSixValentOperatorTLPositive
    balancedSixValentOperatorTLPositiveScalar
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (rationalOrientationSign
        (orientedSixNormalizationNegative
          first second third fourth fifth sixth))
      (sixValentTLChannelSum (fun channel =>
        sixValentTLChannelInverseWeight channel *
          (sixValentOperatorChannelCoordinate channel
              (orientedSixTargetIndex
                first second third fourth fifth sixth) *
            sixValentOperatorChannelCoordinate channel
              (orientedSixSourceIndex
                first second third fourth fifth sixth))))) ?_
  refine Q'.eqv_trans _ _ _
    (sixValentTLChannelSum_mul_right _
      (rationalOrientationSign
        (orientedSixNormalizationNegative
          first second third fourth fifth sixth))) ?_
  unfold orientedSixTransportedPositiveScalar
    orientedSixTransportedTargetValue
    orientedSixTransportedSourceValue
    orientedSixChannelBoolTensor
  exact sixValentTLChannelSum_eqv_congr _ _ (fun channel =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (sixValentTLChannelInverseWeight channel *
          (sixValentOperatorChannelCoordinate channel
              (orientedSixTargetIndex
                first second third fourth fifth sixth) *
            sixValentOperatorChannelCoordinate channel
              (orientedSixSourceIndex
                first second third fourth fifth sixth)))
        (sixValentTLChannelInverseWeight channel *
          (BoolTensor.eval 6
              (sixValentOperatorChannelBoolTensor channel)
              (orientationTransportNormalizedTargetBits
                (orientedSixTransportEntries
                  first second third fourth fifth sixth)) *
            BoolTensor.eval 6
              (sixValentOperatorChannelBoolTensor channel)
              (orientationTransportNormalizedSourceBits
                (orientedSixTransportEntries
                  first second third fourth fifth sixth))))
        (rationalOrientationSign
          (orientedSixNormalizationNegative
            first second third fourth fifth sixth))
        (Q'.mul_eqv_congr_left
          (sixValentTLChannelInverseWeight channel) _ _
          (Q'.eqv_of_eq
            (sixStandardChannelProduct_eq_normalizedEval
              first second third fourth fifth sixth channel))))
      (Q'.eqv_trans _ _ _
        (weight_value_sign_swap
          (sixValentTLChannelInverseWeight channel)
          (BoolTensor.eval 6
              (sixValentOperatorChannelBoolTensor channel)
              (orientationTransportNormalizedTargetBits
                (orientedSixTransportEntries
                  first second third fourth fifth sixth)) *
            BoolTensor.eval 6
              (sixValentOperatorChannelBoolTensor channel)
              (orientationTransportNormalizedSourceBits
                (orientedSixTransportEntries
                  first second third fourth fifth sixth)))
          (rationalOrientationSign
            (orientedSixNormalizationNegative
              first second third fourth fifth sixth)))
        (Q'.mul_eqv_congr_left
          (sixValentTLChannelInverseWeight channel) _ _
          (Q'.eqv_symm
            (orientedSixChannelWiring_eval_product
              first second third fourth fifth sixth
              (sixValentOperatorChannelBoolTensor channel))))))

/-- Total transported positive-channel scalar for the seven cutoff-one local
valences.  Odd valences remain zero and the empty word remains one. -/
def cutoffOneOrientedTransportedPositiveScalar :
    CutoffOneHaarWord → Q'
  | .v0 => 1
  | .v1 _ => 0
  | .v2 first second =>
      orientedBivalentTransportedPositiveScalar first second
  | .v3 _ _ _ => 0
  | .v4 first second third fourth =>
      orientedFourTransportedPositiveScalar first second third fourth
  | .v5 _ _ _ _ _ => 0
  | .v6 first second third fourth fifth sixth =>
      orientedSixTransportedPositiveScalar
        first second third fourth fifth sixth

/-- **Pointwise transported `N3` capstone.**  The real component of every
honest arbitrary-orientation local Haar kernel is a positive-weight sum of
products `v_oriented(target) * v_oriented(source)` using the *same*
transported channel vector on both sides.  No exterior normalization sign and
no Boolean assignment enumeration remains. -/
theorem cutoffOneHaarKernel_fst_eqv_transportedPositiveChannels
    (word : CutoffOneHaarWord) :
    (cutoffOneHaarKernel word).1 ≈
      cutoffOneOrientedTransportedPositiveScalar word := by
  cases word with
  | v0 => exact Q'.eqv_refl 1
  | v1 first => exact Q'.eqv_refl 0
  | v2 first second =>
      exact orientedBivalentHaarKernel_fst_eqv_transportedPositive
        first second
  | v3 first second third => exact Q'.eqv_refl 0
  | v4 first second third fourth =>
      exact
        orientedFourNormalizedHaarProjector_fst_eqv_transportedPositive
          first second third fourth
  | v5 first second third fourth fifth => exact Q'.eqv_refl 0
  | v6 first second third fourth fifth sixth =>
      exact
        orientedSixNormalizedHaarProjector_fst_eqv_transportedPositive
          first second third fourth fifth sixth

/-- Rational-complex lift of the fully transported positive-channel scalar. -/
def cutoffOneOrientedTransportedPositiveKernel
    (word : CutoffOneHaarWord) : RationalComplex :=
  (cutoffOneOrientedTransportedPositiveScalar word, 0)

/-- **Full local `N3` kernel theorem.**  Every honest cutoff-one local Haar
kernel is componentwise equivalent to the positive-weight target/source
factorization in the same transported channel vectors. -/
theorem cutoffOneHaarKernel_eqv_transportedPositiveChannels
    (word : CutoffOneHaarWord) :
    RationalComplexEqv
      (cutoffOneHaarKernel word)
      (cutoffOneOrientedTransportedPositiveKernel word) := by
  constructor
  · exact cutoffOneHaarKernel_fst_eqv_transportedPositiveChannels word
  · cases word with
    | v0 => exact Q'.eqv_refl 0
    | v1 first => exact Q'.eqv_refl 0
    | v2 first second =>
        refine Q'.eqv_trans _ _ _
          (orientedBivalentHaarKernel_eqv_positiveChannel
            first second).2 ?_
        unfold orientedBivalentPositiveChannelKernel
          bivalentOperatorPositiveChannelKernel
        exact signedRationalComplex_pureReal _ _
    | v3 first second third => exact Q'.eqv_refl 0
    | v4 first second third fourth =>
        refine Q'.eqv_trans _ _ _
          (orientedFourNormalizedHaarProjector_eqv_positiveChannel
            first second third fourth).2 ?_
        unfold orientedFourPositiveChannelKernel
          fourValentOperatorPositiveChannelKernel
        exact signedRationalComplex_pureReal _ _
    | v5 first second third fourth fifth => exact Q'.eqv_refl 0
    | v6 first second third fourth fifth sixth =>
        refine Q'.eqv_trans _ _ _
          (orientedSixNormalizedHaarProjector_eqv_positiveChannel
            first second third fourth fifth sixth).2 ?_
        unfold orientedSixPositiveChannelKernel
          balancedSixValentOperatorTLPositive
        exact signedRationalComplex_pureReal _ _

/-- Bivalent orientation transport preserves the exact channel norm. -/
theorem orientedBivalentChannelBoolTensor_gram_eqv
    (first second : FundamentalOccurrence) :
    boolTensorDot 2
        (orientedBivalentChannelBoolTensor first second)
        (orientedBivalentChannelBoolTensor first second) ≈
      boolTensorDot 2 bivalentInvariantDeltaBoolTensor
        bivalentInvariantDeltaBoolTensor := by
  exact SignedBoolWiring.gram_eqv
    (orientedBivalentChannelWiring first second)
    bivalentInvariantDeltaBoolTensor bivalentInvariantDeltaBoolTensor

/-- Four-valent orientation transport preserves every channel Gram entry,
not merely the two diagonal norms. -/
theorem orientedFourChannelBoolTensor_gram_eqv
    (first second third fourth : FundamentalOccurrence)
    (left right : FourValentOperatorBoolChannel) :
    boolTensorDot 4
        (orientedFourChannelBoolTensor
          first second third fourth left)
        (orientedFourChannelBoolTensor
          first second third fourth right) ≈
      boolTensorDot 4
        (fourValentOperatorChannelBoolTensor left)
        (fourValentOperatorChannelBoolTensor right) := by
  exact SignedBoolWiring.gram_eqv
    (orientedFourChannelWiring first second third fourth)
    (fourValentOperatorChannelBoolTensor left)
    (fourValentOperatorChannelBoolTensor right)

/-- Six-valent orientation transport preserves the full five-channel Gram
table without expanding any of the sixty-four Boolean coordinates. -/
theorem orientedSixChannelBoolTensor_gram_eqv
    (first second third fourth fifth sixth : FundamentalOccurrence)
    (left right : SixValentTLChannel) :
    boolTensorDot 6
        (orientedSixChannelBoolTensor
          first second third fourth fifth sixth left)
        (orientedSixChannelBoolTensor
          first second third fourth fifth sixth right) ≈
      boolTensorDot 6
        (sixValentOperatorChannelBoolTensor left)
        (sixValentOperatorChannelBoolTensor right) := by
  exact SignedBoolWiring.gram_eqv
    (orientedSixChannelWiring first second third fourth fifth sixth)
    (sixValentOperatorChannelBoolTensor left)
    (sixValentOperatorChannelBoolTensor right)

/-! ## Axiom audit -/

#print axioms orientedBivalentFundamentalTerm_eq_signed_normalized
#print axioms orientedBivalentHaarKernel_eqv_signed_normalized
#print axioms orientedBivalentHaarKernel_eqv_positiveChannel
#print axioms orientedFourNormalizedHaarProjector_eqv_positiveChannel
#print axioms orientedSixNormalizedHaarProjector_eqv_positiveChannel
#print axioms cutoffOneHaarKernel_eqv_orientedPositiveChannels
#print axioms epsilonMaskSign_target_mul_source
#print axioms orientedBivalentChannelWiring_eval_product
#print axioms orientedFourChannelWiring_eval_product
#print axioms orientedSixChannelWiring_eval_product
#print axioms orientedBivalentHaarKernel_fst_eqv_transportedPositive
#print axioms orientedFourNormalizedHaarProjector_fst_eqv_transportedPositive
#print axioms orientedSixNormalizedHaarProjector_fst_eqv_transportedPositive
#print axioms cutoffOneHaarKernel_fst_eqv_transportedPositiveChannels
#print axioms cutoffOneHaarKernel_eqv_transportedPositiveChannels
#print axioms orientedBivalentChannelBoolTensor_gram_eqv
#print axioms orientedFourChannelBoolTensor_gram_eqv
#print axioms orientedSixChannelBoolTensor_gram_eqv

end YMGap.Continuum.SU2QuaternionCutoffOneOrientedPositiveChannels
