/-
# BF4 retained-Gram reference order

The retained-path construction exposes the finite SU(2) reflection kernel as
a sum of rank-one channels.  This module records the matrix-order estimate
which is natural for that representation.

For one common amplitude family `a(x,p)`, let `r_p` be a nonnegative
reference channel weight and `w_p` the physical channel weight.  Termwise
bounds

    lower * r_p ≤ w_p ≤ upper * r_p

imply, for every rational coefficient vector `c`,

    lower * Q_r(c) ≤ Q_w(c) ≤ upper * Q_r(c),

where `Q` is the complete finite weighted-Gram quadratic.  The same proof
works after an arbitrary finite matrix amplification because it uses only a
nonnegative square in each retained channel.

This is a Loewner/reference-order statement, not scalar entrywise Harnack:
individual Gram entries may be negative.  Its BF4 specialization remains
conditional on a uniform comparison of the actual fixed-interface weights
`centralBoundaryWeight` with a chosen reference weight.  No such all-label,
cutoff-uniform, or spacing-uniform physical estimate is proved here.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4RetainedSU2InterfaceGram

namespace YMGap.Continuum.BF4RetainedGramReferenceOrder

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.BF4RetainedSU2InterfaceGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite weighted-Gram reference order -/

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun x hx =>
            hbound x (List.mem_cons_of_mem head hx)))

/-- A nonnegative reference window on a selected finite channel carrier. -/
structure NonnegativeGramReferenceWindow
    {Channel : Type}
    (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q') : Type where
  lower : Q'
  upper : Q'
  lower_nonnegative : (0 : Q') ≤ lower
  upper_nonnegative : (0 : Q') ≤ upper
  reference_nonnegative :
    ∀ channel, channel ∈ channels →
      (0 : Q') ≤ referenceWeight channel
  lower_bound :
    ∀ channel, channel ∈ channels →
      lower * referenceWeight channel ≤ physicalWeight channel
  upper_bound :
    ∀ channel, channel ∈ channels →
      physicalWeight channel ≤ upper * referenceWeight channel

namespace NonnegativeGramReferenceWindow

/-- The lower reference comparison itself certifies nonnegativity of every
physical channel weight. -/
theorem physical_nonnegative
    {Channel : Type}
    {channels : List Channel}
    {referenceWeight physicalWeight : Channel → Q'}
    (window :
      NonnegativeGramReferenceWindow
        channels referenceWeight physicalWeight)
    (channel : Channel) (hchannel : channel ∈ channels) :
    (0 : Q') ≤ physicalWeight channel := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _
      window.lower_nonnegative
      (window.reference_nonnegative channel hchannel))
    (window.lower_bound channel hchannel)

end NonnegativeGramReferenceWindow

/-- Lower comparison of the manifest Gram sums of squares. -/
theorem weightedGramSOS_reference_lower
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q')
    (lower : Q')
    (hlower :
      ∀ channel, channel ∈ channels →
        lower * referenceWeight channel ≤ physicalWeight channel) :
    lower *
        weightedGramSOS
          states channels referenceWeight amplitude coefficient ≤
      weightedGramSOS
        states channels physicalWeight amplitude coefficient := by
  let square : Channel → Q' := fun channel =>
    channelLinear states amplitude coefficient channel *
      channelLinear states amplitude coefficient channel
  have hsum :
      listQSum
          (fun channel =>
            lower * (referenceWeight channel * square channel))
          channels ≤
        listQSum
          (fun channel =>
            physicalWeight channel * square channel)
          channels := by
    apply listQSum_mono_on
    intro channel hchannel
    have hsquare : (0 : Q') ≤ square channel :=
      q_mul_self_nonneg
        (channelLinear states amplitude coefficient channel)
    have hmul :
        (lower * referenceWeight channel) * square channel ≤
          physicalWeight channel * square channel :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (hlower channel hchannel) hsquare
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            lower (referenceWeight channel) (square channel))))
      hmul
  unfold weightedGramSOS
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (listQSum_mul_left lower
        (fun channel =>
          referenceWeight channel * square channel)
        channels))
    hsum

/-- Upper comparison of the manifest Gram sums of squares. -/
theorem weightedGramSOS_reference_upper
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q')
    (upper : Q')
    (hupper :
      ∀ channel, channel ∈ channels →
        physicalWeight channel ≤ upper * referenceWeight channel) :
    weightedGramSOS
        states channels physicalWeight amplitude coefficient ≤
      upper *
        weightedGramSOS
          states channels referenceWeight amplitude coefficient := by
  let square : Channel → Q' := fun channel =>
    channelLinear states amplitude coefficient channel *
      channelLinear states amplitude coefficient channel
  have hsum :
      listQSum
          (fun channel =>
            physicalWeight channel * square channel)
          channels ≤
        listQSum
          (fun channel =>
            upper * (referenceWeight channel * square channel))
          channels := by
    apply listQSum_mono_on
    intro channel hchannel
    have hsquare : (0 : Q') ≤ square channel :=
      q_mul_self_nonneg
        (channelLinear states amplitude coefficient channel)
    have hmul :
        physicalWeight channel * square channel ≤
          (upper * referenceWeight channel) * square channel :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (hupper channel hchannel) hsquare
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv
          upper (referenceWeight channel) (square channel)))
  unfold weightedGramSOS
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (listQSum_mul_left upper
        (fun channel =>
          referenceWeight channel * square channel)
        channels))

/-- **Finite Loewner/reference-order sandwich.**  Termwise channel-weight
bounds pass through a common amplitude family to every coefficient-vector
quadratic. -/
theorem weightedGramQuadratic_reference_sandwich
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q')
    (lower upper : Q')
    (hlower :
      ∀ channel, channel ∈ channels →
        lower * referenceWeight channel ≤ physicalWeight channel)
    (hupper :
      ∀ channel, channel ∈ channels →
        physicalWeight channel ≤ upper * referenceWeight channel) :
    lower *
        weightedGramQuadratic
          states channels referenceWeight amplitude coefficient ≤
      weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ∧
    weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ≤
      upper *
        weightedGramQuadratic
          states channels referenceWeight amplitude coefficient := by
  have hlowerSOS :=
    weightedGramSOS_reference_lower
      states channels referenceWeight physicalWeight
      amplitude coefficient lower hlower
  have hupperSOS :=
    weightedGramSOS_reference_upper
      states channels referenceWeight physicalWeight
      amplitude coefficient upper hupper
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left lower _ _
          (weightedGramQuadratic_eq_sos
            states channels referenceWeight amplitude coefficient)))
      (Q'.le_trans' _ _ _ hlowerSOS
        (Q'.ge_of_eqv
          (weightedGramQuadratic_eq_sos
            states channels physicalWeight amplitude coefficient)))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (weightedGramQuadratic_eq_sos
          states channels physicalWeight amplitude coefficient))
      (Q'.le_trans' _ _ _ hupperSOS
        (Q'.ge_of_eqv
          (Q'.mul_eqv_congr_left upper _ _
            (weightedGramQuadratic_eq_sos
              states channels referenceWeight amplitude coefficient))))

/-- Bundled nonnegative reference windows therefore give the complete
finite Loewner sandwich. -/
theorem NonnegativeGramReferenceWindow.quadratic_sandwich
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (window :
      NonnegativeGramReferenceWindow
        channels referenceWeight physicalWeight)
    (coefficient : State → Q') :
    window.lower *
        weightedGramQuadratic
          states channels referenceWeight amplitude coefficient ≤
      weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ∧
    weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ≤
      window.upper *
        weightedGramQuadratic
          states channels referenceWeight amplitude coefficient :=
  weightedGramQuadratic_reference_sandwich
    states channels referenceWeight physicalWeight amplitude coefficient
    window.lower window.upper window.lower_bound window.upper_bound

/-- The proof is stable under an arbitrary finite matrix amplification:
replace the state carrier by any finite list of `(matrix index, state)`
pairs and allow an arbitrary common amplified amplitude family. -/
theorem weightedGramQuadratic_reference_sandwich_amplified
    {MatrixIndex State Channel : Type}
    (amplifiedStates : List (MatrixIndex × State))
    (channels : List Channel)
    (referenceWeight physicalWeight : Channel → Q')
    (amplitude : (MatrixIndex × State) → Channel → Q')
    (coefficient : (MatrixIndex × State) → Q')
    (lower upper : Q')
    (hlower :
      ∀ channel, channel ∈ channels →
        lower * referenceWeight channel ≤ physicalWeight channel)
    (hupper :
      ∀ channel, channel ∈ channels →
        physicalWeight channel ≤ upper * referenceWeight channel) :
    lower *
        weightedGramQuadratic
          amplifiedStates channels referenceWeight amplitude coefficient ≤
      weightedGramQuadratic
          amplifiedStates channels physicalWeight amplitude coefficient ∧
    weightedGramQuadratic
          amplifiedStates channels physicalWeight amplitude coefficient ≤
      upper *
        weightedGramQuadratic
          amplifiedStates channels referenceWeight amplitude coefficient :=
  weightedGramQuadratic_reference_sandwich
    amplifiedStates channels referenceWeight physicalWeight
    amplitude coefficient lower upper hlower hupper

/-! ## 2. Common unweighted reference -/

/-- The reference Gram with one unit of weight in every retained channel. -/
def unweightedGramQuadratic
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (amplitude : State → Channel → Q')
    (coefficient : State → Q') : Q' :=
  weightedGramQuadratic states channels
    (fun _ => 1) amplitude coefficient

/-- A uniform scalar window on the physical channel weights gives a
Loewner sandwich against the common unweighted Gram. -/
theorem weightedGramQuadratic_unweighted_sandwich
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (physicalWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q')
    (lower upper : Q')
    (hlower :
      ∀ channel, channel ∈ channels →
        lower ≤ physicalWeight channel)
    (hupper :
      ∀ channel, channel ∈ channels →
        physicalWeight channel ≤ upper) :
    lower *
        unweightedGramQuadratic
          states channels amplitude coefficient ≤
      weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ∧
    weightedGramQuadratic
          states channels physicalWeight amplitude coefficient ≤
      upper *
        unweightedGramQuadratic
          states channels amplitude coefficient := by
  unfold unweightedGramQuadratic
  apply weightedGramQuadratic_reference_sandwich
  · intro channel hchannel
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv lower))
      (hlower channel hchannel)
  · intro channel hchannel
    exact Q'.le_trans' _ _ _
      (hupper channel hchannel)
      (Q'.ge_of_eqv (Q'.mul_one_eqv upper))

/-! ## 3. Conditional specialization to the actual finite BF4 SU(2) Gram -/

/-- A chosen reference-weight quadratic on the actual finite BF4 endpoint,
boundary-channel, and half-amplitude families. -/
def retainedSU2ReferenceQuadratic
    (w : Q') (K half : Nat)
    (referenceWeight : EdgeLabelling → Q')
    (coefficient : EdgeLabelling → Q') : Q' :=
  weightedGramQuadratic
    (centralHalfStates K half)
    (centralBoundaryChannels K half)
    referenceWeight
    (centralHalfAmplitude w K half)
    coefficient

/-- The explicit missing finite BF4 input, bundled as a nonnegative
reference window on the literal fixed-interface carrier. -/
abbrev RetainedSU2BoundaryReferenceWindow
    (w : Q') (K half : Nat)
    (referenceWeight : EdgeLabelling → Q') :=
  NonnegativeGramReferenceWindow
    (centralBoundaryChannels K half)
    referenceWeight
    (centralBoundaryWeight w K half)

/-- The actual retained SU(2) quadratic is exactly its boundary-weighted
Gram presentation. -/
theorem retainedSU2Quadratic_eq_boundaryWeightedGram
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    retainedSU2Quadratic w K half coefficient ≈
      weightedGramQuadratic
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        coefficient := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (centralPhysicalReflectionQuadratic_eq_retainedSU2
        w K half coefficient))
    (centralPhysicalReflectionQuadratic_eq_weightedGram
      w K half coefficient)

/-- **Conditional BF4 retained-Gram reference order.**  The desired finite
matrix sandwich follows immediately once the missing boundary-channel
weight comparison is supplied.  This theorem does not construct that
comparison or make its constants cutoff/spacing uniform. -/
theorem retainedSU2Quadratic_reference_sandwich_of_boundaryWeightComparison
    (w : Q') (K half : Nat)
    (referenceWeight : EdgeLabelling → Q')
    (lower upper : Q')
    (boundaryLower :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          lower * referenceWeight boundary ≤
            centralBoundaryWeight w K half boundary)
    (boundaryUpper :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          centralBoundaryWeight w K half boundary ≤
            upper * referenceWeight boundary)
    (coefficient : EdgeLabelling → Q') :
    lower *
        retainedSU2ReferenceQuadratic
          w K half referenceWeight coefficient ≤
      retainedSU2Quadratic w K half coefficient ∧
    retainedSU2Quadratic w K half coefficient ≤
      upper *
        retainedSU2ReferenceQuadratic
          w K half referenceWeight coefficient := by
  have hsandwich :=
    weightedGramQuadratic_reference_sandwich
      (centralHalfStates K half)
      (centralBoundaryChannels K half)
      referenceWeight
      (centralBoundaryWeight w K half)
      (centralHalfAmplitude w K half)
      coefficient lower upper boundaryLower boundaryUpper
  unfold retainedSU2ReferenceQuadratic
  constructor
  · exact Q'.le_trans' _ _ _ hsandwich.1
      (Q'.ge_of_eqv
        (retainedSU2Quadratic_eq_boundaryWeightedGram
          w K half coefficient))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
      (retainedSU2Quadratic_eq_boundaryWeightedGram
        w K half coefficient))
      hsandwich.2

/-- Bundled form of the conditional BF4 application.  Producing such
windows with constants uniform in the physical cutoff and lattice spacing
is deliberately left as the named missing input. -/
theorem retainedSU2Quadratic_reference_sandwich_of_window
    (w : Q') (K half : Nat)
    (referenceWeight : EdgeLabelling → Q')
    (window :
      RetainedSU2BoundaryReferenceWindow
        w K half referenceWeight)
    (coefficient : EdgeLabelling → Q') :
    window.lower *
        retainedSU2ReferenceQuadratic
          w K half referenceWeight coefficient ≤
      retainedSU2Quadratic w K half coefficient ∧
    retainedSU2Quadratic w K half coefficient ≤
      window.upper *
        retainedSU2ReferenceQuadratic
          w K half referenceWeight coefficient :=
  retainedSU2Quadratic_reference_sandwich_of_boundaryWeightComparison
    w K half referenceWeight window.lower window.upper
    window.lower_bound window.upper_bound coefficient

/-- In the clean unit-reference specialization, a pointwise window on the
actual finite boundary weights sandwiches the actual retained SU(2)
quadratic between scalar multiples of the unweighted common-amplitude Gram.
The boundary window remains an explicit hypothesis. -/
theorem retainedSU2Quadratic_unweighted_sandwich_of_boundaryWeightWindow
    (w : Q') (K half : Nat)
    (lower upper : Q')
    (boundaryLower :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          lower ≤ centralBoundaryWeight w K half boundary)
    (boundaryUpper :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          centralBoundaryWeight w K half boundary ≤ upper)
    (coefficient : EdgeLabelling → Q') :
    lower *
        unweightedGramQuadratic
          (centralHalfStates K half)
          (centralBoundaryChannels K half)
          (centralHalfAmplitude w K half)
          coefficient ≤
      retainedSU2Quadratic w K half coefficient ∧
    retainedSU2Quadratic w K half coefficient ≤
      upper *
        unweightedGramQuadratic
          (centralHalfStates K half)
          (centralBoundaryChannels K half)
          (centralHalfAmplitude w K half)
          coefficient := by
  have hsandwich :=
    weightedGramQuadratic_unweighted_sandwich
      (centralHalfStates K half)
      (centralBoundaryChannels K half)
      (centralBoundaryWeight w K half)
      (centralHalfAmplitude w K half)
      coefficient lower upper boundaryLower boundaryUpper
  constructor
  · exact Q'.le_trans' _ _ _ hsandwich.1
      (Q'.ge_of_eqv
        (retainedSU2Quadratic_eq_boundaryWeightedGram
          w K half coefficient))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (retainedSU2Quadratic_eq_boundaryWeightedGram
          w K half coefficient))
      hsandwich.2

/-! ## Axiom audit -/

#print axioms NonnegativeGramReferenceWindow.physical_nonnegative
#print axioms weightedGramSOS_reference_lower
#print axioms weightedGramSOS_reference_upper
#print axioms weightedGramQuadratic_reference_sandwich
#print axioms NonnegativeGramReferenceWindow.quadratic_sandwich
#print axioms weightedGramQuadratic_reference_sandwich_amplified
#print axioms weightedGramQuadratic_unweighted_sandwich
#print axioms retainedSU2Quadratic_eq_boundaryWeightedGram
#print axioms retainedSU2Quadratic_reference_sandwich_of_boundaryWeightComparison
#print axioms retainedSU2Quadratic_reference_sandwich_of_window
#print axioms retainedSU2Quadratic_unweighted_sandwich_of_boundaryWeightWindow

end YMGap.Continuum.BF4RetainedGramReferenceOrder
