/-
# Terminal-independent projective refresh for finite boundary messages

Physical gluing of adjacent BF4 slabs is a boundary-conditioned fiber
product.  Its finite-horizon Markov kernel is therefore a backward-message
(Doob) normalization of a raw positive grouped transfer kernel, rather than
an independent normalization of each slab.

This file proves the finite exact theorem needed by that route.  A positive
raw kernel with cross-ratio spread `s` retains the same cross-ratio
certificate after multiplication by an arbitrary positive terminal message
and row normalization.  Since every normalized row has total mass one, any
two rows have the pointwise order

  P(first,z) <= s^2 P(second,z).

Consequently every row contains the displayed reference row with common mass
`1 / s^2`.  The coefficient is independent of the terminal boundary message.

This is a proof-by-checking interface for heavy finite computation: an
external Rust or C program may generate kernel entries and a division-free
cross-ratio witness, but the witness is consumed only by this constructive
Lean theorem.  External execution is not trusted as a proof.

## Axiom gate

Finite lists and exact `Q'` arithmetic only, with no forbidden proof
shortcuts, choice principles, or opaque declarations.
-/

import YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence
import YMGap.Continuum.ConstructiveRefreshContraction
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.RationalCrossRatioDiameter.FiniteCrossRatioDiameterCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Projectively natural terminal normalization -/

/-- The backward-message kernel written as positive column rescaling followed
by positive row rescaling.  This order is definitionally compatible with the
projective cross-ratio constructors. -/
def terminalProjectiveKernel
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) (target : Target) : Q' :=
  rowRescaledKernel
    (fun row =>
      Q'.recipPos
        (terminalWeightedDenominator
          targetStates kernel terminal row)
        (denominator_pos row))
    (columnRescaledKernel terminal kernel)
    source target

/-- The projectively natural presentation is pointwise equal in `Q'` to the
canonical terminal-normalized kernel. -/
theorem terminalProjectiveKernel_eqv_terminalNormalizedKernel
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) (target : Target) :
    terminalProjectiveKernel
        targetStates kernel terminal denominator_pos source target ≈
      terminalNormalizedKernel
        targetStates kernel terminal denominator_pos source target := by
  unfold terminalProjectiveKernel rowRescaledKernel
    columnRescaledKernel terminalNormalizedKernel Q'.divPos
  exact Q'.mul_comm_eqv _ _

/-- Positive terminal weighting and its backward-message row normalization
preserve the raw kernel's exact cross-ratio spread. -/
def terminalNormalize
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source) :
    FiniteCrossRatioDiameterCertificate
      (terminalProjectiveKernel
        targetStates kernel terminal denominator_pos)
      sourceStates targetStates :=
  (certificate.columnRescale terminal terminal_pos).rowRescale
    (fun source =>
      Q'.recipPos
        (terminalWeightedDenominator
          targetStates kernel terminal source)
        (denominator_pos source))
    (fun source _ =>
      Q'.recipPos_pos _ (denominator_pos source))

/-- Every projectively presented terminal row has exact total mass one. -/
theorem terminalProjectiveKernel_row_normalized
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) :
    listQSum
        (terminalProjectiveKernel
          targetStates kernel terminal denominator_pos source)
        targetStates ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (terminalNormalizedKernel
        targetStates kernel terminal denominator_pos source)
      targetStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact terminalProjectiveKernel_eqv_terminalNormalizedKernel
      targetStates kernel terminal denominator_pos source target
  · exact terminalNormalizedKernel_row_normalized
      targetStates kernel terminal denominator_pos source

/-! ## 2. Cross-ratio plus row mass gives pointwise row order -/

/-- A row-normalized positive kernel with cross-ratio spread `s` has all rows
pointwise ordered by `s^2`.  This is a finite summation theorem, not an appeal
to Birkhoff--Hopf or a spectral theorem. -/
theorem rowNormalizedKernel_row_domination
    {State Target : Type}
    {kernel : State → Target → Q'}
    {states : List State} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel states targets)
    (row_normalized :
      ∀ source, source ∈ states →
        listQSum (kernel source) targets ≈ 1)
    (first : State) (hfirst : first ∈ states)
    (second : State) (hsecond : second ∈ states)
    (target : Target) (htarget : target ∈ targets) :
    kernel first target ≤
      (certificate.spread * certificate.spread) *
        kernel second target := by
  let square := certificate.spread * certificate.spread
  have hterm :
      ∀ reference,
        reference ∈ targets →
          kernel first target * kernel second reference ≤
            square *
              (kernel first reference * kernel second target) := by
    intro reference hreference
    exact certificate.crossRatioBound
      first hfirst second hsecond
      target htarget reference hreference
  have hsum :=
    listQSum_mono
      (fun reference =>
        kernel first target * kernel second reference)
      (fun reference =>
        square *
          (kernel first reference * kernel second target))
      targets hterm
  have hleft :
      listQSum
          (fun reference =>
            kernel first target * kernel second reference)
          targets ≈
        kernel first target := by
    refine Q'.eqv_trans _
      (kernel first target *
        listQSum (kernel second) targets) _ ?_ ?_
    · exact listQSum_mul_left
        (kernel first target) (kernel second) targets
    exact Q'.eqv_trans _ (kernel first target * 1) _
      (Q'.mul_eqv_congr_left
        (kernel first target) _ _
        (row_normalized second hsecond))
      (Q'.mul_one_eqv _)
  have hright :
      listQSum
          (fun reference =>
            square *
              (kernel first reference * kernel second target))
          targets ≈
        square * kernel second target := by
    refine Q'.eqv_trans _
      ((square * kernel second target) *
        listQSum (kernel first) targets) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun reference =>
            (square * kernel second target) *
              kernel first reference)
          targets) _ ?_ ?_
      · apply listQSum_congr_on
        intro reference _
        ac_qeqv
      · exact listQSum_mul_left
          (square * kernel second target)
          (kernel first) targets
    exact Q'.eqv_trans _
      ((square * kernel second target) * 1) _
      (Q'.mul_eqv_congr_left _ _ _
        (row_normalized first hfirst))
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv hright))

/-! ## 3. Explicit terminal-independent common mass -/

/-- The constructive common mass associated with a squared cross-ratio
spread. -/
def commonMass
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) : Q' :=
  Q'.divPos 1
    (certificate.spread * certificate.spread)
    (Q'.mul_pos certificate.spread_pos certificate.spread_pos)

theorem commonMass_pos
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (0 : Q') < commonMass certificate :=
  Q'.divPos_pos 1
    (certificate.spread * certificate.spread)
    (Q'.mul_pos certificate.spread_pos certificate.spread_pos)
    (by decide)

private theorem spreadSquare_one_le
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    (1 : Q') ≤ certificate.spread * certificate.spread := by
  have hmul := Q'.mul_le_mul_of_nonneg
    certificate.one_le_spread certificate.one_le_spread
    (Q'.le_of_lt certificate.spread_pos) Q'.zero_le_one
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv 1)) hmul

theorem commonMass_le_one
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets) :
    commonMass certificate ≤ (1 : Q') := by
  unfold commonMass
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (spreadSquare_one_le certificate)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (certificate.spread * certificate.spread)))

/-! ## 4. A fixed rational quarter-rate gate -/

/-- The fixed contraction rate used by the physical BF4 overlay. -/
def quarterRate : Q' := Q'.mkPos 1 4 (by decide)

/-- The common-mass threshold complementary to `quarterRate`. -/
def threeQuarterMass : Q' := Q'.mkPos 3 4 (by decide)

/-- A convenient squared-spread ceiling implying common mass at least
three quarters. -/
def fourThirdsSpreadSquare : Q' := Q'.mkPos 4 3 (by decide)

/-- A division-free squared-spread witness gives the fixed common-mass
threshold needed for quarter contraction. -/
theorem commonMass_ge_threeQuarter_of_spreadSquare_le
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate kernel sources targets)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        fourThirdsSpreadSquare) :
    threeQuarterMass ≤ commonMass certificate := by
  unfold commonMass
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left
      (certificate.spread * certificate.spread)
      fourThirdsSpreadSquare threeQuarterMass
      spreadSquare_le (by decide))
    (by decide)

/-- Every backward-message row contains the selected reference row with
common mass `1 / spread^2`, uniformly in the positive terminal message. -/
theorem terminalProjectiveKernel_common_mass
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (reference : Source) (hreference : reference ∈ sourceStates)
    (source : Source) (hsource : source ∈ sourceStates)
    (target : Target) (htarget : target ∈ targetStates) :
    commonMass certificate *
        terminalProjectiveKernel
          targetStates kernel terminal denominator_pos reference target ≤
      terminalProjectiveKernel
        targetStates kernel terminal denominator_pos source target := by
  let normalizedCertificate :=
    terminalNormalize certificate terminal terminal_pos denominator_pos
  have hdom :
      terminalProjectiveKernel
          targetStates kernel terminal denominator_pos reference target ≤
        (certificate.spread * certificate.spread) *
          terminalProjectiveKernel
            targetStates kernel terminal denominator_pos source target := by
    exact rowNormalizedKernel_row_domination
      normalizedCertificate
      (fun row _ =>
        terminalProjectiveKernel_row_normalized
          targetStates kernel terminal denominator_pos row)
      reference hreference source hsource target htarget
  have hquot :
      Q'.divPos
          (terminalProjectiveKernel
            targetStates kernel terminal denominator_pos reference target)
          (certificate.spread * certificate.spread)
          (Q'.mul_pos certificate.spread_pos certificate.spread_pos) ≤
        terminalProjectiveKernel
          targetStates kernel terminal denominator_pos source target := by
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ hdom
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (certificate.spread * certificate.spread)
          (terminalProjectiveKernel
            targetStates kernel terminal denominator_pos source target)))
  refine Q'.le_trans' _ _ _ ?_ hquot
  exact Q'.le_of_eqv (by
    unfold commonMass Q'.divPos
    ac_qeqv)

/-! ## 4. Common mass as an explicit constructive refresh packet -/

/-- Residual kernel obtained by removing a common reference-row packet and
renormalizing the remaining mass. -/
def minorizationResidual
    {Source Target : Type}
    (kernel : Source → Target → Q')
    (reference : Target → Q')
    (epsilon : Q')
    (rate_pos : (0 : Q') < (1 : Q') + -epsilon)
    (source : Source) (target : Target) : Q' :=
  Q'.divPos
    (kernel source target + (-epsilon) * reference target)
    ((1 : Q') + -epsilon) rate_pos

/-- Any exact common-mass minorization constructs the witness-bearing refresh
decomposition consumed by `ConstructiveRefreshContraction`. -/
def refreshCertificateOfMinorization
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (kernel : Source → Target → Q')
    (kernel_nonnegative :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') ≤ kernel source target)
    (row_normalized :
      ∀ source, source ∈ sources →
        listQSum (kernel source) targets ≈ 1)
    (epsilon : Q')
    (epsilon_positive : (0 : Q') < epsilon)
    (epsilon_le_one : epsilon ≤ (1 : Q'))
    (rate_pos : (0 : Q') < (1 : Q') + -epsilon)
    (reference : Target → Q')
    (reference_nonnegative :
      ∀ target, target ∈ targets →
        (0 : Q') ≤ reference target)
    (reference_normalized : listQSum reference targets ≈ 1)
    (minorization :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          epsilon * reference target ≤ kernel source target) :
    FiniteRefreshCertificate sources targets where
  epsilon := epsilon
  epsilon_positive := epsilon_positive
  epsilon_le_one := epsilon_le_one
  reference := reference
  reference_nonnegative := reference_nonnegative
  reference_normalized := reference_normalized
  residual :=
    minorizationResidual kernel reference epsilon rate_pos
  residual_nonnegative := by
    intro source hsource target htarget
    unfold minorizationResidual Q'.divPos
    apply Q'.mul_nonneg
    · have hsub :
          (0 : Q') ≤
            kernel source target +
              -(epsilon * reference target) :=
        Q'.sub_nonneg_of_le
          (minorization source hsource target htarget)
      exact Q'.le_trans' _ _ _ hsub
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_left
            (kernel source target) _ _
            (Q'.eqv_symm
              (Q'.neg_mul_eqv
                epsilon (reference target)))))
    · exact Q'.le_of_lt
        (Q'.recipPos_pos _ rate_pos)
  residual_row_normalized := by
    intro source hsource
    let numerator : Target → Q' := fun target =>
      kernel source target + (-epsilon) * reference target
    let rate : Q' := (1 : Q') + -epsilon
    have hsumNumerator :
        listQSum numerator targets ≈ rate := by
      unfold numerator rate
      refine Q'.eqv_trans _
        (listQSum (kernel source) targets +
          listQSum
            (fun target => (-epsilon) * reference target)
            targets) _ ?_ ?_
      · exact listQSum_add _ _ targets
      refine Q'.eqv_trans _
        (listQSum (kernel source) targets +
          (-epsilon) * listQSum reference targets) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_left
            (-epsilon) reference targets)
      refine Q'.eqv_trans _
        (1 + (-epsilon) * 1) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (row_normalized source hsource)
          (Q'.mul_eqv_congr_left
            (-epsilon) _ _ reference_normalized)
      exact Q'.add_eqv_congr_left 1 _ _
        (Q'.mul_one_eqv (-epsilon))
    unfold minorizationResidual Q'.divPos
    change
      listQSum
          (fun target =>
            numerator target * Q'.recipPos rate rate_pos)
          targets ≈ 1
    refine Q'.eqv_trans _
      (listQSum numerator targets *
        Q'.recipPos rate rate_pos) _ ?_ ?_
    · exact listQSum_mul_right
        numerator (Q'.recipPos rate rate_pos) targets
    refine Q'.eqv_trans _
      (rate * Q'.recipPos rate rate_pos) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hsumNumerator
    · exact Q'.mul_recipPos_eqv rate rate_pos

/-- The constructed refresh packet reconstructs the original kernel
pointwise in the rational setoid. -/
theorem refreshCertificateOfMinorization_kernel_eqv
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (kernel : Source → Target → Q')
    (kernel_nonnegative :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') ≤ kernel source target)
    (row_normalized :
      ∀ source, source ∈ sources →
        listQSum (kernel source) targets ≈ 1)
    (epsilon : Q')
    (epsilon_positive : (0 : Q') < epsilon)
    (epsilon_le_one : epsilon ≤ (1 : Q'))
    (rate_pos : (0 : Q') < (1 : Q') + -epsilon)
    (reference : Target → Q')
    (reference_nonnegative :
      ∀ target, target ∈ targets →
        (0 : Q') ≤ reference target)
    (reference_normalized : listQSum reference targets ≈ 1)
    (minorization :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          epsilon * reference target ≤ kernel source target)
    (source : Source) (target : Target) :
    (refreshCertificateOfMinorization
        sources targets kernel kernel_nonnegative row_normalized
        epsilon epsilon_positive epsilon_le_one rate_pos
        reference reference_nonnegative reference_normalized
        minorization).kernel source target ≈
      kernel source target := by
  let rate : Q' := (1 : Q') + -epsilon
  let numerator : Q' :=
    kernel source target + (-epsilon) * reference target
  have hresidual :
      rate * Q'.divPos numerator rate rate_pos ≈ numerator := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv rate
        (Q'.divPos numerator rate rate_pos))
      (Q'.divPos_mul_eqv numerator rate rate_pos)
  unfold FiniteRefreshCertificate.kernel
    FiniteRefreshCertificate.rate
    refreshCertificateOfMinorization minorizationResidual
  change
    epsilon * reference target +
        rate * Q'.divPos numerator rate rate_pos ≈
      kernel source target
  refine Q'.eqv_trans _
    (epsilon * reference target + numerator) _
    (Q'.add_eqv_congr_left _ _ _ hresidual) ?_
  unfold numerator
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv
        (epsilon * reference target)
        (kernel source target)
        ((-epsilon) * reference target))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_comm_eqv
        (epsilon * reference target)
        (kernel source target))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      (kernel source target)
      (epsilon * reference target)
      ((-epsilon) * reference target)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (kernel source target) _ _
      (Q'.add_eqv_congr_left (epsilon * reference target) _ _
        (Q'.neg_mul_eqv epsilon (reference target)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (kernel source target) _ _
      (Q'.add_neg_self_eqv (epsilon * reference target))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (kernel source target))

/-- A strict common mass turns the terminal-normalized projective kernel into
an explicit refresh certificate.  The only strictness assumption excludes
the degenerate spread-one case, where all normalized rows already coincide. -/
def terminalProjectiveRefreshCertificate
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (commonMass_lt_one : commonMass certificate < (1 : Q'))
    (reference : Source) (hreference : reference ∈ sourceStates) :
    FiniteRefreshCertificate sourceStates targetStates := by
  let normalized :=
    terminalProjectiveKernel
      targetStates kernel terminal denominator_pos
  let normalizedCertificate :=
    terminalNormalize certificate terminal terminal_pos denominator_pos
  let referenceRow : Target → Q' := normalized reference
  exact refreshCertificateOfMinorization
    sourceStates targetStates normalized
    (fun source hsource target htarget =>
      Q'.le_of_lt
        (normalizedCertificate.strictlyPositive
          source hsource target htarget))
    (fun source _ =>
      terminalProjectiveKernel_row_normalized
        targetStates kernel terminal denominator_pos source)
    (commonMass certificate)
    (commonMass_pos certificate)
    (commonMass_le_one certificate)
    (YMGap.Continuum.HKPos.one_sub_pos commonMass_lt_one)
    referenceRow
    (fun target htarget =>
      Q'.le_of_lt
        (normalizedCertificate.strictlyPositive
          reference hreference target htarget))
    (terminalProjectiveKernel_row_normalized
      targetStates kernel terminal denominator_pos reference)
    (fun source hsource target htarget =>
      terminalProjectiveKernel_common_mass
        certificate terminal terminal_pos denominator_pos
        reference hreference source hsource target htarget)

/-- The terminal refresh packet reconstructs the normalized boundary-message
kernel pointwise. -/
theorem terminalProjectiveRefreshCertificate_kernel_eqv
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (commonMass_lt_one : commonMass certificate < (1 : Q'))
    (reference : Source) (hreference : reference ∈ sourceStates)
    (source : Source) (target : Target) :
    (terminalProjectiveRefreshCertificate
        certificate terminal terminal_pos denominator_pos
        commonMass_lt_one reference hreference).kernel source target ≈
      terminalProjectiveKernel
        targetStates kernel terminal denominator_pos source target := by
  let normalized :=
    terminalProjectiveKernel
      targetStates kernel terminal denominator_pos
  let normalizedCertificate :=
    terminalNormalize certificate terminal terminal_pos denominator_pos
  let referenceRow : Target → Q' := normalized reference
  exact refreshCertificateOfMinorization_kernel_eqv
    sourceStates targetStates normalized
    (fun s hs t ht =>
      Q'.le_of_lt
        (normalizedCertificate.strictlyPositive s hs t ht))
    (fun s _ =>
      terminalProjectiveKernel_row_normalized
        targetStates kernel terminal denominator_pos s)
    (commonMass certificate)
    (commonMass_pos certificate)
    (commonMass_le_one certificate)
    (YMGap.Continuum.HKPos.one_sub_pos commonMass_lt_one)
    referenceRow
    (fun t ht =>
      Q'.le_of_lt
        (normalizedCertificate.strictlyPositive
          reference hreference t ht))
    (terminalProjectiveKernel_row_normalized
      targetStates kernel terminal denominator_pos reference)
    (fun s hs t ht =>
      terminalProjectiveKernel_common_mass
        certificate terminal terminal_pos denominator_pos
        reference hreference s hs t ht)
    source target

/-- The explicit terminal refresh packet contracts all equal-mass source
weights by `1 - 1/spread^2`. -/
theorem terminalProjectiveRefresh_l1_contraction
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (commonMass_lt_one : commonMass certificate < (1 : Q'))
    (reference : Source) (hreference : reference ∈ sourceStates)
    (left right : Source → Q')
    (equalMass :
      finiteMass sourceStates left ≈ finiteMass sourceStates right) :
    let refresh :=
      terminalProjectiveRefreshCertificate
        certificate terminal terminal_pos denominator_pos
        commonMass_lt_one reference hreference
    finiteL1Distance targetStates
        (finiteKernelPushforward sourceStates left refresh.kernel)
        (finiteKernelPushforward sourceStates right refresh.kernel) ≤
      refresh.rate *
        finiteL1Distance sourceStates left right := by
  dsimp only
  exact FiniteRefreshCertificate.l1_contraction _ _ _ equalMass

/-- Any explicit refresh packet with common mass at least three quarters has
residual rate at most one quarter. -/
theorem finiteRefresh_rate_le_quarter
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (refresh : FiniteRefreshCertificate sources targets)
    (threeQuarter_le : threeQuarterMass ≤ refresh.epsilon) :
    refresh.rate ≤ quarterRate := by
  unfold FiniteRefreshCertificate.rate
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (1 : Q') _ _
      (Q'.neg_le_neg threeQuarter_le))
    (by decide)

/-- The squared-spread ceiling turns every positive terminal boundary
message into an explicit refresh packet of rate at most one quarter. -/
theorem terminalProjectiveRefresh_rate_le_quarter
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (commonMass_lt_one : commonMass certificate < (1 : Q'))
    (reference : Source) (hreference : reference ∈ sourceStates)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        fourThirdsSpreadSquare) :
    (terminalProjectiveRefreshCertificate
        certificate terminal terminal_pos denominator_pos
        commonMass_lt_one reference hreference).rate ≤
      quarterRate := by
  apply finiteRefresh_rate_le_quarter
  change threeQuarterMass ≤ commonMass certificate
  exact commonMass_ge_threeQuarter_of_spreadSquare_le
    certificate spreadSquare_le

/-- Uniform quarter contraction of equal-mass finite boundary weights. -/
theorem terminalProjectiveRefresh_l1_quarter_contraction
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sourceStates : List Source} {targetStates : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sourceStates targetStates)
    (terminal : Target → Q')
    (terminal_pos :
      ∀ target, target ∈ targetStates →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (commonMass_lt_one : commonMass certificate < (1 : Q'))
    (reference : Source) (hreference : reference ∈ sourceStates)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        fourThirdsSpreadSquare)
    (left right : Source → Q')
    (equalMass :
      finiteMass sourceStates left ≈ finiteMass sourceStates right) :
    let refresh :=
      terminalProjectiveRefreshCertificate
        certificate terminal terminal_pos denominator_pos
        commonMass_lt_one reference hreference
    finiteL1Distance targetStates
        (finiteKernelPushforward sourceStates left refresh.kernel)
        (finiteKernelPushforward sourceStates right refresh.kernel) ≤
      quarterRate *
        finiteL1Distance sourceStates left right := by
  dsimp only
  refine Q'.le_trans' _ _ _
    (terminalProjectiveRefresh_l1_contraction
      certificate terminal terminal_pos denominator_pos
      commonMass_lt_one reference hreference
      left right equalMass) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (terminalProjectiveRefresh_rate_le_quarter
      certificate terminal terminal_pos denominator_pos
      commonMass_lt_one reference hreference spreadSquare_le)
    (finiteL1Distance_nonnegative sourceStates left right)

/-! ## 5. Uniform proof-carrying computation interface -/

/-- A compact uniform witness contract for a family of finite physical raw
kernels.  Heavy exact enumeration may construct the data, but Lean consumes
the literal rational kernel together with positivity and division-free
cross-ratio proofs.  No sampler or external executable is trusted.

The explicit reference state prevents a vacuous empty source carrier.  The
strict common-mass field only excludes the spread-one case, whose normalized
rows coincide and can be handled separately without dividing by a residual
rate. -/
structure UniformBoundaryMessageQuarterCertificate
    (Index : Type)
    (Source Target : Index → Type)
    (kernel : ∀ index, Source index → Target index → Q')
    (sources : ∀ index, List (Source index))
    (targets : ∀ index, List (Target index)) : Type where
  crossRatio :
    UniformCrossRatioDiameterCertificate
      Index Source Target kernel sources targets
  spreadSquare_le :
    crossRatio.spread * crossRatio.spread ≤ fourThirdsSpreadSquare
  commonMass_lt_one :
    ∀ index, commonMass (crossRatio.atIndex index) < (1 : Q')
  reference : ∀ index, Source index
  reference_mem : ∀ index, reference index ∈ sources index

namespace UniformBoundaryMessageQuarterCertificate

/-- Construct the exact refresh packet at one regulator and for an arbitrary
strictly positive terminal boundary message. -/
def refreshAt
    {Index : Type}
    {Source Target : Index → Type}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Index Source Target kernel sources targets)
    (index : Index)
    (terminal : Target index → Q')
    (terminal_pos :
      ∀ target, target ∈ targets index →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            (targets index) (kernel index) terminal source) :
    FiniteRefreshCertificate (sources index) (targets index) :=
  terminalProjectiveRefreshCertificate
    (certificate.crossRatio.atIndex index)
    terminal terminal_pos denominator_pos
    (certificate.commonMass_lt_one index)
    (certificate.reference index)
    (certificate.reference_mem index)

/-- The proof-carrying uniform packet reconstructs the actual normalized
boundary-message kernel pointwise. -/
theorem refreshAt_kernel_eqv
    {Index : Type}
    {Source Target : Index → Type}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Index Source Target kernel sources targets)
    (index : Index)
    (terminal : Target index → Q')
    (terminal_pos :
      ∀ target, target ∈ targets index →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            (targets index) (kernel index) terminal source)
    (source : Source index) (target : Target index) :
    (certificate.refreshAt index terminal terminal_pos denominator_pos).kernel
        source target ≈
      terminalProjectiveKernel
        (targets index) (kernel index) terminal denominator_pos
        source target := by
  exact terminalProjectiveRefreshCertificate_kernel_eqv
    (certificate.crossRatio.atIndex index)
    terminal terminal_pos denominator_pos
    (certificate.commonMass_lt_one index)
    (certificate.reference index)
    (certificate.reference_mem index)
    source target

/-- Every regulator and every positive terminal message has rate at most one
quarter from the same uniform raw-kernel witness. -/
theorem refreshAt_rate_le_quarter
    {Index : Type}
    {Source Target : Index → Type}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Index Source Target kernel sources targets)
    (index : Index)
    (terminal : Target index → Q')
    (terminal_pos :
      ∀ target, target ∈ targets index →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            (targets index) (kernel index) terminal source) :
    (certificate.refreshAt index terminal terminal_pos denominator_pos).rate ≤
      quarterRate := by
  exact terminalProjectiveRefresh_rate_le_quarter
    (certificate.crossRatio.atIndex index)
    terminal terminal_pos denominator_pos
    (certificate.commonMass_lt_one index)
    (certificate.reference index)
    (certificate.reference_mem index)
    certificate.spreadSquare_le

/-- Uniform exact quarter contraction for every regulator, terminal message,
and pair of equal-mass source weights. -/
theorem refreshAt_l1_quarter_contraction
    {Index : Type}
    {Source Target : Index → Type}
    {kernel : ∀ index, Source index → Target index → Q'}
    {sources : ∀ index, List (Source index)}
    {targets : ∀ index, List (Target index)}
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Index Source Target kernel sources targets)
    (index : Index)
    (terminal : Target index → Q')
    (terminal_pos :
      ∀ target, target ∈ targets index →
        (0 : Q') < terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            (targets index) (kernel index) terminal source)
    (left right : Source index → Q')
    (equalMass :
      finiteMass (sources index) left ≈
        finiteMass (sources index) right) :
    finiteL1Distance (targets index)
        (finiteKernelPushforward (sources index) left
          (certificate.refreshAt
            index terminal terminal_pos denominator_pos).kernel)
        (finiteKernelPushforward (sources index) right
          (certificate.refreshAt
            index terminal terminal_pos denominator_pos).kernel) ≤
      quarterRate * finiteL1Distance (sources index) left right := by
  exact terminalProjectiveRefresh_l1_quarter_contraction
    (certificate.crossRatio.atIndex index)
    terminal terminal_pos denominator_pos
    (certificate.commonMass_lt_one index)
    (certificate.reference index)
    (certificate.reference_mem index)
    certificate.spreadSquare_le
    left right equalMass

end UniformBoundaryMessageQuarterCertificate

end YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh

#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveKernel_eqv_terminalNormalizedKernel
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalNormalize
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveKernel_row_normalized
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.rowNormalizedKernel_row_domination
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.commonMass_pos
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.commonMass_le_one
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.commonMass_ge_threeQuarter_of_spreadSquare_le
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveKernel_common_mass
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.refreshCertificateOfMinorization
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.refreshCertificateOfMinorization_kernel_eqv
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefreshCertificate
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefreshCertificate_kernel_eqv
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefresh_l1_contraction
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.finiteRefresh_rate_le_quarter
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefresh_rate_le_quarter
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefresh_l1_quarter_contraction
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.UniformBoundaryMessageQuarterCertificate.refreshAt
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.UniformBoundaryMessageQuarterCertificate.refreshAt_kernel_eqv
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.UniformBoundaryMessageQuarterCertificate.refreshAt_rate_le_quarter
#print axioms YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh.UniformBoundaryMessageQuarterCertificate.refreshAt_l1_quarter_contraction
