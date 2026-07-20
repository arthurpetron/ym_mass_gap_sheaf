/-
# Ordered-associator convention for the four-valent channel basis

The signed rational channel action is

    F = [[-1/2, 3/2], [1/2, 1/2]]

on the dimension-rescaled `(singlet,triplet)` column carrier.  The repository's
fixed-output forward coefficients instead list *left inputs as rows* and
*right outputs as columns*.  Their induced column-coordinate action is
therefore `Fᵀ`.  The concrete Schur coefficient represents the inverse ordered
associator with left outputs as rows and right inputs as columns; its table is
also `Fᵀ`.

This is not an accidental symmetry.  The channel Gram is `G = diag(1,3)`,
`F² = I`, and

    Fᵀ = G F G⁻¹.

Equivalently, if `lower(s,t) = (s,3t)`, the ordered coefficient action on
lowered coordinates intertwines the rational channel action:

    Fᵀ (lower x) ≈ lower (F x).

The ordered fixed-channel weights are `diag(4,12) = 4G`; the common factor
four cancels from probability ratios, while the `1:3` channel ratio cannot be
dropped.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
Only the two-channel tables and symbolic two-coordinate identities occur.
-/

import YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization
import YMGap.Continuum.SU2OrderedRacahMultiplicityFence
import YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge

namespace YMGap.Continuum.SU2QuaternionFourValentOrderedAssociatorBridge

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

open YMGap.Constructive
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Exact finite carrier order -/

/-- `false` is the singlet and `true` is the triplet on the left carrier. -/
def fundamentalFixedLeftChannel : Bool → FixedLeftCGChannel 1 1 1 1
  | false => fundamentalFixedLeftSinglet
  | true => fundamentalFixedLeftTriplet

/-- The same Boolean order on the right carrier. -/
def fundamentalFixedRightChannel : Bool → FixedRightCGChannel 1 1 1 1
  | false => fundamentalFixedRightSinglet
  | true => fundamentalFixedRightTriplet

def fundamentalRecoupleChannel : Bool → RecoupleVec
  | false => singletChannel
  | true => tripletChannel

/-- Both fixed carriers use intermediate label `0` for the singlet and `2`
for the triplet. -/
theorem fundamental_fixed_channel_intermediates_exact :
    fundamentalFixedLeftSinglet.intermediate = 0 ∧
    fundamentalFixedLeftTriplet.intermediate = 2 ∧
    fundamentalFixedRightSinglet.intermediate = 0 ∧
    fundamentalFixedRightTriplet.intermediate = 2 := by
  decide

/-! ## 2. Forward and inverse coefficient tables -/

/-- Forward fixed-output coefficient table.  Its arguments retain the
repository semantics `(left input, right output)`. -/
def fundamentalOrderedForwardEntry (leftInput rightOutput : Bool) : Q' :=
  fixedOrderedFCoefficient
    (fundamentalFixedLeftChannel leftInput)
    (fundamentalFixedRightChannel rightOutput)

/-- The inverse Schur table, indexed as `(left output, right input)`. -/
def fundamentalOrderedInverseSchurEntry
    (leftOutput rightInput : Bool) : Q' :=
  fixedLeftRightDiagonalCoeff
    (fundamentalFixedLeftChannel leftOutput)
    (fundamentalFixedRightChannel rightInput) 0

/-- The raw forward table, in singlet/triplet order. -/
theorem fundamentalOrderedForwardEntry_exact :
    fundamentalOrderedForwardEntry false false ≈ -oneHalf ∧
    fundamentalOrderedForwardEntry false true ≈ threeHalves ∧
    fundamentalOrderedForwardEntry true false ≈ oneHalf ∧
    fundamentalOrderedForwardEntry true true ≈ oneHalf := by
  simp only [fundamentalOrderedForwardEntry, fundamentalFixedLeftChannel,
    fundamentalFixedRightChannel]
  exact
    ⟨Q'.eqv_trans _ (-fundamentalHalf) _
        fundamental_fixedF_entries.1 (by decide),
      Q'.eqv_trans _ fundamentalThreeHalves _
        fundamental_fixedF_entries.2.1 (by decide),
      Q'.eqv_trans _ fundamentalHalf _
        fundamental_fixedF_entries.2.2.1 (by decide),
      Q'.eqv_trans _ fundamentalHalf _
        fundamental_fixedF_entries.2.2.2 (by decide)⟩

/-- The Schur inverse table is the transpose of the forward table. -/
theorem fundamentalOrderedInverseSchurEntry_exact :
    fundamentalOrderedInverseSchurEntry false false ≈ -oneHalf ∧
    fundamentalOrderedInverseSchurEntry false true ≈ oneHalf ∧
    fundamentalOrderedInverseSchurEntry true false ≈ threeHalves ∧
    fundamentalOrderedInverseSchurEntry true true ≈ oneHalf := by
  simp only [fundamentalOrderedInverseSchurEntry,
    fundamentalFixedLeftChannel, fundamentalFixedRightChannel]
  exact
    ⟨Q'.eqv_trans _ (-fundamentalHalf) _
        fundamental_schurCoeff_entries.1 (by decide),
      Q'.eqv_trans _ fundamentalHalf _
        fundamental_schurCoeff_entries.2.1 (by decide),
      Q'.eqv_trans _ fundamentalThreeHalves _
        fundamental_schurCoeff_entries.2.2.1 (by decide),
      Q'.eqv_trans _ fundamentalHalf _
        fundamental_schurCoeff_entries.2.2.2 (by decide)⟩

/-- **Exact transpose convention.**  The inverse entry with semantic indices
`(left output,right input)` equals the forward entry with those semantic
indices exchanged. -/
theorem fundamental_inverseSchurEntry_eq_forward_transpose
    (leftOutput rightInput : Bool) :
    fundamentalOrderedInverseSchurEntry leftOutput rightInput ≈
      fundamentalOrderedForwardEntry rightInput leftOutput := by
  cases leftOutput <;> cases rightInput
  · exact Q'.eqv_trans _ (-oneHalf) _
      fundamentalOrderedInverseSchurEntry_exact.1
      (Q'.eqv_symm fundamentalOrderedForwardEntry_exact.1)
  · exact Q'.eqv_trans _ oneHalf _
      fundamentalOrderedInverseSchurEntry_exact.2.1
      (Q'.eqv_symm fundamentalOrderedForwardEntry_exact.2.2.1)
  · exact Q'.eqv_trans _ threeHalves _
      fundamentalOrderedInverseSchurEntry_exact.2.2.1
      (Q'.eqv_symm fundamentalOrderedForwardEntry_exact.2.1)
  · exact Q'.eqv_trans _ oneHalf _
      fundamentalOrderedInverseSchurEntry_exact.2.2.2
      (Q'.eqv_symm fundamentalOrderedForwardEntry_exact.2.2.2)

/-- The raw ordered table is exactly the signed `fundamentalFMove` matrix,
but its first semantic index is the left input whereas a column-action matrix
reads that same position as the output row.  This theorem pins all four
placements rather than identifying only unsigned squares. -/
theorem fundamental_ordered_forward_entries_match_fmove :
    fundamentalOrderedForwardEntry false false ≈
        (fundamentalFMove singletChannel).1 ∧
    fundamentalOrderedForwardEntry true false ≈
        (fundamentalFMove singletChannel).2 ∧
    fundamentalOrderedForwardEntry false true ≈
        (fundamentalFMove tripletChannel).1 ∧
    fundamentalOrderedForwardEntry true true ≈
        (fundamentalFMove tripletChannel).2 := by
  exact
    ⟨Q'.eqv_trans _ (-oneHalf) _
        fundamentalOrderedForwardEntry_exact.1
        (Q'.eqv_symm fundamentalFMove_basis_exact.1.1),
      Q'.eqv_trans _ oneHalf _
        fundamentalOrderedForwardEntry_exact.2.2.1
        (Q'.eqv_symm fundamentalFMove_basis_exact.1.2),
      Q'.eqv_trans _ threeHalves _
        fundamentalOrderedForwardEntry_exact.2.1
        (Q'.eqv_symm fundamentalFMove_basis_exact.2.1),
      Q'.eqv_trans _ oneHalf _
        fundamentalOrderedForwardEntry_exact.2.2.2
        (Q'.eqv_symm fundamentalFMove_basis_exact.2.2)⟩

/-! ## 3. Genuine ordered coordinate actions and Gram lowering -/

/-- Column-coordinate action induced by the semantic forward table: sum over
the left-input row while retaining the right-output column. -/
def orderedForwardRecoupleAction (x : RecoupleVec) : RecoupleVec :=
  (fundamentalOrderedForwardEntry false false * x.1 +
      fundamentalOrderedForwardEntry true false * x.2,
    fundamentalOrderedForwardEntry false true * x.1 +
      fundamentalOrderedForwardEntry true true * x.2)

/-- Column action of the inverse Schur table. -/
def orderedInverseRecoupleAction (x : RecoupleVec) : RecoupleVec :=
  (fundamentalOrderedInverseSchurEntry false false * x.1 +
      fundamentalOrderedInverseSchurEntry false true * x.2,
    fundamentalOrderedInverseSchurEntry true false * x.1 +
      fundamentalOrderedInverseSchurEntry true true * x.2)

/-- Lower channel coordinates by the exact Gram `diag(1,3)`. -/
def recoupleGramLower (x : RecoupleVec) : RecoupleVec :=
  (x.1, Q'.ofNat 3 * x.2)

/-- **Carrier intertwiner `Fᵀ G = G F`.**  This is the exact mathematical
reason the ordered coefficient action is the transpose of the rational
channel action. -/
theorem ordered_forward_action_gram_intertwines_fmove (x : RecoupleVec) :
    RecoupleEq
      (orderedForwardRecoupleAction (recoupleGramLower x))
      (recoupleGramLower (fundamentalFMove x)) := by
  unfold RecoupleEq orderedForwardRecoupleAction recoupleGramLower
  constructor
  · refine Q'.eqv_trans _
      ((-oneHalf) * x.1 +
        oneHalf * (Q'.ofNat 3 * x.2)) _ ?_ ?_
    · exact q_add_congr
        (q_mul_congr fundamentalOrderedForwardEntry_exact.1
          (Q'.eqv_refl x.1))
        (q_mul_congr fundamentalOrderedForwardEntry_exact.2.2.1
          (Q'.eqv_refl (Q'.ofNat 3 * x.2)))
    · unfold fundamentalFMove fundamentalFMoveAt oneHalf
      ring_qeqv
  · refine Q'.eqv_trans _
      (threeHalves * x.1 +
        oneHalf * (Q'.ofNat 3 * x.2)) _ ?_ ?_
    · exact q_add_congr
        (q_mul_congr fundamentalOrderedForwardEntry_exact.2.1
          (Q'.eqv_refl x.1))
        (q_mul_congr fundamentalOrderedForwardEntry_exact.2.2.2
          (Q'.eqv_refl (Q'.ofNat 3 * x.2)))
    · unfold fundamentalFMove fundamentalFMoveAt oneHalf threeHalves
      ring_qeqv

/-- The actual inverse table and the semantic forward table induce the same
column action.  Together with `fundamentalFMove_involutive`, this pins the
repository convention as inverse-transpose, not as an unweighted orthogonal
transpose. -/
theorem ordered_inverse_action_eq_forward_action (x : RecoupleVec) :
    RecoupleEq
      (orderedInverseRecoupleAction x)
      (orderedForwardRecoupleAction x) := by
  unfold RecoupleEq orderedInverseRecoupleAction orderedForwardRecoupleAction
  constructor
  · exact q_add_congr
      (q_mul_congr
        (fundamental_inverseSchurEntry_eq_forward_transpose false false)
        (Q'.eqv_refl x.1))
      (q_mul_congr
        (fundamental_inverseSchurEntry_eq_forward_transpose false true)
        (Q'.eqv_refl x.2))
  · exact q_add_congr
      (q_mul_congr
        (fundamental_inverseSchurEntry_eq_forward_transpose true false)
        (Q'.eqv_refl x.1))
      (q_mul_congr
        (fundamental_inverseSchurEntry_eq_forward_transpose true true)
        (Q'.eqv_refl x.2))

/-! ## 4. The actual inverse associator and the probability normalization -/

/-- The genuine inverse ordered-associator entry on the fixed fundamental
carrier. -/
def fundamentalOrderedAssociatorInvEntry
    (leftOutput rightInput : Bool) : Q' :=
  orderedAllLabelAssociatorInv 1 1 1
    (fixedRightOrderedBasisVector
      (fundamentalFixedRightChannel rightInput) 0)
    (fixedLeftNestedChannel
      (fundamentalFixedLeftChannel leftOutput) 0 (by decide))

theorem fundamentalOrderedAssociatorInvEntry_eq_inverseSchurEntry
    (leftOutput rightInput : Bool) :
    fundamentalOrderedAssociatorInvEntry leftOutput rightInput ≈
      fundamentalOrderedInverseSchurEntry leftOutput rightInput := by
  unfold fundamentalOrderedAssociatorInvEntry
    fundamentalOrderedInverseSchurEntry
  exact orderedAssociatorInv_entry_eq_schurCoeff
    (fundamentalFixedLeftChannel leftOutput)
    (fundamentalFixedRightChannel rightInput) 0 (by decide)

/-- The actual inverse associator entry is the forward coefficient with
exchanged semantic indices. -/
theorem fundamentalOrderedAssociatorInvEntry_eq_forward_transpose
    (leftOutput rightInput : Bool) :
    fundamentalOrderedAssociatorInvEntry leftOutput rightInput ≈
      fundamentalOrderedForwardEntry rightInput leftOutput :=
  Q'.eqv_trans _ _ _
    (fundamentalOrderedAssociatorInvEntry_eq_inverseSchurEntry
      leftOutput rightInput)
    (fundamental_inverseSchurEntry_eq_forward_transpose
      leftOutput rightInput)

/-- The ordered fixed-channel Gram is exactly the common factor four times
the channel Gram `diag(1,3)`. -/
theorem fundamental_ordered_weights_eq_four_times_channel_gram :
    triLeftChannelWeight 1 1 1 1 0 ≈
        Q'.ofNat 4 * recoupleGram singletChannel singletChannel ∧
    triLeftChannelWeight 1 1 1 1 2 ≈
        Q'.ofNat 4 * recoupleGram tripletChannel tripletChannel ∧
    triRightChannelWeight 1 1 1 1 0 ≈
        Q'.ofNat 4 * recoupleGram singletChannel singletChannel ∧
    triRightChannelWeight 1 1 1 1 2 ≈
        Q'.ofNat 4 * recoupleGram tripletChannel tripletChannel := by
  unfold recoupleGram singletChannel tripletChannel
  decide

/-- The factorial Racah kernel and the independently defined recoupling
probability agree entrywise on the complete fundamental block. -/
theorem fundamental_factorialRacah_eq_recouple_probability :
    racahKernel6 1 1 1 1 0 0 ≈ fundamentalRacahProb 0 0 ∧
    racahKernel6 1 1 1 1 0 2 ≈ fundamentalRacahProb 0 1 ∧
    racahKernel6 1 1 1 1 2 0 ≈ fundamentalRacahProb 1 0 ∧
    racahKernel6 1 1 1 1 2 2 ≈ fundamentalRacahProb 1 1 := by
  exact
    ⟨Q'.eqv_trans _ _ _ fundamental_racahKernel_entries.1
        (Q'.eqv_symm fundamentalRacahProb_exact.1),
      Q'.eqv_trans _ _ _ fundamental_racahKernel_entries.2.1
        (Q'.eqv_symm fundamentalRacahProb_exact.2.1),
      Q'.eqv_trans _ _ _ fundamental_racahKernel_entries.2.2.1
        (Q'.eqv_symm fundamentalRacahProb_exact.2.2.1),
      Q'.eqv_trans _ _ _ fundamental_racahKernel_entries.2.2.2
        (Q'.eqv_symm fundamentalRacahProb_exact.2.2.2)⟩

/-- Division-free weighted-square normalization of every forward entry. -/
theorem fundamental_ordered_forward_gramWeighted_probabilities :
    GramWeightedRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    GramWeightedRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    GramWeightedRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    GramWeightedRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet :=
  fundamental_gramWeighted_bridges

#print axioms fundamental_fixed_channel_intermediates_exact
#print axioms fundamentalOrderedForwardEntry_exact
#print axioms fundamentalOrderedInverseSchurEntry_exact
#print axioms fundamental_inverseSchurEntry_eq_forward_transpose
#print axioms fundamental_ordered_forward_entries_match_fmove
#print axioms ordered_forward_action_gram_intertwines_fmove
#print axioms ordered_inverse_action_eq_forward_action
#print axioms fundamentalOrderedAssociatorInvEntry_eq_forward_transpose
#print axioms fundamental_ordered_weights_eq_four_times_channel_gram
#print axioms fundamental_factorialRacah_eq_recouple_probability
#print axioms fundamental_ordered_forward_gramWeighted_probabilities

end YMGap.Continuum.SU2QuaternionFourValentOrderedAssociatorBridge
