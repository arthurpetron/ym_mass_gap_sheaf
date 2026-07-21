/-
# Cutoff-one local positive-channel mass ledger

The global factored trace bound needs one uniform channel tag even though the
local invariant tensors live in Boolean dimensions zero, two, four, and six.
This leaf supplies that tag and freezes the exact local choice list for every
branch of the total cutoff-one Haar dispatcher.

Every displayed channel has nonnegative inverse-Gram weight and exactly one
unit of weighted symbolic norm.  Consequently the structural `listQSum` of
local channel masses is exactly the dispatcher invariant multiplicity
`1,0,1,0,2,0,5`, which is independently identified with the production
geometric multiplicity table.

No global channel product or Boolean assignment family is formed here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor
import YMGap.Continuum.FactoredPositiveChannelTraceBound
import YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
import YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

namespace YMGap.Continuum.SU2QuaternionCutoffOneLocalChannelMass

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.PositiveChannelTraceBound
open YMGap.Continuum.FactoredPositiveChannelTraceBound
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
open YMGap.Continuum.SU2QuaternionFourValentOperatorKernel
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionSixValentOperatorKernel
open YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge
open YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor
open YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One uniform local channel carrier -/

/-- A tagged disjoint union of all local positive channels needed at
cutoff one.  The payload types retain the frozen four- and six-valent channel
orders from their audited operator kernels. -/
inductive CutoffOneLocalChannel where
  | vacuum
  | bivalent
  | fourValent (channel : FourValentOperatorBoolChannel)
  | sixValent (channel : SixValentTLChannel)
  deriving DecidableEq

/-- Exact local channel choices selected by one total dispatcher word.
Odd-valent Haar words have no channels because their local Haar value is
zero. -/
def cutoffOneLocalChannelChoices :
    CutoffOneHaarWord → List CutoffOneLocalChannel
  | .v0 => [.vacuum]
  | .v1 _ => []
  | .v2 _ _ => [.bivalent]
  | .v3 _ _ _ => []
  | .v4 _ _ _ _ =>
      [.fourValent .singlet, .fourValent .triplet]
  | .v5 _ _ _ _ _ => []
  | .v6 _ _ _ _ _ _ =>
      [.sixValent .spinThreeHalves,
       .sixValent .leftA,
       .sixValent .leftB,
       .sixValent .leftX,
       .sixValent .leftY]

/-- The choice count is definitionally the dispatcher invariant-sector
multiplicity in every one of the seven valence branches. -/
theorem cutoffOneLocalChannelChoices_length
    (word : CutoffOneHaarWord) :
    (cutoffOneLocalChannelChoices word).length =
      invariantMultiplicity word := by
  cases word <;> rfl

/-- Explicit audit that all three odd branches carry the empty choice list. -/
theorem cutoffOneLocalChannelChoices_odd_empty
    (first second third fourth fifth : FundamentalOccurrence) :
    cutoffOneLocalChannelChoices (.v1 first) = [] ∧
      cutoffOneLocalChannelChoices (.v3 first second third) = [] ∧
      cutoffOneLocalChannelChoices
        (.v5 first second third fourth fifth) = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## 2. Exact weight and symbolic norm -/

/-- Positive inverse-Gram coefficient of one tagged local channel. -/
def cutoffOneLocalChannelWeight : CutoffOneLocalChannel → Q'
  | .vacuum => 1
  | .bivalent => bivalentInvariantChannelWeight
  | .fourValent channel => fourValentOperatorBoolChannelWeight channel
  | .sixValent channel => sixValentTLChannelInverseWeight channel

/-- Squared symbolic norm of one tagged local channel.  The non-vacuum
branches are the actual recursive Boolean-tensor contractions, not merely
their already-computed numerical values. -/
def cutoffOneLocalChannelNorm : CutoffOneLocalChannel → Q'
  | .vacuum => 1
  | .bivalent =>
      boolTensorDot 2 bivalentInvariantDeltaBoolTensor
        bivalentInvariantDeltaBoolTensor
  | .fourValent channel =>
      boolTensorDot 4
        (fourValentOperatorChannelBoolTensor channel)
        (fourValentOperatorChannelBoolTensor channel)
  | .sixValent channel =>
      boolTensorDot 6
        (sixValentOperatorChannelBoolTensor channel)
        (sixValentOperatorChannelBoolTensor channel)

/-- Every local inverse-Gram weight is nonnegative. -/
theorem cutoffOneLocalChannelWeight_nonneg
    (channel : CutoffOneLocalChannel) :
    (0 : Q') ≤ cutoffOneLocalChannelWeight channel := by
  cases channel with
  | vacuum => decide
  | bivalent =>
      unfold cutoffOneLocalChannelWeight bivalentInvariantChannelWeight
      decide
  | fourValent channel =>
      exact fourValentOperatorBoolChannelWeight_nonneg channel
  | sixValent channel =>
      exact Q'.le_of_lt
        (sixValentOperatorChannelInverseWeight_positive channel)

/-- **Unit local mass.**  Each tagged channel contributes exactly one unit
of inverse-Gram-weighted symbolic norm. -/
theorem cutoffOneLocalChannel_weighted_norm_exact
    (channel : CutoffOneLocalChannel) :
    cutoffOneLocalChannelWeight channel *
        cutoffOneLocalChannelNorm channel ≈ 1 := by
  cases channel with
  | vacuum => decide
  | bivalent =>
      exact bivalentInvariantDeltaBoolTensor_weighted_norm_exact
  | fourValent channel =>
      exact fourValentOperatorChannelBoolTensor_weighted_norm_exact channel
  | sixValent channel =>
      exact sixValentOperatorChannelBoolTensor_weighted_norm_exact channel

/-- Membership-specialized form used by the factored global resolution. -/
theorem cutoffOneLocalChannel_mem_weighted_norm_exact
    {word : CutoffOneHaarWord} {channel : CutoffOneLocalChannel}
    (_ : channel ∈ cutoffOneLocalChannelChoices word) :
    cutoffOneLocalChannelWeight channel *
        cutoffOneLocalChannelNorm channel ≈ 1 :=
  cutoffOneLocalChannel_weighted_norm_exact channel

/-! ## 3. Structural local mass -/

/-- The exact positive Gram mass of one local dispatcher branch. -/
def cutoffOneLocalChannelMass (word : CutoffOneHaarWord) : Q' :=
  listQSum
    (fun channel =>
      cutoffOneLocalChannelWeight channel *
        cutoffOneLocalChannelNorm channel)
    (cutoffOneLocalChannelChoices word)

/-- The structural channel mass is exactly the dispatcher multiplicity.
Only the at-most-five-element local choice list is reduced; the Boolean
tensors inside each norm remain opaque behind their weighted-norm theorem. -/
theorem cutoffOneLocalChannelMass_eqv_invariantMultiplicity
    (word : CutoffOneHaarWord) :
    cutoffOneLocalChannelMass word ≈
      Q'.ofNat (invariantMultiplicity word) := by
  refine Q'.eqv_trans _
    (listQSum (fun _ : CutoffOneLocalChannel => (1 : Q'))
      (cutoffOneLocalChannelChoices word)) _ ?_ ?_
  · unfold cutoffOneLocalChannelMass
    exact listQSum_eqv_congr
      (fun channel => cutoffOneLocalChannel_weighted_norm_exact channel)
      (cutoffOneLocalChannelChoices word)
  · cases word <;>
      simp only [cutoffOneLocalChannelChoices, invariantMultiplicity,
        listQSum] <;>
      decide

/-! ## 4. Agreement with the production multiplicity table -/

/-- The dispatcher multiplicity and the independently established geometric
fundamental-invariant multiplicity are the same function on all total local
words. -/
theorem invariantMultiplicity_eq_fundamentalInvariantMultiplicity_valence
    (word : CutoffOneHaarWord) :
    invariantMultiplicity word =
      fundamentalInvariantMultiplicity (valence word) := by
  cases word <;> rfl

theorem cutoffOneLocalChannelChoices_length_eq_fundamentalInvariantMultiplicity
    (word : CutoffOneHaarWord) :
    (cutoffOneLocalChannelChoices word).length =
      fundamentalInvariantMultiplicity (valence word) := by
  rw [cutoffOneLocalChannelChoices_length,
    invariantMultiplicity_eq_fundamentalInvariantMultiplicity_valence]

/-- Final local ledger in the production geometric normalization. -/
theorem cutoffOneLocalChannelMass_eqv_fundamentalInvariantMultiplicity
    (word : CutoffOneHaarWord) :
    cutoffOneLocalChannelMass word ≈
      Q'.ofNat (fundamentalInvariantMultiplicity (valence word)) := by
  rw [← invariantMultiplicity_eq_fundamentalInvariantMultiplicity_valence]
  exact cutoffOneLocalChannelMass_eqv_invariantMultiplicity word

#print axioms cutoffOneLocalChannelChoices_length
#print axioms cutoffOneLocalChannelWeight_nonneg
#print axioms cutoffOneLocalChannel_weighted_norm_exact
#print axioms cutoffOneLocalChannelMass_eqv_invariantMultiplicity
#print axioms invariantMultiplicity_eq_fundamentalInvariantMultiplicity_valence
#print axioms cutoffOneLocalChannelMass_eqv_fundamentalInvariantMultiplicity

end YMGap.Continuum.SU2QuaternionCutoffOneLocalChannelMass
