/-
# Descriptor-fixed cutoff-one positive-channel tensors

The cutoff-one Haar word at one physical link contains matrix coordinates
read from a Boolean corner environment.  Those coordinates must not be used
to choose the tensor leaf of the global contraction graph: only the ordered
occurrence orientations determine that leaf.  This module separates the two
roles.

It first factors the local channel list through valence.  It then builds the
honest environment-dependent dispatcher word through the existing
proof-carrying at-most-six conversion, while building the tensor from the
same descriptors evaluated at a fixed dummy environment.  The dummy values
do not alter any occurrence orientation.

At valence four the local positive-channel tensor uses the frozen native
coordinate order `[1, 3, 2, 4]`.  Endpoint factors advertise literal
descriptor order `[1, 2, 3, 4]`, so the tensor here includes the indispensable
middle adjacent swap.  The final Gram theorem proves that this correction
and every orientation transport preserve the exact local channel norm.

# Constructive discipline

There is no `Classical`, assignment enumeration, `native_decide`,
`sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneOrientedPositiveChannels
import YMGap.Continuum.SU2QuaternionCutoffOneLocalChannelMass
import YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts
import YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini
import YMGap.Continuum.SymbolicFiniteBoolTensorPortReordering

namespace YMGap.Continuum.SU2QuaternionCutoffOneDescriptorChannelTensor

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
open YMGap.Continuum.SU2QuaternionAtMostSixBlockWordFubini
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
open YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedPositiveChannels
open YMGap.Continuum.SU2QuaternionCutoffOneLocalChannelMass

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Channel choices depend only on local valence -/

/-- The exact cutoff-one local channel list as a function of valence alone.
Values above six are unreachable for the descriptor words below and are
assigned the empty list rather than truncated. -/
def cutoffOneLocalChannelChoicesAtValence :
    Nat -> List CutoffOneLocalChannel
  | 0 => [.vacuum]
  | 1 => []
  | 2 => [.bivalent]
  | 3 => []
  | 4 => [.fourValent .singlet, .fourValent .triplet]
  | 5 => []
  | 6 =>
      [.sixValent .spinThreeHalves,
       .sixValent .leftA,
       .sixValent .leftB,
       .sixValent .leftX,
       .sixValent .leftY]
  | _ => []

/-- The existing dispatcher choice list forgets all matrix coordinates and
factors exactly through the word's valence. -/
theorem cutoffOneLocalChannelChoices_eq_atValence
    (word : CutoffOneHaarWord) :
    cutoffOneLocalChannelChoices word =
      cutoffOneLocalChannelChoicesAtValence (valence word) := by
  cases word <;> rfl

/-! ## 2. Honest and orientation-reference descriptor words -/

/-- The honest dispatcher word selected by a bounded descriptor list in one
named Boolean environment.  No descriptor is dropped or padded. -/
def cutoffOneDescriptorHaarWord
    (environment : Nat -> Bool)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6) : CutoffOneHaarWord :=
  AtMostSixFundamentalWord.toHaarWord
    { occurrences := descriptors.map
        (cutoffOneDescriptorOccurrence environment)
      length_le_six := by
        rw [List.length_map]
        exact hlen }

/-- The descriptor conversion retains the literal list length. -/
theorem cutoffOneDescriptorHaarWord_valence
    (environment : Nat -> Bool)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6) :
    valence (cutoffOneDescriptorHaarWord environment descriptors hlen) =
      descriptors.length := by
  unfold cutoffOneDescriptorHaarWord
  rw [AtMostSixFundamentalWord.valence_toHaarWord]
  exact List.length_map _

/-- Hence the honest local choice list is independent of the Boolean corner
environment and depends only on the descriptor count. -/
theorem cutoffOneDescriptorHaarWord_choices_exact
    (environment : Nat -> Bool)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6) :
    cutoffOneLocalChannelChoices
        (cutoffOneDescriptorHaarWord environment descriptors hlen) =
      cutoffOneLocalChannelChoicesAtValence descriptors.length := by
  rw [cutoffOneLocalChannelChoices_eq_atValence,
    cutoffOneDescriptorHaarWord_valence]

/-- A reference word retaining every descriptor orientation while replacing
both matrix coordinates by `false`.  It is used only to define a fixed tensor
leaf; actual environment bits enter later through endpoint-port evaluation. -/
def cutoffOneDescriptorOrientationWord
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6) : CutoffOneHaarWord :=
  cutoffOneDescriptorHaarWord (fun _ => false) descriptors hlen

/-! ## 3. Literal-order channel tensors -/

/-- The zero tensor, used only on channel/valence combinations which are not
members of the exact local choice list. -/
def zeroBoolTensor : (n : Nat) -> BoolTensor n
  | 0 => show Q' from 0
  | n + 1 => fun _ => zeroBoolTensor n

/-- The unique middle swap taking literal four-port evaluation order to the
native positive-channel order `[1, 3, 2, 4]`. -/
def fourLiteralToChannelProgram : AdjacentSwapProgram 4 :=
  .cons (AdjacentSwapStep.at 1 1) .nil

/-- A channel tensor at the exact valence of one dispatcher word.  Valid
channels use the actual transported positive-channel tensors; all invalid
channel/valence pairs are zero. -/
def cutoffOneWordChannelTensor :
    (word : CutoffOneHaarWord) ->
      CutoffOneLocalChannel -> BoolTensor (valence word)
  | .v0, .vacuum => show Q' from 1
  | .v0, _ => zeroBoolTensor 0
  | .v1 _, _ => zeroBoolTensor 1
  | .v2 first second, .bivalent =>
      orientedBivalentChannelBoolTensor first second
  | .v2 _ _, _ => zeroBoolTensor 2
  | .v3 _ _ _, _ => zeroBoolTensor 3
  | .v4 first second third fourth, .fourValent channel =>
      fourLiteralToChannelProgram.toWiring.act
        (orientedFourChannelBoolTensor
          first second third fourth channel)
  | .v4 _ _ _ _, _ => zeroBoolTensor 4
  | .v5 _ _ _ _ _, _ => zeroBoolTensor 5
  | .v6 first second third fourth fifth sixth, .sixValent channel =>
      orientedSixChannelBoolTensor
        first second third fourth fifth sixth channel
  | .v6 _ _ _ _ _ _, _ => zeroBoolTensor 6

/-- Every valid literal-order word tensor has exactly the symbolic norm stored
in the uniform local channel ledger.  The four-valent proof explicitly uses
the middle-swap Gram isometry before the orientation-transport isometry. -/
theorem cutoffOneWordChannelTensor_gram_eqv_localNorm
    (word : CutoffOneHaarWord) (channel : CutoffOneLocalChannel)
    (hchannel : channel ∈ cutoffOneLocalChannelChoices word) :
    boolTensorDot (valence word)
        (cutoffOneWordChannelTensor word channel)
        (cutoffOneWordChannelTensor word channel) ≈
      cutoffOneLocalChannelNorm channel := by
  cases word with
  | v0 =>
      change channel ∈ [.vacuum] at hchannel
      have hchannel' : channel = .vacuum :=
        List.mem_singleton.mp hchannel
      cases hchannel'
      change (1 : Q') * 1 ≈ 1
      exact Q'.mul_one_eqv 1
  | v1 first =>
      change channel ∈ [] at hchannel
      exact False.elim (List.not_mem_nil hchannel)
  | v2 first second =>
      change channel ∈ [.bivalent] at hchannel
      have hchannel' : channel = .bivalent :=
        List.mem_singleton.mp hchannel
      cases hchannel'
      exact orientedBivalentChannelBoolTensor_gram_eqv first second
  | v3 first second third =>
      change channel ∈ [] at hchannel
      exact False.elim (List.not_mem_nil hchannel)
  | v4 first second third fourth =>
      change channel ∈
        [.fourValent .singlet, .fourValent .triplet] at hchannel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
      rcases hchannel with hchannel | hchannel <;> cases hchannel
      · refine Q'.eqv_trans _ _ _
          (SignedBoolWiring.gram_eqv
            fourLiteralToChannelProgram.toWiring
            (orientedFourChannelBoolTensor
              first second third fourth .singlet)
            (orientedFourChannelBoolTensor
              first second third fourth .singlet)) ?_
        exact orientedFourChannelBoolTensor_gram_eqv
          first second third fourth .singlet .singlet
      · refine Q'.eqv_trans _ _ _
          (SignedBoolWiring.gram_eqv
            fourLiteralToChannelProgram.toWiring
            (orientedFourChannelBoolTensor
              first second third fourth .triplet)
            (orientedFourChannelBoolTensor
              first second third fourth .triplet)) ?_
        exact orientedFourChannelBoolTensor_gram_eqv
          first second third fourth .triplet .triplet
  | v5 first second third fourth fifth =>
      change channel ∈ [] at hchannel
      exact False.elim (List.not_mem_nil hchannel)
  | v6 first second third fourth fifth sixth =>
      change channel ∈
        [.sixValent .spinThreeHalves,
         .sixValent .leftA,
         .sixValent .leftB,
         .sixValent .leftX,
         .sixValent .leftY] at hchannel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
      rcases hchannel with hchannel | hchannel | hchannel | hchannel |
        hchannel <;> cases hchannel
      · exact orientedSixChannelBoolTensor_gram_eqv
          first second third fourth fifth sixth
          .spinThreeHalves .spinThreeHalves
      · exact orientedSixChannelBoolTensor_gram_eqv
          first second third fourth fifth sixth .leftA .leftA
      · exact orientedSixChannelBoolTensor_gram_eqv
          first second third fourth fifth sixth .leftB .leftB
      · exact orientedSixChannelBoolTensor_gram_eqv
          first second third fourth fifth sixth .leftX .leftX
      · exact orientedSixChannelBoolTensor_gram_eqv
          first second third fourth fifth sixth .leftY .leftY

/-- The fixed descriptor tensor, in literal descriptor order.  Its arity is
transported along the exact valence theorem rather than filled or truncated. -/
def cutoffOneDescriptorChannelTensor
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6)
    (channel : CutoffOneLocalChannel) :
    BoolTensor descriptors.length :=
  tensorCast
    (cutoffOneDescriptorHaarWord_valence
      (fun _ => false) descriptors hlen)
    (cutoffOneWordChannelTensor
      (cutoffOneDescriptorOrientationWord descriptors hlen) channel)

/-- The fixed descriptor tensor has the exact local norm whenever the
channel belongs to the valence-indexed choice list. -/
theorem cutoffOneDescriptorChannelTensor_gram_eqv_localNorm
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6)
    (channel : CutoffOneLocalChannel)
    (hchannel :
      channel ∈ cutoffOneLocalChannelChoicesAtValence descriptors.length) :
    boolTensorDot descriptors.length
        (cutoffOneDescriptorChannelTensor descriptors hlen channel)
        (cutoffOneDescriptorChannelTensor descriptors hlen channel) ≈
      cutoffOneLocalChannelNorm channel := by
  have hword :
      channel ∈ cutoffOneLocalChannelChoices
        (cutoffOneDescriptorOrientationWord descriptors hlen) := by
    unfold cutoffOneDescriptorOrientationWord
    rw [cutoffOneDescriptorHaarWord_choices_exact]
    exact hchannel
  unfold cutoffOneDescriptorChannelTensor
  rw [boolTensorDot_tensorCast]
  exact cutoffOneWordChannelTensor_gram_eqv_localNorm
    (cutoffOneDescriptorOrientationWord descriptors hlen) channel hword

/-! ## 4. Exact endpoint-pair normalization -/

/-- **Unit endpoint-pair leaf mass.**  The inverse Gram weight is absorbed in
exactly the target endpoint tensor, while the source endpoint tensor is left
unscaled.  Consequently the product of the two leaf Gram masses is
`(weight * norm)^2`, hence exactly one.  This square, rather than a single
`weight * norm`, is the normalization required by the closed graphical
contraction bound. -/
theorem cutoffOneDescriptorEndpointLeafMass_eqv_one
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlen : descriptors.length <= 6)
    (channel : CutoffOneLocalChannel)
    (hchannel :
      channel ∈ cutoffOneLocalChannelChoicesAtValence descriptors.length) :
    let tensor :=
      cutoffOneDescriptorChannelTensor descriptors hlen channel
    boolTensorDot descriptors.length
          (tensorScale descriptors.length
            (cutoffOneLocalChannelWeight channel) tensor)
          (tensorScale descriptors.length
            (cutoffOneLocalChannelWeight channel) tensor) *
        boolTensorDot descriptors.length tensor tensor ≈ 1 := by
  let tensor := cutoffOneDescriptorChannelTensor descriptors hlen channel
  let norm := boolTensorDot descriptors.length tensor tensor
  let weight := cutoffOneLocalChannelWeight channel
  have hnorm : norm ≈ cutoffOneLocalChannelNorm channel := by
    exact cutoffOneDescriptorChannelTensor_gram_eqv_localNorm
      descriptors hlen channel hchannel
  have hscaled :
      boolTensorDot descriptors.length
          (tensorScale descriptors.length weight tensor)
          (tensorScale descriptors.length weight tensor) ≈
        (weight * weight) * norm := by
    exact boolTensorDot_scale descriptors.length weight weight tensor tensor
  have hnormalized : weight * norm ≈ 1 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left weight norm
        (cutoffOneLocalChannelNorm channel) hnorm)
      (cutoffOneLocalChannel_weighted_norm_exact channel)
  change
    boolTensorDot descriptors.length
          (tensorScale descriptors.length weight tensor)
          (tensorScale descriptors.length weight tensor) * norm ≈ 1
  refine Q'.eqv_trans _ (((weight * weight) * norm) * norm) _
    (Q'.mul_eqv_congr_right _ _ norm hscaled) ?_
  refine Q'.eqv_trans _ ((weight * weight) * (norm * norm)) _
    (Q'.mul_assoc_eqv (weight * weight) norm norm) ?_
  refine Q'.eqv_trans _ ((weight * norm) * (weight * norm)) _
    (Q'.eqv_symm (mul4_rearrange weight norm weight norm)) ?_
  refine Q'.eqv_trans _ (1 * (weight * norm)) _
    (Q'.mul_eqv_congr_right
      (weight * norm) 1 (weight * norm) hnormalized) ?_
  refine Q'.eqv_trans _ (1 * 1) _
    (Q'.mul_eqv_congr_left 1 (weight * norm) 1 hnormalized) ?_
  exact Q'.one_mul_eqv 1

/-! ## Axiom audit -/

#print axioms cutoffOneLocalChannelChoices_eq_atValence
#print axioms cutoffOneDescriptorHaarWord_valence
#print axioms cutoffOneDescriptorHaarWord_choices_exact
#print axioms cutoffOneWordChannelTensor_gram_eqv_localNorm
#print axioms cutoffOneDescriptorChannelTensor_gram_eqv_localNorm
#print axioms cutoffOneDescriptorEndpointLeafMass_eqv_one

end YMGap.Continuum.SU2QuaternionCutoffOneDescriptorChannelTensor
