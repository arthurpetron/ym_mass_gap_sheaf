/-
# Exact cross-plane channel convolution for finite SU(2) fusion paths

The left-associated finite-cutoff path count is not an associative fusion
algebra at an undersized cutoff.  In particular, a same-order attempt to
split a vacuum multiplicity across a channel can fail.  The reflection
geometry supplies the missing operation: the path on the reflected half is
read in reverse order.  Since each SU(2) fusion step is symmetric, reversing
the path transposes the finite transition product, and the cross-plane
contraction is an exact finite matrix multiplication at every cutoff.

This file proves that statement from the literal recursive path count.  The
main theorem is an equality of natural cardinalities, before any rational
weight, positivity, or PSD wrapper is introduced.
-/

import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.Z4FusionChannelConvolution

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Finite transition paths -/

/-- A finite-cutoff fusion walk from `start` to `finish`, reading the
displayed external spins from left to right. -/
def fusionWalkMultiplicity
    (cutoff start finish : Nat) : List Nat -> Nat
  | [] => boolMultiplicity (decide (start = finish))
  | spin :: rest =>
      natListSum ((List.range (cutoff + 1)).map fun next =>
        if fusionOK start spin next then
          fusionWalkMultiplicity cutoff next finish rest
        else 0)

/-- Full symmetry of the SU(2) trivalent fusion predicate, in the orientation
needed to transpose one transition step. -/
theorem fusionOK_reverse_step (start spin finish : Nat) :
    fusionOK start spin finish = fusionOK finish spin start := by
  calc
    fusionOK start spin finish = fusionOK start finish spin :=
      fusionOK_symm_bt start spin finish
    _ = fusionOK finish start spin :=
      fusionOK_symm_ab start finish spin
    _ = fusionOK finish spin start :=
      fusionOK_symm_bt finish start spin

private theorem natListSumMapZero {A : Type} :
    ∀ xs : List A, natListSum (xs.map fun _ => 0) = 0
  | [] => by simp [natListSum]
  | _ :: tail => by
      simp only [List.map_cons, natListSum, Nat.zero_add]
      exact natListSumMapZero tail

private theorem natListSumRangeUnique
    {cutoff chosen : Nat} (term : Nat -> Nat)
    (hchosen : chosen ≤ cutoff)
    (hzero : ∀ x, x ≤ cutoff -> x ≠ chosen -> term x = 0) :
    natListSum ((List.range (cutoff + 1)).map term) = term chosen := by
  induction cutoff with
  | zero =>
      have hchosenZero : chosen = 0 := by omega
      subst chosen
      rfl
  | succ cutoff ih =>
      rw [List.range_succ, List.map_append, natListSum_append]
      simp only [List.map_singleton, natListSum, Nat.add_zero]
      by_cases hbelow : chosen ≤ cutoff
      · rw [ih hbelow (fun x hx hne => hzero x (by omega) hne),
          hzero (cutoff + 1) (by omega) (by omega), Nat.add_zero]
      · have htop : chosen = cutoff + 1 := by omega
        subst chosen
        have hprefix :
            natListSum ((List.range (cutoff + 1)).map term) = 0 :=
          (natListSum_map_congr term (fun _ => 0)
              (List.range (cutoff + 1)) (by
                intro x hx
                exact hzero x (by
                  have hlt := List.mem_range.mp hx
                  omega) (by
                  have hlt := List.mem_range.mp hx
                  omega))).trans
            (natListSumMapZero (List.range (cutoff + 1)))
        rw [hprefix, Nat.zero_add]

theorem fusionWalkMultiplicity_singleton
    {cutoff start finish : Nat} (spin : Nat)
    (hfinish : finish ≤ cutoff) :
    fusionWalkMultiplicity cutoff start finish [spin] =
      boolMultiplicity (fusionOK start spin finish) := by
  rw [fusionWalkMultiplicity]
  rw [natListSumRangeUnique
    (fun next =>
      if fusionOK start spin next then
        fusionWalkMultiplicity cutoff next finish []
      else 0) hfinish]
  · cases h : fusionOK start spin finish <;>
      simp [fusionWalkMultiplicity, boolMultiplicity]
  · intro next _ hne
    simp [fusionWalkMultiplicity, boolMultiplicity, hne]

/-! ## 2. Identification with the production left-associated count -/

/-- Closing a walk from `start` to `finish` by one final `finish` leg gives
exactly the existing vacuum-ending left-associated path count. -/
theorem fusionPathMultiplicity_cons_append_eq_walk
    {cutoff : Nat} : ∀ (spins : List Nat) (start finish : Nat),
    start ≤ cutoff -> finish ≤ cutoff ->
    SpinsBounded cutoff spins ->
    fusionPathMultiplicity cutoff (start :: spins ++ [finish]) =
      fusionWalkMultiplicity cutoff start finish spins
  | [], start, finish, _, _, _ => by
      change fusionPathMultiplicity cutoff [start, finish] =
        boolMultiplicity (decide (start = finish))
      rw [fusionPathMultiplicity_two,
        fusionOK_zero_output_eq_decide]
  | spin :: rest, start, finish, _, hfinish, hbounded => by
      rw [show start :: (spin :: rest) ++ [finish] =
          start :: spin :: (rest ++ [finish]) by rfl,
        fusionPathMultiplicity_cons_cons,
        fusionWalkMultiplicity]
      apply natListSum_map_congr
      intro channel hchannel
      by_cases hfusion : fusionOK start spin channel = true
      · simp only [hfusion, if_true]
        apply fusionPathMultiplicity_cons_append_eq_walk
        · have hlt := List.mem_range.mp hchannel
          omega
        · exact hfinish
        · intro value hvalue
          exact hbounded value
            (List.mem_cons_of_mem spin hvalue)
      · have hfalse : fusionOK start spin channel = false := by
          cases h : fusionOK start spin channel
          · rfl
          · exact False.elim (hfusion h)
        simp [hfalse]

/-- Multiplicity for a half-path whose open end carries `channel`. -/
def fusionChannelAmplitude
    (cutoff : Nat) (spins : List Nat) (channel : Nat) : Nat :=
  fusionPathMultiplicity cutoff (spins ++ [channel])

theorem fusionChannelAmplitude_eq_walk
    {cutoff channel : Nat} {spins : List Nat}
    (hchannel : channel ≤ cutoff)
    (hbounded : SpinsBounded cutoff spins) :
    fusionChannelAmplitude cutoff spins channel =
      fusionWalkMultiplicity cutoff 0 channel spins := by
  have hall : SpinsBounded cutoff (spins ++ [channel]) := by
    intro spin hspin
    rcases List.mem_append.mp hspin with hsource | hlast
    · exact hbounded spin hsource
    · have heq : spin = channel := List.mem_singleton.mp hlast
      rw [heq]
      exact hchannel
  unfold fusionChannelAmplitude
  rw [← fusionPathMultiplicity_zero_cons
    (spins ++ [channel]) hall]
  exact fusionPathMultiplicity_cons_append_eq_walk
    spins 0 channel (Nat.zero_le _) hchannel hbounded

theorem fusionPathMultiplicity_eq_walk
    {cutoff : Nat} {spins : List Nat}
    (hbounded : SpinsBounded cutoff spins) :
    fusionPathMultiplicity cutoff spins =
      fusionWalkMultiplicity cutoff 0 0 spins := by
  calc
    fusionPathMultiplicity cutoff spins =
        fusionChannelAmplitude cutoff spins 0 := by
      unfold fusionChannelAmplitude
      simpa using fusionPathMultiplicity_insert_zero spins [] (by
        simpa using hbounded)
    _ = fusionWalkMultiplicity cutoff 0 0 spins :=
      fusionChannelAmplitude_eq_walk (Nat.zero_le _) hbounded

/-! ## 3. Finite-sum algebra for path concatenation -/

private theorem natListSumMapMulRight {A : Type}
    (value : A -> Nat) (factor : Nat) : ∀ xs : List A,
    natListSum (xs.map fun x => value x * factor) =
      natListSum (xs.map value) * factor
  | [] => by simp [natListSum]
  | head :: tail => by
      simp only [List.map_cons, natListSum]
      rw [natListSumMapMulRight value factor tail,
        Nat.add_mul]

private theorem natListSumIfNested
    {A B : Type} (allowed : A -> Bool)
    (term : A -> B -> Nat) : ∀ (xs : List A) (ys : List B),
    natListSum (xs.map fun x =>
        if allowed x then natListSum (ys.map (term x)) else 0) =
      natListSum (xs.map fun x =>
        natListSum (ys.map fun y =>
          if allowed x then term x y else 0))
  | [], _ => rfl
  | head :: tail, ys => by
      simp only [List.map_cons, natListSum]
      rw [natListSumIfNested allowed term tail ys]
      cases allowed head <;> simp [natListSumMapZero]

private theorem natListSumWeightedSwap
    {A B : Type} (allowed : A -> Bool)
    (amplitude : A -> B -> Nat) (weight : B -> Nat)
    (xs : List A) (ys : List B) :
    natListSum (xs.map fun x =>
        if allowed x then
          natListSum (ys.map fun y => amplitude x y * weight y)
        else 0) =
      natListSum (ys.map fun y =>
        natListSum (xs.map fun x =>
          if allowed x then amplitude x y else 0) * weight y) := by
  calc
    natListSum (xs.map fun x =>
        if allowed x then
          natListSum (ys.map fun y => amplitude x y * weight y)
        else 0) =
        natListSum (xs.map fun x =>
          natListSum (ys.map fun y =>
            if allowed x then amplitude x y * weight y else 0)) :=
      natListSumIfNested allowed
        (fun x y => amplitude x y * weight y) xs ys
    _ = natListSum (ys.map fun y =>
          natListSum (xs.map fun x =>
            if allowed x then amplitude x y * weight y else 0)) :=
      natListSum_map_swap
        (fun x y =>
          if allowed x then amplitude x y * weight y else 0) xs ys
    _ = natListSum (ys.map fun y =>
          natListSum (xs.map fun x =>
            if allowed x then amplitude x y else 0) * weight y) := by
      apply natListSum_map_congr
      intro y _
      rw [← natListSumMapMulRight
        (fun x => if allowed x then amplitude x y else 0)
        (weight y) xs]
      apply natListSum_map_congr
      intro x _
      cases allowed x <;> simp

/-- Chapman--Kolmogorov identity for the literal finite fusion walks. -/
theorem fusionWalkMultiplicity_append
    {cutoff start : Nat} (left right : List Nat) (finish : Nat)
    (hstart : start ≤ cutoff) :
    fusionWalkMultiplicity cutoff start finish (left ++ right) =
      natListSum ((List.range (cutoff + 1)).map fun channel =>
        fusionWalkMultiplicity cutoff start channel left *
          fusionWalkMultiplicity cutoff channel finish right) := by
  induction left generalizing start with
  | nil =>
      simp only [List.nil_append, fusionWalkMultiplicity]
      rw [natListSumRangeUnique
        (fun channel =>
          boolMultiplicity (decide (start = channel)) *
            fusionWalkMultiplicity cutoff channel finish right)
        hstart]
      · simp [boolMultiplicity]
      · intro channel _ hne
        have hne' : start ≠ channel := by
          intro heq
          exact hne heq.symm
        simp [boolMultiplicity, hne']
  | cons spin rest ih =>
      simp only [List.cons_append, fusionWalkMultiplicity]
      let channels := List.range (cutoff + 1)
      calc
        natListSum (channels.map fun next =>
            if fusionOK start spin next then
              fusionWalkMultiplicity cutoff next finish (rest ++ right)
            else 0) =
            natListSum (channels.map fun next =>
              if fusionOK start spin next then
                natListSum (channels.map fun channel =>
                  fusionWalkMultiplicity cutoff next channel rest *
                    fusionWalkMultiplicity cutoff channel finish right)
              else 0) := by
          apply natListSum_map_congr
          intro next hnext
          by_cases hfusion : fusionOK start spin next = true
          · simp only [hfusion, if_true]
            exact ih (start := next)
              (by have hlt := List.mem_range.mp hnext; omega)
          · have hfalse : fusionOK start spin next = false := by
              cases h : fusionOK start spin next
              · rfl
              · exact False.elim (hfusion h)
            simp [hfalse]
        _ = natListSum (channels.map fun channel =>
              natListSum (channels.map fun next =>
                if fusionOK start spin next then
                  fusionWalkMultiplicity cutoff next channel rest
                else 0) *
              fusionWalkMultiplicity cutoff channel finish right) :=
          natListSumWeightedSwap
            (fun next => fusionOK start spin next)
            (fun next channel =>
              fusionWalkMultiplicity cutoff next channel rest)
            (fun channel =>
              fusionWalkMultiplicity cutoff channel finish right)
            channels channels

/-! ## 4. Path reversal and exact channel convolution -/

/-- Reversing the external-spin word transposes the finite fusion walk. -/
theorem fusionWalkMultiplicity_reverse
    {cutoff start finish : Nat} (spins : List Nat)
    (hstart : start ≤ cutoff) (hfinish : finish ≤ cutoff) :
    fusionWalkMultiplicity cutoff start finish spins =
      fusionWalkMultiplicity cutoff finish start spins.reverse := by
  induction spins generalizing start finish with
  | nil =>
      simp [fusionWalkMultiplicity, boolMultiplicity, eq_comm]
  | cons spin rest ih =>
      simp only [fusionWalkMultiplicity, List.reverse_cons]
      let channels := List.range (cutoff + 1)
      have happ := fusionWalkMultiplicity_append
        (cutoff := cutoff) (start := finish)
        rest.reverse [spin] start hfinish
      rw [happ]
      apply natListSum_map_congr
      intro channel hchannel
      have hchannelBound : channel ≤ cutoff := by
        have hlt := List.mem_range.mp hchannel
        omega
      rw [fusionWalkMultiplicity_singleton spin hstart,
        ← ih hchannelBound hfinish]
      rw [fusionOK_reverse_step start spin channel]
      cases fusionOK channel spin start <;>
        simp [boolMultiplicity, Nat.mul_comm]

/-- **Exact cross-plane channel convolution.**  The vacuum multiplicity of
`left ++ reflectedRight` is the finite sum over boundary channels of the two
open half-path cardinalities.  The reflected half is read in reverse order;
no associativity or fusion-complete-cutoff hypothesis is used. -/
theorem fusionPathMultiplicity_reflection_convolution
    {cutoff : Nat} (left reflectedRight : List Nat)
    (hbounded : SpinsBounded cutoff (left ++ reflectedRight)) :
    fusionPathMultiplicity cutoff (left ++ reflectedRight) =
      natListSum ((List.range (cutoff + 1)).map fun channel =>
        fusionChannelAmplitude cutoff left channel *
          fusionChannelAmplitude cutoff reflectedRight.reverse channel) := by
  have hparts := spinsBounded_append hbounded
  calc
    fusionPathMultiplicity cutoff (left ++ reflectedRight) =
        fusionWalkMultiplicity cutoff 0 0 (left ++ reflectedRight) :=
      fusionPathMultiplicity_eq_walk hbounded
    _ = natListSum ((List.range (cutoff + 1)).map fun channel =>
          fusionWalkMultiplicity cutoff 0 channel left *
            fusionWalkMultiplicity cutoff channel 0 reflectedRight) :=
      fusionWalkMultiplicity_append left reflectedRight 0 (Nat.zero_le _)
    _ = natListSum ((List.range (cutoff + 1)).map fun channel =>
          fusionWalkMultiplicity cutoff 0 channel left *
            fusionWalkMultiplicity cutoff 0 channel
              reflectedRight.reverse) := by
      apply natListSum_map_congr
      intro channel hchannel
      apply congrArg
        (fun value => fusionWalkMultiplicity cutoff 0 channel left * value)
      exact fusionWalkMultiplicity_reverse reflectedRight
        (by have hlt := List.mem_range.mp hchannel; omega)
        (Nat.zero_le _)
    _ = natListSum ((List.range (cutoff + 1)).map fun channel =>
          fusionChannelAmplitude cutoff left channel *
            fusionChannelAmplitude cutoff reflectedRight.reverse channel) := by
      apply natListSum_map_congr
      intro channel hchannel
      have hchannelBound : channel ≤ cutoff := by
        have hlt := List.mem_range.mp hchannel
        omega
      rw [fusionChannelAmplitude_eq_walk hchannelBound hparts.1,
        fusionChannelAmplitude_eq_walk hchannelBound]
      intro spin hspin
      exact hparts.2 spin (by
        have hsource := List.mem_reverse.mp hspin
        exact hsource)

/-! ## 5. Checked same-order fence -/

/-- At cutoff two, the literal four-spin count has two paths. -/
theorem sameOrderFence_full :
    fusionPathMultiplicity 2 ([1] ++ [1, 2, 2]) = 2 := by
  decide

/-- The tempting same-order channel contraction loses one of those paths. -/
theorem sameOrderFence_channel_sum :
    natListSum ((List.range 3).map fun channel =>
      fusionChannelAmplitude 2 [1] channel *
        fusionChannelAmplitude 2 [1, 2, 2] channel) = 1 := by
  decide

/-- Therefore the reflected-half reversal in the main convolution theorem is
load-bearing at an undersized cutoff; it may not be silently erased. -/
theorem sameOrder_channel_convolution_false :
    fusionPathMultiplicity 2 ([1] ++ [1, 2, 2]) ≠
      natListSum ((List.range 3).map fun channel =>
        fusionChannelAmplitude 2 [1] channel *
          fusionChannelAmplitude 2 [1, 2, 2] channel) := by
  rw [sameOrderFence_full, sameOrderFence_channel_sum]
  decide

end YMGap.Continuum.Z4FusionChannelConvolution

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionOK_reverse_step
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionWalkMultiplicity_singleton
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionPathMultiplicity_cons_append_eq_walk
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionChannelAmplitude_eq_walk
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionWalkMultiplicity_append
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionWalkMultiplicity_reverse
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.fusionPathMultiplicity_reflection_convolution
#print axioms YMGap.Continuum.Z4FusionChannelConvolution.sameOrder_channel_convolution_false
