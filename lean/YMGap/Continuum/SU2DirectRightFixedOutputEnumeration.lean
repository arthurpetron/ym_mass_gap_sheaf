/-
# Constructive enumeration of fixed-output ordered right channels

For fixed input degrees `(a,b,c)` and final degree `d`, a right-associated
channel is determined uniquely by its inner contraction order `p`: the outer
order must be `couplingOrder a (b+c-2p) d`.  This module gives a decidable
admissibility predicate, enumerates all admissible `p` in a bounded list, and
proves soundness, completeness, and uniqueness of the resulting channels.
-/

import YMGap.Continuum.SU2DirectRightFixedOutputSections

namespace YMGap.Continuum.SU2DirectRightFixedOutputEnumeration

open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections

/-- Decidable proof-free admissibility of an inner right contraction order
for final degree `d`. -/
def FixedRightAdmissible (a b c d p : Nat) : Prop :=
  p ≤ min b c ∧
    couplingOrder a (b + c - 2 * p) d ≤ min a (b + c - 2 * p) ∧
    a + (b + c - 2 * p) -
      2 * couplingOrder a (b + c - 2 * p) d = d

instance fixedRightAdmissibleDecidable (a b c d p : Nat) :
    Decidable (FixedRightAdmissible a b c d p) := by
  unfold FixedRightAdmissible
  infer_instance

/-- Every proof-carrying fixed right channel satisfies the proof-free
admissibility predicate at its inner order. -/
theorem fixedRight_admissible {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    FixedRightAdmissible a b c d q.p := by
  refine ⟨q.p_le, ?_, ?_⟩
  · change couplingOrder a q.intermediate d ≤ min a q.intermediate
    rw [fixedRight_outer_couplingOrder q]
    exact q.r_le
  · change a + q.intermediate -
      2 * couplingOrder a q.intermediate d = d
    rw [fixedRight_outer_couplingOrder q]
    exact q.degree_eq

/-- Turn a decidably admissible inner order into its unique proof-carrying
fixed right channel. -/
def fixedRightChannelOfAdmissible {a b c d p : Nat}
    (hp : FixedRightAdmissible a b c d p) :
    FixedRightCGChannel a b c d where
  p := p
  p_le := hp.1
  r := couplingOrder a (b + c - 2 * p) d
  r_le := hp.2.1
  degree_eq := hp.2.2

/-- Two fixed-output right channels with the same inner order are equal. -/
theorem fixedRightChannel_eq_of_p_eq {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (hpu : q.p = u.p) : q = u := by
  have hru : q.r = u.r := by
    calc
      q.r = couplingOrder a q.intermediate d :=
        (fixedRight_outer_couplingOrder q).symm
      _ = couplingOrder a u.intermediate d := by
        simp only [FixedRightCGChannel.intermediate, hpu]
      _ = u.r := fixedRight_outer_couplingOrder u
  cases q with
  | mk p hp r hr hd =>
      cases u with
      | mk p' hp' r' hr' hd' =>
          dsimp only at hpu hru
          subst p'
          subst r'
          rfl

/-- Reconstructing a proof-carrying channel from its admissibility proof
returns that channel. -/
theorem fixedRightChannelOfAdmissible_roundtrip {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    fixedRightChannelOfAdmissible (fixedRight_admissible q) = q := by
  apply fixedRightChannel_eq_of_p_eq
  rfl

/-- Bounded constructive list of all admissible inner right orders. -/
def fixedRightValidPs (a b c d : Nat) : List Nat :=
  (List.range (min b c + 1)).filter
    (fun p => decide (FixedRightAdmissible a b c d p))

/-- Membership in the bounded enumeration is exactly admissibility. -/
theorem mem_fixedRightValidPs_iff (a b c d p : Nat) :
    p ∈ fixedRightValidPs a b c d ↔
      FixedRightAdmissible a b c d p := by
  constructor
  · intro hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  · intro hp
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by
      have hbound := hp.1
      omega), decide_eq_true hp⟩

/-- Every proof-carrying fixed right channel occurs in the bounded list. -/
theorem fixedRightValidPs_complete {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    q.p ∈ fixedRightValidPs a b c d := by
  exact (mem_fixedRightValidPs_iff a b c d q.p).2
    (fixedRight_admissible q)

/-- Every enumerated inner order constructs a sound fixed right channel. -/
def fixedRightChannelOfMem {a b c d p : Nat}
    (hp : p ∈ fixedRightValidPs a b c d) :
    FixedRightCGChannel a b c d :=
  fixedRightChannelOfAdmissible
    ((mem_fixedRightValidPs_iff a b c d p).1 hp)

/-- The channel constructed from an enumerated order has that order. -/
theorem fixedRightChannelOfMem_p {a b c d p : Nat}
    (hp : p ∈ fixedRightValidPs a b c d) :
    (fixedRightChannelOfMem hp).p = p := rfl

/-- Actual proof-carrying list of every fixed-output right channel. -/
def fixedRightChannels (a b c d : Nat) :
    List (FixedRightCGChannel a b c d) :=
  (fixedRightValidPs a b c d).attach.map
    (fun p => fixedRightChannelOfMem p.property)

/-- Forgetting the proofs and outer orders from the channel list returns
exactly the decidable list of valid inner orders. -/
theorem fixedRightChannels_map_p (a b c d : Nat) :
    (fixedRightChannels a b c d).map (fun q => q.p) =
      fixedRightValidPs a b c d := by
  unfold fixedRightChannels
  rw [List.map_map]
  simpa only [Function.comp_apply, fixedRightChannelOfMem_p] using
    (List.attach_map_subtype_val (fixedRightValidPs a b c d))

/-- The proof-carrying list is complete: every fixed-output right channel is
a member. -/
theorem fixedRightChannels_complete {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    q ∈ fixedRightChannels a b c d := by
  have hp : q.p ∈ (fixedRightChannels a b c d).map (fun u => u.p) := by
    rw [fixedRightChannels_map_p]
    exact fixedRightValidPs_complete q
  rcases List.mem_map.mp hp with ⟨u, hu, hup⟩
  have huq : u = q := fixedRightChannel_eq_of_p_eq u q hup
  simpa only [huq] using hu

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-- The decidable label enumeration has no duplicates. -/
theorem fixedRightValidPs_nodup (a b c d : Nat) :
    (fixedRightValidPs a b c d).Nodup := by
  exact List.filter_sublist.nodup (range_nodup (min b c + 1))

private theorem nodup_of_map_nodup {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hm := List.nodup_cons.mp h
      refine List.nodup_cons.mpr ⟨?_, nodup_of_map_nodup f xs hm.2⟩
      intro hx
      exact hm.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-- The proof-carrying channel enumeration has no duplicates. -/
theorem fixedRightChannels_nodup (a b c d : Nat) :
    (fixedRightChannels a b c d).Nodup := by
  apply nodup_of_map_nodup (fun q => q.p)
  rw [fixedRightChannels_map_p]
  exact fixedRightValidPs_nodup a b c d

end YMGap.Continuum.SU2DirectRightFixedOutputEnumeration

#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRight_admissible
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannel_eq_of_p_eq
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannelOfAdmissible_roundtrip
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.mem_fixedRightValidPs_iff
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightValidPs_complete
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannelOfMem_p
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannels_map_p
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannels_complete
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightValidPs_nodup
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputEnumeration.fixedRightChannels_nodup
