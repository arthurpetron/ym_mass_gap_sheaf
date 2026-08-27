/-
# Constructive enumeration of fixed-output ordered left channels

For fixed external degrees `(a,b,c)` and final degree `d`, a left-associated
channel is uniquely determined by its first contraction order `k`; the outer
order is forced by the final degree.  This is the left-tree counterpart of
the existing complete right-channel enumeration.

Constructive contract: bounded lists and decidable arithmetic only, with no
choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2FixedLeftTransvectantEvaluation

namespace YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration

open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2TransvectantMixedPentagon

/-- Proof-free admissibility of a first left contraction order at fixed final
degree. -/
def FixedLeftAdmissible (a b c d k : Nat) : Prop :=
  k ≤ min a b ∧
    couplingOrder (a + b - 2 * k) c d ≤
      min (a + b - 2 * k) c ∧
    (a + b - 2 * k) + c -
      2 * couplingOrder (a + b - 2 * k) c d = d

instance fixedLeftAdmissibleDecidable (a b c d k : Nat) :
    Decidable (FixedLeftAdmissible a b c d k) := by
  unfold FixedLeftAdmissible
  infer_instance

theorem fixedLeft_admissible {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    FixedLeftAdmissible a b c d q.k := by
  refine ⟨q.k_le, ?_, ?_⟩
  · change couplingOrder q.intermediate c d ≤ min q.intermediate c
    rw [fixedLeft_outer_couplingOrder q]
    exact q.r_le
  · change q.intermediate + c -
      2 * couplingOrder q.intermediate c d = d
    rw [fixedLeft_outer_couplingOrder q]
    exact q.degree_eq

def fixedLeftChannelOfAdmissible {a b c d k : Nat}
    (hk : FixedLeftAdmissible a b c d k) :
    FixedLeftCGChannel a b c d where
  k := k
  k_le := hk.1
  r := couplingOrder (a + b - 2 * k) c d
  r_le := hk.2.1
  degree_eq := hk.2.2

theorem fixedLeftChannel_eq_of_k_eq {a b c d : Nat}
    (q u : FixedLeftCGChannel a b c d) (hku : q.k = u.k) : q = u := by
  have hru : q.r = u.r := by
    calc
      q.r = couplingOrder q.intermediate c d :=
        (fixedLeft_outer_couplingOrder q).symm
      _ = couplingOrder u.intermediate c d := by
        simp only [FixedLeftCGChannel.intermediate, hku]
      _ = u.r := fixedLeft_outer_couplingOrder u
  cases q with
  | mk k hk r hr hd =>
      cases u with
      | mk k' hk' r' hr' hd' =>
          dsimp only at hku hru
          subst k'
          subst r'
          rfl

theorem fixedLeftChannelOfAdmissible_roundtrip {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    fixedLeftChannelOfAdmissible (fixedLeft_admissible q) = q := by
  apply fixedLeftChannel_eq_of_k_eq
  rfl

def fixedLeftValidKs (a b c d : Nat) : List Nat :=
  (List.range (min a b + 1)).filter
    (fun k => decide (FixedLeftAdmissible a b c d k))

theorem mem_fixedLeftValidKs_iff (a b c d k : Nat) :
    k ∈ fixedLeftValidKs a b c d ↔
      FixedLeftAdmissible a b c d k := by
  constructor
  · intro hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  · intro hk
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (Nat.lt_succ_of_le hk.1),
      decide_eq_true hk⟩

theorem fixedLeftValidKs_complete {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    q.k ∈ fixedLeftValidKs a b c d :=
  (mem_fixedLeftValidKs_iff a b c d q.k).2 (fixedLeft_admissible q)

def fixedLeftChannelOfMem {a b c d k : Nat}
    (hk : k ∈ fixedLeftValidKs a b c d) :
    FixedLeftCGChannel a b c d :=
  fixedLeftChannelOfAdmissible
    ((mem_fixedLeftValidKs_iff a b c d k).1 hk)

@[simp] theorem fixedLeftChannelOfMem_k {a b c d k : Nat}
    (hk : k ∈ fixedLeftValidKs a b c d) :
    (fixedLeftChannelOfMem hk).k = k := rfl

def fixedLeftChannels (a b c d : Nat) :
    List (FixedLeftCGChannel a b c d) :=
  (fixedLeftValidKs a b c d).attach.map
    (fun k => fixedLeftChannelOfMem k.property)

theorem fixedLeftChannels_map_k (a b c d : Nat) :
    (fixedLeftChannels a b c d).map (fun q => q.k) =
      fixedLeftValidKs a b c d := by
  unfold fixedLeftChannels
  rw [List.map_map]
  simpa only [Function.comp_apply, fixedLeftChannelOfMem_k] using
    (List.attach_map_subtype_val (fixedLeftValidKs a b c d))

theorem fixedLeftChannels_complete {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    q ∈ fixedLeftChannels a b c d := by
  have hk : q.k ∈ (fixedLeftChannels a b c d).map (fun u => u.k) := by
    rw [fixedLeftChannels_map_k]
    exact fixedLeftValidKs_complete q
  rcases List.mem_map.mp hk with ⟨u, hu, huk⟩
  have huq : u = q := fixedLeftChannel_eq_of_k_eq u q huk
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

theorem fixedLeftValidKs_nodup (a b c d : Nat) :
    (fixedLeftValidKs a b c d).Nodup :=
  List.filter_sublist.nodup (range_nodup (min a b + 1))

private theorem nodup_of_map_nodup {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hm := List.nodup_cons.mp h
      refine List.nodup_cons.mpr
        ⟨?_, nodup_of_map_nodup f xs hm.2⟩
      intro hx
      exact hm.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem fixedLeftChannels_nodup (a b c d : Nat) :
    (fixedLeftChannels a b c d).Nodup := by
  apply nodup_of_map_nodup (fun q => q.k)
  rw [fixedLeftChannels_map_k]
  exact fixedLeftValidKs_nodup a b c d

#print axioms fixedLeft_admissible
#print axioms fixedLeftChannel_eq_of_k_eq
#print axioms fixedLeftChannelOfAdmissible_roundtrip
#print axioms mem_fixedLeftValidKs_iff
#print axioms fixedLeftValidKs_complete
#print axioms fixedLeftChannelOfMem_k
#print axioms fixedLeftChannels_map_k
#print axioms fixedLeftChannels_complete
#print axioms fixedLeftValidKs_nodup
#print axioms fixedLeftChannels_nodup

end YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
