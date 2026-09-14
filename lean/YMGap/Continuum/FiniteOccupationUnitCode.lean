/-
# Count finite occupation profiles by their mass, not their cutoff

A profile emits one coordinate symbol for each occupation unit. The word
length is exactly total mass H, and every symbol is below the profile
length m. Equal-length profiles are recovered from their words, so a
duplicate-free family of mass H has at most m^H members. Zero mass is
allowed by the compiler; excluding it is a separate hypothesis when
summing a nonzero tail. No list of m^H words is evaluated here.
-/

import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.FiniteOccupationUnitCode

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection

def mass : List Nat → Nat
  | [] => 0
  | value::rest => value+mass rest

def unitWord : List Nat → List Nat
  | [] => []
  | value::rest => List.replicate value 0 ++ (unitWord rest).map Nat.succ

def zeroCount : List Nat → Nat
  | [] => 0
  | value::rest => (if value = 0 then 1 else 0)+zeroCount rest

def peel : List Nat → List Nat
  | [] => []
  | value::rest => if value = 0 then peel rest else (value-1)::peel rest

theorem zeroCount_prefix (n : Nat) (word : List Nat) :
    zeroCount (List.replicate n 0 ++ word.map Nat.succ) = n := by
  have hz : ∀ xs : List Nat, zeroCount (xs.map Nat.succ) = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, zeroCount, Nat.succ_ne_zero,
        ↓reduceIte, Nat.zero_add] using ih
  induction n with
  | zero => exact hz word
  | succ n ih =>
    change 1+zeroCount (List.replicate n 0 ++ word.map Nat.succ) = n+1
    rw [ih, Nat.add_comm]

theorem peel_prefix (n : Nat) (word : List Nat) :
    peel (List.replicate n 0 ++ word.map Nat.succ) = word := by
  have hp : ∀ xs : List Nat, peel (xs.map Nat.succ) = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, peel, Nat.succ_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel] using congrArg (List.cons x) ih
  induction n with
  | zero => exact hp word
  | succ n ih => exact ih

theorem unitWord_injective : ∀ left right : List Nat,
    left.length = right.length → unitWord left = unitWord right → left = right
  | [], [], _, _ => rfl
  | [], _::_, hl, _ => by cases hl
  | _::_, [], hl, _ => by cases hl
  | a::left, b::right, hl, he => by
    have hh := congrArg zeroCount he
    change zeroCount (List.replicate a 0 ++ (unitWord left).map Nat.succ) =
      zeroCount (List.replicate b 0 ++ (unitWord right).map Nat.succ) at hh
    rw [zeroCount_prefix, zeroCount_prefix] at hh
    have ht := congrArg peel he
    change peel (List.replicate a 0 ++ (unitWord left).map Nat.succ) =
      peel (List.replicate b 0 ++ (unitWord right).map Nat.succ) at ht
    rw [peel_prefix, peel_prefix] at ht
    rw [hh, unitWord_injective left right (Nat.succ.inj hl) ht]

theorem unitWord_length : ∀ values : List Nat, (unitWord values).length = mass values
  | [] => rfl
  | value::rest => by
    rw [unitWord, List.length_append, List.length_replicate, List.length_map, unitWord_length]
    rfl

theorem unitWord_entry_lt : ∀ values : List Nat, ∀ entry, entry ∈ unitWord values → entry < values.length
  | [], _, he => by cases he
  | value::rest, entry, he => by
    rcases List.mem_append.mp he with he | he
    · have hz := List.eq_of_mem_replicate he
      rw [hz]
      exact Nat.zero_lt_succ _
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
      exact Nat.succ_lt_succ (unitWord_entry_lt rest x hx)

theorem unitWord_mem (m H : Nat) (values : List Nat) (hl : values.length ≤ m) (hm : mass values = H) :
    unitWord values ∈ allSeqs m H :=
  mem_allSeqs m H _ ((unitWord_length values).trans hm)
    (fun entry he => Nat.lt_of_lt_of_le (unitWord_entry_lt values entry he) hl)

theorem mass_stratum_count (m H : Nat) (profiles : List (List Nat)) (hn : profiles.Nodup)
    (hl : ∀ values, values ∈ profiles → values.length = m)
    (hm : ∀ values, values ∈ profiles → mass values = H) : profiles.length ≤ m^H := by
  have hi := nodup_map_of_injOn unitWord profiles hn
    (fun a ha b hb he => unitWord_injective a b ((hl a ha).trans (hl b hb).symm) he)
  have hc := nodup_subset_length_le (profiles.map unitWord) (allSeqs m H) hi (by
    intro code hcode
    obtain ⟨values,hv,rfl⟩ := List.mem_map.mp hcode
    exact unitWord_mem m H values (Nat.le_of_eq (hl values hv)) (hm values hv))
  rw [List.length_map, length_allSeqs] at hc
  exact hc

end YMGap.Continuum.FiniteOccupationUnitCode

#print axioms YMGap.Continuum.FiniteOccupationUnitCode.mass
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.unitWord
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.zeroCount
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.peel
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.zeroCount_prefix
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.peel_prefix
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.unitWord_injective
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.unitWord_length
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.unitWord_entry_lt
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.unitWord_mem
#print axioms YMGap.Continuum.FiniteOccupationUnitCode.mass_stratum_count
