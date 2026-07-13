/-
# Occurrence-distinct codes for exceptional Xi sums

Value-level lists of polymers do not remember which occurrence of a duplicate
ambient polymer was selected.  This file introduces length-indexed Boolean
vectors as canonical occurrence masks.  Their enumeration is complete and
`Nodup`; selecting ambient polymers from all masks reproduces the existing
`sublists` enumeration exactly, including its multiplicities.

Pairs of masks are enumerated by a constructive Cartesian product and are
again `Nodup`.  These are the source codes needed for a genuinely injective
exceptional-pair map.
-/

import YMGap.Continuum.XiExceptionalCarrierCode

namespace YMGap.Continuum.XiExceptionalOccurrenceCodes

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Length-indexed Boolean vectors -/

inductive BitVec : Nat → Type
  | nil : BitVec 0
  | cons {n : Nat} (head : Bool) (tail : BitVec n) : BitVec (n + 1)
deriving DecidableEq

def bitVectors : (n : Nat) → List (BitVec n)
  | 0 => [.nil]
  | n + 1 =>
      (bitVectors n).map (BitVec.cons false) ++
        (bitVectors n).map (BitVec.cons true)

theorem nodup_map_of_injOn {a b : Type} (f : a → b) :
    ∀ (xs : List a), xs.Nodup →
      (∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) →
      (xs.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnd, hinj => by
      have hp := List.nodup_cons.mp hnd
      refine List.nodup_cons.mpr ⟨?_,
        nodup_map_of_injOn f xs hp.2
          (fun y hy z hz => hinj y (List.mem_cons_of_mem x hy)
            z (List.mem_cons_of_mem x hz))⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      have hxy := hinj x List.mem_cons_self y
        (List.mem_cons_of_mem x hy) heq.symm
      exact hp.1 (hxy ▸ hy)

theorem bitVectors_complete : ∀ {n : Nat} (v : BitVec n), v ∈ bitVectors n
  | 0, .nil => List.mem_cons_self
  | _ + 1, .cons false tail => by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨tail, bitVectors_complete tail, rfl⟩
  | _ + 1, .cons true tail => by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨tail, bitVectors_complete tail, rfl⟩

theorem bitVectors_nodup : ∀ n, (bitVectors n).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => by
      have ih := bitVectors_nodup n
      have hfalse : ((bitVectors n).map (BitVec.cons false)).Nodup :=
        nodup_map_of_injOn (BitVec.cons false) (bitVectors n) ih
          (fun _ _ _ _ h => by injection h)
      have htrue : ((bitVectors n).map (BitVec.cons true)).Nodup :=
        nodup_map_of_injOn (BitVec.cons true) (bitVectors n) ih
          (fun _ _ _ _ h => by injection h)
      apply List.nodup_append.mpr
      refine ⟨hfalse, htrue, ?_⟩
      intro x hx y hy hxy
      obtain ⟨u, hu, hux⟩ := List.mem_map.mp hx
      obtain ⟨v, hv, hvy⟩ := List.mem_map.mp hy
      rw [← hux, ← hvy] at hxy
      injection hxy with _ hhead _
      exact Bool.false_ne_true hhead

def BitVec.at : {n : Nat} → BitVec n → Nat → Bool
  | 0, .nil, _ => false
  | _ + 1, .cons b _, 0 => b
  | _ + 1, .cons _ tail, i + 1 => tail.at i

theorem BitVec.ext : ∀ {n : Nat} {u v : BitVec n},
    (∀ i, u.at i = v.at i) → u = v
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons bu tu, .cons bv tv, h => by
      have hb : bu = bv := h 0
      have ht : tu = tv := BitVec.ext (fun i => h (i + 1))
      subst bv
      subst tv
      rfl

/-! ## 2. Selecting an ambient family by occurrence -/

def selectByBits : (xs : List a) → BitVec xs.length → List a
  | [], .nil => []
  | x :: xs, .cons b tail =>
      if b then x :: selectByBits xs tail else selectByBits xs tail

@[simp] theorem selectByBits_nil :
    selectByBits ([] : List a) .nil = [] := rfl

@[simp] theorem selectByBits_cons_false (x : a) (xs : List a)
    (tail : BitVec xs.length) :
    selectByBits (x :: xs) (.cons false tail) = selectByBits xs tail := rfl

@[simp] theorem selectByBits_cons_true (x : a) (xs : List a)
    (tail : BitVec xs.length) :
    selectByBits (x :: xs) (.cons true tail) = x :: selectByBits xs tail := rfl

theorem map_select_cons_false (x : a) (xs : List a) :
    ∀ vs : List (BitVec xs.length),
      vs.map (selectByBits (x :: xs) ∘ BitVec.cons false) =
        vs.map (selectByBits xs)
  | [] => rfl
  | _ :: vs => by
      simp only [List.map_cons, Function.comp_apply, selectByBits_cons_false,
        map_select_cons_false x xs vs]

theorem map_select_cons_true (x : a) (xs : List a) :
    ∀ vs : List (BitVec xs.length),
      vs.map (selectByBits (x :: xs) ∘ BitVec.cons true) =
        vs.map ((fun s => x :: s) ∘ selectByBits xs)
  | [] => rfl
  | _ :: vs => by
      simp only [List.map_cons, Function.comp_apply, selectByBits_cons_true,
        map_select_cons_true x xs vs]

/-- The occurrence-mask enumeration maps exactly to the existing sublist
enumeration, in the same order and with the same duplicate-value
multiplicities. -/
theorem select_bitVectors_eq_sublists : ∀ xs : List a,
    (bitVectors xs.length).map (selectByBits xs) = sublists xs
  | [] => rfl
  | x :: xs => by
      simp only [List.length_cons, bitVectors, List.map_append, List.map_map,
        sublists_cons]
      have hf := map_select_cons_false x xs (bitVectors xs.length)
      have ht := map_select_cons_true x xs (bitVectors xs.length)
      have hleft := congrArg
        (fun z => z ++
          (bitVectors xs.length).map
            (selectByBits (x :: xs) ∘ BitVec.cons true)) hf
      have hright := congrArg
        (fun z => (bitVectors xs.length).map (selectByBits xs) ++ z) ht
      exact Eq.trans hleft (Eq.trans hright (by
        rw [← List.map_map, select_bitVectors_eq_sublists xs]))

/-- Summing the old admissible-family weight over occurrence masks gives
exactly the old restricted partition function.  This is the weighted form
of `select_bitVectors_eq_sublists`. -/
theorem admissibleFamilyWeight_bitVectors_eqv_XiR
    (w : Q') (q : Polymer L → Bool) (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) :
    qListSum
        (fun bits => admissibleFamilyWeight w q label
          (selectByBits Gamma bits))
        (bitVectors Gamma.length) ≈ XiR w q Gamma label := by
  rw [← qListSum_map]
  rw [select_bitVectors_eq_sublists]
  exact admissibleFamilyWeight_sum_eqv_XiR w q Gamma label

/-! ## 3. Canonical pairs of occurrence masks -/

abbrev MaskPair (n : Nat) := BitVec n × BitVec n

def maskPairs (n : Nat) : List (MaskPair n) :=
  (bitVectors n).flatMap (fun left =>
    (bitVectors n).map (fun right => (left, right)))

theorem maskPairs_complete {n : Nat} (pair : MaskPair n) :
    pair ∈ maskPairs n := by
  unfold maskPairs
  apply List.mem_flatMap.mpr
  exact ⟨pair.1, bitVectors_complete pair.1,
    List.mem_map.mpr ⟨pair.2, bitVectors_complete pair.2, by cases pair; rfl⟩⟩

theorem nodup_cartesian {a b : Type} (xs : List a) (ys : List b)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hp := List.nodup_cons.mp hxs
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, ih hp.2, ?_⟩
      · exact nodup_map_of_injOn (fun y => (x, y)) ys hys
          (fun _ _ _ _ h => by injection h)
      · intro p hpMem q hqMem hpq
        obtain ⟨y, hy, hyp⟩ := List.mem_map.mp hpMem
        obtain ⟨z, hz, hzq⟩ := List.mem_flatMap.mp hqMem
        obtain ⟨t, ht, htq⟩ := List.mem_map.mp hzq
        rw [← hyp, ← htq] at hpq
        have hxz : x = z := by injection hpq
        exact hp.1 (hxz ▸ hz)

theorem maskPairs_nodup (n : Nat) : (maskPairs n).Nodup :=
  nodup_cartesian (bitVectors n) (bitVectors n)
    (bitVectors_nodup n) (bitVectors_nodup n)

def leftFamily (xs : List a) (pair : MaskPair xs.length) : List a :=
  selectByBits xs pair.1

def rightFamily (xs : List a) (pair : MaskPair xs.length) : List a :=
  selectByBits xs pair.2

theorem MaskPair.ext {n : Nat} {p q : MaskPair n}
    (hleft : ∀ i, p.1.at i = q.1.at i)
    (hright : ∀ i, p.2.at i = q.2.at i) : p = q := by
  apply Prod.ext
  · exact BitVec.ext hleft
  · exact BitVec.ext hright

/-! ## 4. Occurrence-indexed carrier codes -/

/-- Canonical occurrence indices.  The recursive presentation makes their
alignment with `polyAt` transparent without importing a finite-set API. -/
def occurrenceIndices : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: (occurrenceIndices n).map Nat.succ

theorem occurrenceIndices_complete : ∀ {n i : Nat}, i < n →
    i ∈ occurrenceIndices n
  | 0, _, hi => by omega
  | _ + 1, 0, _ => List.mem_cons_self
  | n + 1, i + 1, hi => by
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨i, occurrenceIndices_complete (by omega), rfl⟩

theorem occurrenceIndices_nodup : ∀ n, (occurrenceIndices n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      apply List.nodup_cons.mpr
      constructor
      · intro hzero
        obtain ⟨i, _, hi⟩ := List.mem_map.mp hzero
        cases hi
      · exact nodup_map_of_injOn Nat.succ (occurrenceIndices n)
          (occurrenceIndices_nodup n)
          (fun _ _ _ _ h => Nat.succ.inj h)

theorem map_polyAt_occurrenceIndices : ∀ Gamma : List (Polymer L),
    (occurrenceIndices Gamma.length).map (polyAt Gamma) = Gamma
  | [] => rfl
  | X :: Gamma => by
      simp only [List.length_cons, occurrenceIndices, List.map_cons,
        polyAt_cons_zero, List.map_map]
      have htail :
          (occurrenceIndices Gamma.length).map
              (polyAt (X :: Gamma) ∘ Nat.succ) =
            (occurrenceIndices Gamma.length).map (polyAt Gamma) := by
        apply List.map_congr_left
        intro i _
        exact polyAt_cons_succ X Gamma i
      rw [htail, map_polyAt_occurrenceIndices Gamma]

/-- A chain whose recursive choices and terminal background remember ambient
occurrences rather than merely polymer values. -/
inductive OccChainCode (n : Nat) : Type
  | terminal (background : BitVec n)
  | step (next : Nat) (rest : OccChainCode n)
deriving DecidableEq

def eraseOccChainCode (Gamma : List (Polymer L)) :
    OccChainCode Gamma.length → ChainCode L.Plaquette
  | .terminal background =>
      .terminal (selectByBits Gamma background)
  | .step next rest =>
      .step (polyAt Gamma next) (eraseOccChainCode Gamma rest)

def occurrenceTerminalCodes (Gamma : List (Polymer L)) :
    List (OccChainCode Gamma.length) :=
  (bitVectors Gamma.length).map OccChainCode.terminal

def occurrenceChainCodes (Gamma : List (Polymer L)) :
    Nat → List (OccChainCode Gamma.length)
  | 0 => occurrenceTerminalCodes Gamma
  | fuel + 1 =>
      occurrenceTerminalCodes Gamma ++
        (occurrenceIndices Gamma.length).flatMap (fun next =>
          (occurrenceChainCodes Gamma fuel).map (OccChainCode.step next))

theorem erase_occurrenceTerminalCodes (Gamma : List (Polymer L)) :
    (occurrenceTerminalCodes Gamma).map (eraseOccChainCode Gamma) =
      terminalCodes Gamma := by
  unfold occurrenceTerminalCodes terminalCodes
  rw [List.map_map]
  change
    (bitVectors Gamma.length).map
        (ChainCode.terminal ∘ selectByBits Gamma) =
      (sublists Gamma).map ChainCode.terminal
  rw [← List.map_map, select_bitVectors_eq_sublists]

theorem map_erase_occurrence_step_blocks
    (Gamma : List (Polymer L)) (codes : List (OccChainCode Gamma.length))
    (indices : List Nat) :
    (indices.flatMap (fun next =>
        codes.map (OccChainCode.step next))).map
        (eraseOccChainCode Gamma) =
      (indices.map (polyAt Gamma)).flatMap (fun next =>
        (codes.map (eraseOccChainCode Gamma)).map (ChainCode.step next)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      have hblock :
          (codes.map (OccChainCode.step i)).map
              (eraseOccChainCode Gamma) =
            (codes.map (eraseOccChainCode Gamma)).map
              (ChainCode.step (polyAt Gamma i)) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro code _
        cases code <;> rfl
      rw [hblock, ih]

theorem erase_occurrenceChainCodes (Gamma : List (Polymer L)) :
    ∀ fuel : Nat,
      (occurrenceChainCodes Gamma fuel).map (eraseOccChainCode Gamma) =
        chainCodes Gamma fuel
  | 0 => erase_occurrenceTerminalCodes Gamma
  | fuel + 1 => by
      unfold occurrenceChainCodes chainCodes
      rw [List.map_append, erase_occurrenceTerminalCodes]
      rw [map_erase_occurrence_step_blocks]
      rw [map_polyAt_occurrenceIndices, erase_occurrenceChainCodes Gamma fuel]

/-- The dependent carrier code is packaged as a structure so its chain field
has the ambient length while the lattice remains inferable. -/
structure OccCarrierCodeAt (Gamma : List (Polymer L)) : Type where
  start : Nat
  chain : OccChainCode Gamma.length
deriving DecidableEq

def eraseOccCarrierCode (Gamma : List (Polymer L))
    (code : OccCarrierCodeAt Gamma) : CarrierCode L :=
  (polyAt Gamma code.start, eraseOccChainCode Gamma code.chain)

def occurrenceCarrierCodes (Gamma : List (Polymer L)) :
    List (OccCarrierCodeAt Gamma) :=
  (occurrenceIndices Gamma.length).flatMap (fun start =>
    (occurrenceChainCodes Gamma Gamma.length).map
      (fun chain => ⟨start, chain⟩))

theorem map_erase_occurrence_carrier_blocks
    (Gamma : List (Polymer L)) (codes : List (OccChainCode Gamma.length))
    (indices : List Nat) :
    (indices.flatMap (fun start =>
        codes.map (fun chain => OccCarrierCodeAt.mk start chain))).map
        (eraseOccCarrierCode Gamma) =
      (indices.map (polyAt Gamma)).flatMap (fun start =>
        (codes.map (eraseOccChainCode Gamma)).map
          (fun chain => (start, chain))) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      have hblock :
          (codes.map (fun chain => OccCarrierCodeAt.mk i chain)).map
              (eraseOccCarrierCode Gamma) =
            (codes.map (eraseOccChainCode Gamma)).map
              (fun chain => (polyAt Gamma i, chain)) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro code _
        cases code <;> rfl
      rw [hblock, ih]

theorem erase_occurrenceCarrierCodes (Gamma : List (Polymer L)) :
    (occurrenceCarrierCodes Gamma).map (eraseOccCarrierCode Gamma) =
      carrierCodes Gamma := by
  unfold occurrenceCarrierCodes carrierCodes
  rw [map_erase_occurrence_carrier_blocks]
  rw [map_polyAt_occurrenceIndices,
    erase_occurrenceChainCodes Gamma Gamma.length]

structure OccCarrierXiCodeAt (Gamma : List (Polymer L)) : Type where
  carrier : OccCarrierCodeAt Gamma
  external : BitVec Gamma.length
deriving DecidableEq

def eraseOccCarrierXiCode (Gamma : List (Polymer L))
    (code : OccCarrierXiCodeAt Gamma) : CarrierXiCode L :=
  (eraseOccCarrierCode Gamma code.carrier,
    selectByBits Gamma code.external)

def occurrenceCarrierXiCodes (Gamma : List (Polymer L)) :
    List (OccCarrierXiCodeAt Gamma) :=
  (bitVectors Gamma.length).flatMap (fun external =>
    (occurrenceCarrierCodes Gamma).map
      (fun carrier => ⟨carrier, external⟩))

theorem map_erase_occurrence_xi_blocks
    (Gamma : List (Polymer L)) (carriers : List (OccCarrierCodeAt Gamma))
    (masks : List (BitVec Gamma.length)) :
    (masks.flatMap (fun external =>
        carriers.map (fun carrier => OccCarrierXiCodeAt.mk carrier external))).map
        (eraseOccCarrierXiCode Gamma) =
      (masks.map (selectByBits Gamma)).flatMap (fun external =>
        (carriers.map (eraseOccCarrierCode Gamma)).map
          (fun carrier => (carrier, external))) := by
  induction masks with
  | nil => rfl
  | cons bits masks ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      have hblock :
          (carriers.map
              (fun carrier => OccCarrierXiCodeAt.mk carrier bits)).map
              (eraseOccCarrierXiCode Gamma) =
            (carriers.map (eraseOccCarrierCode Gamma)).map
              (fun carrier => (carrier, selectByBits Gamma bits)) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro carrier _
        cases carrier
        rfl
      rw [hblock, ih]

theorem erase_occurrenceCarrierXiCodes (Gamma : List (Polymer L)) :
    (occurrenceCarrierXiCodes Gamma).map (eraseOccCarrierXiCode Gamma) =
      carrierXiCodes Gamma := by
  unfold occurrenceCarrierXiCodes carrierXiCodes
  rw [map_erase_occurrence_xi_blocks]
  rw [select_bitVectors_eq_sublists, erase_occurrenceCarrierCodes]

def occurrenceCarrierXiCodeWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (code : OccCarrierXiCodeAt Gamma) : Q' :=
  carrierXiCodeWeight w qP b1 b2 Gamma label
    (eraseOccCarrierXiCode Gamma code)

theorem occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) ≈
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  unfold occurrenceCarrierXiCodeWeight
  rw [← qListSum_map, erase_occurrenceCarrierXiCodes]
  exact carrierXiCodes_sum_eqv_carrier_mul_XiR w qP b1 b2 Gamma label

theorem occurrenceCarrierXiCodeWeight_nonnegative {w : Q'}
    (hw : (0 : Q') ≤ w) (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (code : OccCarrierXiCodeAt Gamma) :
    (0 : Q') ≤ occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label code :=
  carrierXiCodeWeight_nonnegative hw qP b1 b2 Gamma label
    (eraseOccCarrierXiCode Gamma code)

#print axioms bitVectors_complete
#print axioms bitVectors_nodup
#print axioms BitVec.ext
#print axioms select_bitVectors_eq_sublists
#print axioms maskPairs_complete
#print axioms maskPairs_nodup
#print axioms MaskPair.ext
#print axioms occurrenceIndices_complete
#print axioms occurrenceIndices_nodup
#print axioms map_polyAt_occurrenceIndices
#print axioms erase_occurrenceChainCodes
#print axioms erase_occurrenceCarrierXiCodes
#print axioms occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
#print axioms occurrenceCarrierXiCodeWeight_nonnegative

end YMGap.Continuum.XiExceptionalOccurrenceCodes
