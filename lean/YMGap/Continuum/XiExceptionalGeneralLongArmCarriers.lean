/-
# Uniform sharp carrier family for arbitrary long-pair count

For `n = k + 3`, the ambient alternating cycle has `2n + 4` occurrence
slots.  Its long arm contains `2n` interior occurrences.  The code indexed by
one long occurrence traverses the long arm once and replaces that occurrence
by four consecutive copies, using exactly three additional self steps.  The
resulting chain has `2n + 4` steps, exactly the available fuel, and hence
`2n + 5 = Gamma.length + 1` vertices.

The two parity families use the complete opposite-parity external mask; the
first `k = n - 3` entries also carry the corresponding compatible short-arm
tag.  This module proves target membership and occurrence-code injectivity
for all `k`, independently of activity normalization.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra
import YMGap.Continuum.XiExceptionalOccurrenceCodes

namespace YMGap.Continuum.XiExceptionalGeneralLongArmCarriers

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes

variable {L : Lattice} [DecidableEq L.Plaquette]

abbrev OBits :=
  YMGap.Continuum.XiExceptionalOccurrenceCodes.BitVec

inductive LongParity where
  | even | odd
deriving DecidableEq

def longCount (k : Nat) : Nat := k + 3

def ambientCount (k : Nat) : Nat := 2 * longCount k + 4

/-- `m+3, ..., 4`, the descending long interior for `m` occurrences. -/
def longDescending : Nat → List Nat
  | 0 => []
  | m + 1 => (m + 4) :: longDescending m

theorem longDescending_length (m : Nat) :
    (longDescending m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [longDescending, ih]

theorem longDescending_mem_bounds : ∀ {m x : Nat},
    x ∈ longDescending m → 4 ≤ x ∧ x < m + 4
  | 0, _, hx => by cases hx
  | m + 1, x, hx => by
      rcases List.mem_cons.mp hx with hhead | htail
      · subst x
        exact ⟨by omega, by omega⟩
      · have hb := longDescending_mem_bounds htail
        exact ⟨hb.1, by omega⟩

theorem longDescending_nodup : ∀ m : Nat,
    (longDescending m).Nodup
  | 0 => List.nodup_nil
  | m + 1 => by
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        have hb := longDescending_mem_bounds hmem
        omega
      · exact longDescending_nodup m

def baseTail (k : Nat) : List Nat :=
  longDescending (2 * longCount k) ++ [3]

theorem baseTail_length (k : Nat) :
    (baseTail k).length = 2 * longCount k + 1 := by
  simp [baseTail, longDescending_length]

theorem baseTail_mem_bounds {k x : Nat} (hx : x ∈ baseTail k) :
    x < ambientCount k := by
  simp only [baseTail, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with hlong | rfl
  · have hb := longDescending_mem_bounds hlong
    unfold ambientCount
    omega
  · unfold ambientCount longCount
    omega

theorem baseTail_nodup (k : Nat) : (baseTail k).Nodup := by
  unfold baseTail
  have general : ∀ m : Nat, (longDescending m ++ [3]).Nodup := by
    intro m
    induction m with
    | zero =>
        exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    | succ m ih =>
        simp only [longDescending, List.cons_append]
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hmem
          rcases hmem with hlong | heq
          · have hb := longDescending_mem_bounds hlong
            omega
          · omega
        · exact ih
  exact general _

/-- Replace the occurrence at position `p` by four copies. -/
def inflateAt : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, 0 => x :: x :: x :: x :: xs
  | x :: xs, p + 1 => x :: inflateAt xs p

theorem inflateAt_length : ∀ (xs : List Nat) (p : Nat),
    p < xs.length → (inflateAt xs p).length = xs.length + 3
  | [], _, h => by simp at h
  | _ :: xs, 0, _ => by simp [inflateAt]
  | _ :: xs, p + 1, h => by
      simp only [List.length_cons] at h ⊢
      simp only [inflateAt, List.length_cons]
      rw [inflateAt_length xs p (by omega)]

theorem inflateAt_mem : ∀ (xs : List Nat) (p y : Nat),
    y ∈ inflateAt xs p → y ∈ xs
  | [], _, _, h => by cases h
  | x :: xs, 0, y, h => by
      simp only [inflateAt, List.mem_cons] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | h
      all_goals simp_all
  | x :: xs, p + 1, y, h => by
      simp only [inflateAt, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (inflateAt_mem xs p y h)

theorem inflateAt_injective : ∀ (xs : List Nat), xs.Nodup →
    ∀ (p q : Nat), p < xs.length → q < xs.length →
      inflateAt xs p = inflateAt xs q → p = q
  | [], _, p, _, hp, _, _ => by simp at hp
  | x :: xs, hnd, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, q + 1, _, hq, heq => by
      have htail : x :: x :: x :: xs = inflateAt xs q := by
        injection heq
      have hxInflated : x ∈ inflateAt xs q := by
        rw [← htail]
        exact List.mem_cons_self
      have hxTail : x ∈ xs := inflateAt_mem xs q x hxInflated
      exact False.elim ((List.nodup_cons.mp hnd).1 hxTail)
  | x :: xs, hnd, p + 1, 0, hp, _, heq => by
      have htail : inflateAt xs p = x :: x :: x :: xs := by
        injection heq
      have hxInflated : x ∈ inflateAt xs p := by
        rw [htail]
        exact List.mem_cons_self
      have hxTail : x ∈ xs := inflateAt_mem xs p x hxInflated
      exact False.elim ((List.nodup_cons.mp hnd).1 hxTail)
  | x :: xs, hnd, p + 1, q + 1, hp, hq, heq => by
      have htail : inflateAt xs p = inflateAt xs q := by
        injection heq
      have ih := inflateAt_injective xs (List.nodup_cons.mp hnd).2
        p q (by simpa using hp) (by simpa using hq) htail
      exact congrArg Nat.succ ih

def slotPosition (n : Nat) : LongParity → Nat → Nat
  | .even, i => 2 * (n - 1 - i) + 1
  | .odd, i => 2 * (n - 1 - i)

theorem slotPosition_bound {n i : Nat} (side : LongParity)
    (hi : i < n) : slotPosition n side i < 2 * n := by
  cases side <;> simp only [slotPosition] <;> omega

theorem slotPosition_injective {n i j : Nat} {a b : LongParity}
    (hi : i < n) (hj : j < n)
    (hpos : slotPosition n a i = slotPosition n b j) :
    a = b ∧ i = j := by
  cases a <;> cases b <;> simp only [slotPosition] at hpos
  · constructor
    · rfl
    · have hi' : n - 1 - i + i = n - 1 := by omega
      have hj' : n - 1 - j + j = n - 1 := by omega
      omega
  · omega
  · omega
  · constructor
    · rfl
    · have hi' : n - 1 - i + i = n - 1 := by omega
      have hj' : n - 1 - j + j = n - 1 := by omega
      omega

def inflatedTail (k : Nat) (side : LongParity) (i : Nat) : List Nat :=
  inflateAt (baseTail k) (slotPosition (longCount k) side i)

theorem inflatedTail_length {k i : Nat} (side : LongParity)
    (hi : i < longCount k) :
    (inflatedTail k side i).length = ambientCount k := by
  unfold inflatedTail ambientCount
  rw [inflateAt_length _ _]
  · rw [baseTail_length]
  · rw [baseTail_length]
    have hp := slotPosition_bound side hi
    omega

theorem inflatedTail_mem_bounds {k i y : Nat} (side : LongParity)
    (hy : y ∈ inflatedTail k side i) : y < ambientCount k :=
  baseTail_mem_bounds (inflateAt_mem _ _ _ hy)

theorem inflatedTail_injective {k i j : Nat} {a b : LongParity}
    (hi : i < longCount k) (hj : j < longCount k)
    (htail : inflatedTail k a i = inflatedTail k b j) :
    a = b ∧ i = j := by
  have hp := slotPosition_bound a hi
  have hq := slotPosition_bound b hj
  have hpos := inflateAt_injective (baseTail k) (baseTail_nodup k)
    (slotPosition (longCount k) a i)
    (slotPosition (longCount k) b j)
    (by rw [baseTail_length]; omega)
    (by rw [baseTail_length]; omega) htail
  exact slotPosition_injective hi hj hpos

/-! ## Direct occurrence-chain encoding -/

def chainFromIndices {N : Nat} (background : OBits N) :
    List Nat → OccChainCode N
  | [] => .terminal background
  | i :: is => .step i (chainFromIndices background is)

theorem chainFromIndices_injective {N : Nat} (background : OBits N) :
    ∀ {xs ys : List Nat},
      chainFromIndices background xs = chainFromIndices background ys →
        xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
      injection h with hxy htail
      rw [hxy, chainFromIndices_injective background htail]

omit [DecidableEq L.Plaquette] in
theorem chainFromIndices_mem
    (Gamma : List (Polymer L)) (background : OBits Gamma.length) :
    ∀ (xs : List Nat) (fuel : Nat), xs.length ≤ fuel →
      (∀ i, i ∈ xs → i < Gamma.length) →
      chainFromIndices background xs ∈ occurrenceChainCodes Gamma fuel
  | [], fuel, _, _ => by
      induction fuel with
      | zero =>
          unfold chainFromIndices occurrenceChainCodes occurrenceTerminalCodes
          exact List.mem_map.mpr
            ⟨background, bitVectors_complete background, rfl⟩
      | succ fuel _ =>
          unfold chainFromIndices occurrenceChainCodes
          apply List.mem_append_left
          unfold occurrenceTerminalCodes
          exact List.mem_map.mpr
            ⟨background, bitVectors_complete background, rfl⟩
  | _ :: _, 0, h, _ => by simp at h
  | i :: is, fuel + 1, hlen, hbounds => by
      unfold chainFromIndices occurrenceChainCodes
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      have hi : i < Gamma.length := hbounds i List.mem_cons_self
      refine ⟨i, occurrenceIndices_complete hi, ?_⟩
      apply List.mem_map.mpr
      refine ⟨chainFromIndices background is, ?_, rfl⟩
      exact chainFromIndices_mem Gamma background is fuel (by simp at hlen; omega)
        (fun j hj => hbounds j (List.mem_cons_of_mem i hj))

/-! ## External masks and the sharp family -/

def bitsOfPred : (N : Nat) → (Nat → Bool) → OBits N
  | 0, _ => .nil
  | N + 1, p => .cons (p 0) (bitsOfPred N (fun i => p (i + 1)))

def castBitVec {m n : Nat} (h : m = n) (bits : OBits m) : OBits n :=
  h ▸ bits

def externalPred (k : Nat) (side : LongParity) (i j : Nat) : Bool :=
  match side with
  | .even =>
      (decide (i < k) && decide (j = 1)) ||
        (decide (5 ≤ j) && decide (j < ambientCount k) && decide (j % 2 = 1))
  | .odd =>
      (decide (i < k) && decide (j = 2)) ||
        (decide (4 ≤ j) && decide (j < ambientCount k) && decide (j % 2 = 0))

def externalBits (k : Nat) (side : LongParity) (i : Nat) :
    OBits (ambientCount k) :=
  bitsOfPred (ambientCount k) (externalPred k side i)

def emptyBits (Gamma : List (Polymer L)) : OBits Gamma.length :=
  bitsOfPred Gamma.length (fun _ => false)

def longCarrierCode (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (side : LongParity) (i : Nat) : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits Gamma) (inflatedTail k side i) }
    external := castBitVec hGamma.symm (externalBits k side i) }

/-- The canonical bounced short ear.  Its five-step tail is independent of
the long-arm count and fits every ambient size in this family. -/
def shortTail : List Nat := [1, 2, 1, 2, 3]

def shortCarrierCode (Gamma : List (Polymer L)) (k : Nat)
    (_hGamma : Gamma.length = ambientCount k) : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits Gamma) shortTail }
    external := emptyBits Gamma }

omit [DecidableEq L.Plaquette] in
theorem shortCarrierCode_mem
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    shortCarrierCode Gamma k hGamma ∈ occurrenceCarrierXiCodes Gamma := by
  unfold shortCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨emptyBits Gamma, bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices (emptyBits Gamma) shortTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete ?_, ?_⟩
  · rw [hGamma]
    unfold ambientCount longCount
    omega
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (emptyBits Gamma) shortTail, ?_, rfl⟩
  apply chainFromIndices_mem Gamma (emptyBits Gamma) shortTail Gamma.length
  · simp only [shortTail, List.length_cons, List.length_nil]
    rw [hGamma]
    unfold ambientCount longCount
    omega
  · intro j hj
    simp only [shortTail, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    all_goals rw [hGamma]; unfold ambientCount longCount; omega

omit [DecidableEq L.Plaquette] in
theorem longCarrierCode_mem
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (side : LongParity) {i : Nat} (hi : i < longCount k) :
    longCarrierCode Gamma k hGamma side i ∈ occurrenceCarrierXiCodes Gamma := by
  unfold longCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨castBitVec hGamma.symm (externalBits k side i),
    bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices (emptyBits Gamma) (inflatedTail k side i)⟩,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete ?_, ?_⟩
  · rw [hGamma]
    unfold ambientCount longCount
    omega
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (emptyBits Gamma) (inflatedTail k side i), ?_, rfl⟩
  apply chainFromIndices_mem Gamma (emptyBits Gamma) _ Gamma.length
  · rw [inflatedTail_length side hi, hGamma]
    exact Nat.le_refl _
  · intro j hj
    rw [hGamma]
    exact inflatedTail_mem_bounds side hj

omit [DecidableEq L.Plaquette] in
theorem longCarrierCode_injective
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    {a b : LongParity} {i j : Nat}
    (hi : i < longCount k) (hj : j < longCount k)
    (hcode : longCarrierCode Gamma k hGamma a i =
      longCarrierCode Gamma k hGamma b j) :
    a = b ∧ i = j := by
  have hcarrier := congrArg OccCarrierXiCodeAt.carrier hcode
  have hchain := congrArg OccCarrierCodeAt.chain hcarrier
  unfold longCarrierCode at hchain
  have htail := chainFromIndices_injective (emptyBits Gamma) hchain
  exact inflatedTail_injective hi hj htail

theorem occurrenceIndices_bound : ∀ {N i : Nat},
    i ∈ occurrenceIndices N → i < N
  | 0, _, hi => by cases hi
  | _ + 1, 0, _ => by omega
  | N + 1, i + 1, hi => by
      simp only [occurrenceIndices, List.mem_cons, List.mem_map] at hi
      rcases hi with hzero | ⟨j, hj, hji⟩
      · cases hzero
      · have e : j = i := Nat.succ.inj hji
        subst j
        have hb := occurrenceIndices_bound hj
        omega

theorem occurrenceIndices_length : ∀ N,
    (occurrenceIndices N).length = N
  | 0 => rfl
  | N + 1 => by
      simp only [occurrenceIndices, List.length_cons, List.length_map,
        occurrenceIndices_length N]

def sideCarrierCodes (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) (side : LongParity) :
    List (OccCarrierXiCodeAt Gamma) :=
  (occurrenceIndices (longCount k)).map
    (longCarrierCode Gamma k hGamma side)

def longCarrierFamily (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    List (OccCarrierXiCodeAt Gamma) :=
  sideCarrierCodes Gamma k hGamma .even ++
    sideCarrierCodes Gamma k hGamma .odd

def repairCarrierFamily (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    List (OccCarrierXiCodeAt Gamma) :=
  shortCarrierCode Gamma k hGamma :: longCarrierFamily Gamma k hGamma

omit [DecidableEq L.Plaquette] in
theorem sideCarrierCodes_nodup
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) (side : LongParity) :
    (sideCarrierCodes Gamma k hGamma side).Nodup := by
  unfold sideCarrierCodes
  apply nodup_map_of_injOn
  · exact occurrenceIndices_nodup _
  · intro i hi j hj hcode
    exact (longCarrierCode_injective Gamma k hGamma
      (occurrenceIndices_bound hi) (occurrenceIndices_bound hj) hcode).2

omit [DecidableEq L.Plaquette] in
theorem parityCarrierCodes_disjoint
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    ∀ code, code ∈ sideCarrierCodes Gamma k hGamma .even →
      code ∈ sideCarrierCodes Gamma k hGamma .odd → False := by
  intro code he ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  obtain ⟨j, hj, hcode⟩ := List.mem_map.mp ho
  have hp := longCarrierCode_injective Gamma k hGamma
    (occurrenceIndices_bound hi) (occurrenceIndices_bound hj) hcode.symm
  cases hp.1

omit [DecidableEq L.Plaquette] in
theorem shortCarrierCode_not_mem_longCarrierFamily
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    shortCarrierCode Gamma k hGamma ∉ longCarrierFamily Gamma k hGamma := by
  intro hmem
  simp only [longCarrierFamily, sideCarrierCodes, List.mem_append,
    List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hcode⟩ | ⟨i, hi, hcode⟩
  · have hchain := congrArg
      (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hcode
    unfold shortCarrierCode longCarrierCode at hchain
    have htail := chainFromIndices_injective (emptyBits Gamma) hchain.symm
    have hlen := congrArg List.length htail
    rw [inflatedTail_length .even (occurrenceIndices_bound hi)] at hlen
    simp only [shortTail, List.length_cons, List.length_nil] at hlen
    unfold ambientCount longCount at hlen
    omega
  · have hchain := congrArg
      (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hcode
    unfold shortCarrierCode longCarrierCode at hchain
    have htail := chainFromIndices_injective (emptyBits Gamma) hchain.symm
    have hlen := congrArg List.length htail
    rw [inflatedTail_length .odd (occurrenceIndices_bound hi)] at hlen
    simp only [shortTail, List.length_cons, List.length_nil] at hlen
    unfold ambientCount longCount at hlen
    omega

omit [DecidableEq L.Plaquette] in
theorem longCarrierFamily_nodup
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    (longCarrierFamily Gamma k hGamma).Nodup := by
  unfold longCarrierFamily
  apply List.nodup_append.mpr
  refine ⟨sideCarrierCodes_nodup Gamma k hGamma .even,
    sideCarrierCodes_nodup Gamma k hGamma .odd, ?_⟩
  intro a ha b hb hab
  rw [← hab] at hb
  exact parityCarrierCodes_disjoint Gamma k hGamma a ha hb

omit [DecidableEq L.Plaquette] in
theorem longCarrierFamily_mem
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ longCarrierFamily Gamma k hGamma) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  simp only [longCarrierFamily, sideCarrierCodes, List.mem_append,
    List.mem_map] at hcode
  rcases hcode with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact longCarrierCode_mem Gamma k hGamma .even
      (occurrenceIndices_bound hi)
  · exact longCarrierCode_mem Gamma k hGamma .odd
      (occurrenceIndices_bound hi)

omit [DecidableEq L.Plaquette] in
theorem repairCarrierFamily_nodup
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    (repairCarrierFamily Gamma k hGamma).Nodup := by
  exact List.nodup_cons.mpr
    ⟨shortCarrierCode_not_mem_longCarrierFamily Gamma k hGamma,
      longCarrierFamily_nodup Gamma k hGamma⟩

omit [DecidableEq L.Plaquette] in
theorem repairCarrierFamily_mem
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ repairCarrierFamily Gamma k hGamma) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  rcases List.mem_cons.mp hcode with rfl | hlong
  · exact shortCarrierCode_mem Gamma k hGamma
  · exact longCarrierFamily_mem Gamma k hGamma code hlong

omit [DecidableEq L.Plaquette] in
theorem longCarrierFamily_length
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    (longCarrierFamily Gamma k hGamma).length = 2 * longCount k := by
  simp [longCarrierFamily, sideCarrierCodes, occurrenceIndices_length]
  omega

omit [DecidableEq L.Plaquette] in
theorem repairCarrierFamily_length
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    (repairCarrierFamily Gamma k hGamma).length = 2 * longCount k + 1 := by
  simp [repairCarrierFamily, longCarrierFamily_length]

#print axioms inflateAt_injective
#print axioms baseTail_nodup
#print axioms longDescending_mem_bounds
#print axioms longDescending_nodup
#print axioms baseTail_mem_bounds
#print axioms inflatedTail_length
#print axioms inflatedTail_mem_bounds
#print axioms slotPosition_injective
#print axioms inflatedTail_injective
#print axioms chainFromIndices_mem
#print axioms longCarrierCode_mem
#print axioms longCarrierCode_injective
#print axioms longCarrierFamily_nodup
#print axioms longCarrierFamily_mem
#print axioms longCarrierFamily_length
#print axioms shortCarrierCode_mem
#print axioms shortCarrierCode_not_mem_longCarrierFamily
#print axioms repairCarrierFamily_nodup
#print axioms repairCarrierFamily_mem
#print axioms repairCarrierFamily_length

end YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
