/-
# DualKappa — the sign anomaly's no-local-gauge theorem, in Lean

Standalone spike (pattern of `cat_structural_spike`): own toolchain,
zero imports from the main tree, no Mathlib, kernel `decide` only.
Target gate: `{propext, Quot.sound}` (AGENTS.md Rule 1).

**STATUS: UNBUILT.**  Authored in the cloud session of 2026-07-24,
where no Lean toolchain is available (binary downloads blocked).
Build Mac-side under the session-lock discipline; expect at most
API-level touch-ups — every proof below is by literal `decide` or
first-principles induction on local definitions.

## What is formalized

The combinatorial core of the anomaly certificate
(notes/dual-positivity-survival.md, P7): twenty spin configurations
on the 4-cube boundary such that

  1. every face-local datum `(face, spin)` and every edge-local datum
     `(edge, incident spin triple)` occurs an **even** number of times
     across the twenty (proved here by kernel `decide` on the literal
     key-code lists), and
  2. the amplitude-sign parity across the twenty is **odd** (the sign
     table is literal data; its provenance is the exact machine
     computation, arbitrated twice — vertex 6j product and raw
     quaternion Haar moments, which agree to the digit).

**Theorem (`no_local_gauge`).**  No assignment of sign bits to local
data reproduces the recorded sign table: local parities XOR to
`false` over the certificate, the table XORs to `true`.

Key encoding (injective, computed by the exact engine):
face key  (fi, n)         ↦ 1000 + 10*fi + n
edge key  (ei, (a,b,c))   ↦ 100000 + 1000*ei + 100*a + 10*b + c

## Wiring TODO (main-tree integration)

Replace the literal `signBits` by the main tree's own Haar evaluation
of the twenty amplitudes (the quaternion-block `finiteProductHaar`
machinery computes them; this spike's data then becomes a theorem of
the spine, not an input).  Frontier interfaces for the remaining
program targets are typed at the end of this file.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace DualKappa

/-! ## Elementary list machinery (self-contained) -/

def countNat (k : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x = k then 1 else 0) + countNat k xs

def countTrue (w : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: xs => (if w x then 1 else 0) + countTrue w xs

def eraseFirst (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = k then xs else x :: eraseFirst k xs

def parity (n : Nat) : Bool := n % 2 = 1

def xorList : List Bool → Bool
  | [] => false
  | b :: bs => xor b (xorList bs)

theorem countTrue_append (w : Nat → Bool) (l₁ l₂ : List Nat) :
    countTrue w (l₁ ++ l₂) = countTrue w l₁ + countTrue w l₂ := by
  induction l₁ with
  | nil => simp [countTrue]
  | cons x xs ih => simp [countTrue, ih, Nat.add_assoc]

theorem parity_add (m n : Nat) :
    parity (m + n) = xor (parity m) (parity n) := by
  unfold parity
  have hmn : (m + n) % 2 = (m % 2 + n % 2) % 2 := Nat.add_mod m n 2
  cases Nat.mod_two_eq_zero_or_one m with
  | inl hm =>
    cases Nat.mod_two_eq_zero_or_one n with
    | inl hn => simp [hmn, hm, hn]
    | inr hn => simp [hmn, hm, hn]
  | inr hm =>
    cases Nat.mod_two_eq_zero_or_one n with
    | inl hn => simp [hmn, hm, hn]
    | inr hn => simp [hmn, hm, hn]

/-- membership-erase count identity, first principles -/
theorem countTrue_eraseFirst (w : Nat → Bool) (k : Nat) :
    ∀ l : List Nat, k ∈ l →
      countTrue w l = (if w k then 1 else 0) + countTrue w (eraseFirst k l)
  | [], h => nomatch h
  | x :: xs, h => by
    by_cases hx : x = k
    · subst hx; simp [countTrue, eraseFirst]
    · have hk : k ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact h'
      simp [countTrue, eraseFirst, hx, countTrue_eraseFirst w k xs hk]
      omega

theorem countNat_eraseFirst (j k : Nat) :
    ∀ l : List Nat, k ∈ l →
      countNat j l = (if k = j then 1 else 0) + countNat j (eraseFirst k l)
  | [], h => nomatch h
  | x :: xs, h => by
    by_cases hx : x = k
    · subst hx; simp [countNat, eraseFirst]
    · have hk : k ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact h'
      simp [countNat, eraseFirst, hx, countNat_eraseFirst j k xs hk]
      omega

theorem countNat_eq_zero_of_not_mem (j : Nat) :
    ∀ l : List Nat, j ∉ l → countNat j l = 0
  | [], _ => rfl
  | x :: xs, h => by
    have hx : ¬ x = j := fun e => h (by rw [← e]; exact List.mem_cons_self)
    have hxs : j ∉ xs := fun m => h (List.mem_cons_of_mem x m)
    simp [countNat, hx, countNat_eq_zero_of_not_mem j xs hxs]

theorem eraseFirst_length_le (k : Nat) :
    ∀ l : List Nat, (eraseFirst k l).length ≤ l.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    by_cases hx : x = k
    · simp [eraseFirst, hx, Nat.le_succ]
    · simp [eraseFirst, hx]
      exact eraseFirst_length_le k xs

theorem mem_of_mem_eraseFirst (j k : Nat) :
    ∀ l : List Nat, j ∈ eraseFirst k l → j ∈ l
  | [], h => by simp [eraseFirst] at h
  | x :: xs, h => by
    by_cases hx : x = k
    · simp [eraseFirst, hx] at h
      exact List.mem_cons_of_mem x h
    · simp [eraseFirst, hx] at h
      cases h with
      | inl he => exact he ▸ List.mem_cons_self
      | inr ht => exact List.mem_cons_of_mem x (mem_of_mem_eraseFirst j k xs ht)

/-- **Even-multiplicity lemma.**  If every element of `l` occurs an even
number of times in `l`, then for every weight `w` the true-count is
even.  Well-founded recursion on length via double-erase. -/
theorem countTrue_even_of_counts_even (w : Nat → Bool) :
    ∀ l : List Nat, (∀ k ∈ l, countNat k l % 2 = 0) →
      countTrue w l % 2 = 0
  | [], _ => by simp [countTrue]
  | x :: xs, hev => by
    have hx_mem : x ∈ x :: xs := List.mem_cons_self
    have hcx := hev x hx_mem
    have hx_in_xs : x ∈ xs := by
      by_cases hmem : x ∈ xs
      · exact hmem
      · exfalso
        have hz : countNat x xs = 0 := countNat_eq_zero_of_not_mem x xs hmem
        have h1 : countNat x (x :: xs) = 1 := by simp [countNat, hz]
        rw [h1] at hcx
        exact absurd hcx (by decide)
    have hcount : countTrue w (x :: xs)
        = 2 * (if w x then 1 else 0) + countTrue w (eraseFirst x xs) := by
      have h := countTrue_eraseFirst w x xs hx_in_xs
      simp [countTrue, h]
      omega
    have hev' : ∀ k ∈ eraseFirst x xs,
        countNat k (eraseFirst x xs) % 2 = 0 := by
      intro k hk
      have hk_xs : k ∈ xs := mem_of_mem_eraseFirst k x xs hk
      have hk_l : k ∈ x :: xs := List.mem_cons_of_mem x hk_xs
      have hev_k := hev k hk_l
      have e1 : countNat k (x :: xs)
          = (if x = k then 1 else 0) + countNat k xs := by simp [countNat]
      have e2 : countNat k xs
          = (if x = k then 1 else 0) + countNat k (eraseFirst x xs) :=
        countNat_eraseFirst k x xs hx_in_xs
      rw [e1, e2] at hev_k
      by_cases hxk : x = k
      · subst hxk
        simp at hev_k
        omega
      · simp [hxk] at hev_k
        omega
    have hrec := countTrue_even_of_counts_even w (eraseFirst x xs) hev'
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (eraseFirst_length_le x xs)

/-! ## The certificate data (machine-generated; see header for encoding) -/

def keyCodes : List (List Nat) := [
  [1001, 1011, 1022, 1031, 1042, 1072, 1082, 1101, 1111, 1121, 1141, 1151, 1161, 1191, 1201, 1211, 100112, 101112, 102110, 103220, 104202, 105202, 106022, 107101, 108101, 109011, 110211, 111211, 112101, 113101, 114211, 115011, 116211, 118110, 119110, 120101, 121101, 122211, 123011, 124211, 126110, 127110, 129110, 130110],
  [1002, 1022, 1042, 1061, 1071, 1081, 1121, 1142, 1161, 1192, 1211, 100202, 101202, 103220, 104211, 105211, 106011, 110101, 111101, 112202, 114220, 115121, 116101, 119110, 120202, 122220, 123121, 124101, 127110, 129220, 130110],
  [1001, 1011, 1022, 1031, 1042, 1061, 1071, 1081, 1101, 1111, 1122, 1141, 1151, 1162, 1191, 1201, 1212, 100112, 101112, 102110, 103220, 104211, 105211, 106011, 107101, 108101, 109011, 110112, 111112, 112101, 113101, 114211, 115112, 116112, 118110, 119220, 120101, 121101, 122211, 123112, 124112, 126110, 127220, 129110, 130220],
  [1001, 1012, 1021, 1041, 1052, 1071, 1081, 1102, 1121, 1141, 1161, 1191, 1202, 1211, 100121, 101101, 102202, 103112, 104101, 105101, 106211, 107202, 109220, 110121, 111101, 112101, 114110, 115011, 116101, 119110, 120101, 121202, 122112, 123011, 124121, 126220, 127110, 129110, 130110],
  [1002, 1011, 1021, 1031, 1041, 1052, 1071, 1081, 1101, 1111, 1122, 1142, 1151, 1162, 1192, 1201, 1212, 100211, 101211, 102112, 103112, 104101, 105101, 106211, 107101, 108101, 109211, 110112, 111112, 112202, 113101, 114121, 115022, 116112, 118110, 119220, 120202, 121101, 122121, 123022, 124112, 126110, 127220, 129220, 130220],
  [1001, 1012, 1021, 1031, 1042, 1051, 1071, 1082, 1102, 1111, 1121, 1141, 1151, 1161, 1191, 1202, 1211, 100121, 101112, 102211, 103121, 104101, 105202, 106112, 107202, 108101, 109121, 110121, 111211, 112101, 113101, 114211, 115011, 116211, 118110, 119110, 120101, 121202, 122112, 123011, 124121, 126220, 127110, 129110, 130110],
  [1002, 1012, 1022, 1042, 1052, 1072, 1082, 1102, 1122, 1142, 1162, 1192, 1202, 1212, 100222, 101202, 102202, 103222, 104202, 105202, 106222, 107202, 109220, 110222, 111202, 112202, 114220, 115022, 116202, 119220, 120202, 121202, 122222, 123022, 124222, 126220, 127220, 129220, 130220],
  [1001, 1011, 1022, 1031, 1042, 1052, 1072, 1082, 1101, 1111, 1121, 1141, 1151, 1161, 1191, 1201, 1211, 100112, 101112, 102112, 103222, 104202, 105202, 106222, 107101, 108101, 109211, 110211, 111211, 112101, 113101, 114211, 115011, 116211, 118110, 119110, 120101, 121101, 122211, 123011, 124211, 126110, 127110, 129110, 130110],
  [1001, 1011, 1022, 1041, 1051, 1061, 1073, 1082, 1101, 1122, 1141, 1162, 1191, 1201, 1212, 100112, 101101, 102101, 103211, 104213, 105112, 106132, 107101, 109110, 110312, 111202, 112101, 114110, 115112, 116202, 119220, 120101, 121101, 122211, 123112, 124312, 126110, 127220, 129110, 130220],
  [1002, 1011, 1021, 1031, 1043, 1052, 1071, 1083, 1101, 1111, 1122, 1142, 1151, 1162, 1192, 1201, 1212, 100211, 101213, 102112, 103132, 104101, 105303, 106213, 107101, 108101, 109211, 110112, 111312, 112202, 113101, 114321, 115022, 116312, 118110, 119220, 120202, 121101, 122121, 123022, 124112, 126110, 127220, 129220, 130220],
  [1002, 1012, 1022, 1031, 1043, 1051, 1072, 1083, 1102, 1111, 1122, 1142, 1151, 1162, 1192, 1202, 1212, 100222, 101213, 102211, 103231, 104202, 105303, 106123, 107202, 108101, 109121, 110222, 111312, 112202, 113101, 114321, 115022, 116312, 118110, 119220, 120202, 121202, 122222, 123022, 124222, 126220, 127220, 129220, 130220],
  [1002, 1011, 1021, 1031, 1043, 1052, 1061, 1072, 1082, 1101, 1111, 1123, 1142, 1151, 1163, 1192, 1201, 1213, 100211, 101213, 102112, 103132, 104112, 105312, 106222, 107101, 108101, 109211, 110213, 111213, 112202, 113101, 114321, 115123, 116213, 118110, 119330, 120202, 121101, 122121, 123123, 124213, 126110, 127330, 129220, 130330],
  [1001, 1021, 1031, 1042, 1051, 1061, 1072, 1083, 1111, 1122, 1141, 1151, 1162, 1191, 1212, 100101, 101112, 102011, 103121, 104112, 105213, 106123, 108101, 109101, 110202, 111312, 112101, 113101, 114211, 115112, 116312, 118110, 119220, 120101, 122110, 123112, 124202, 127220, 129110, 130220],
  [1002, 1022, 1031, 1043, 1051, 1061, 1071, 1082, 1111, 1121, 1142, 1151, 1161, 1192, 1211, 100202, 101213, 102011, 103231, 104211, 105312, 106112, 108101, 109101, 110101, 111211, 112202, 113101, 114321, 115121, 116211, 118110, 119110, 120202, 122220, 123121, 124101, 127110, 129220, 130110],
  [1001, 1011, 1022, 1031, 1042, 1052, 1061, 1071, 1083, 1101, 1111, 1122, 1141, 1151, 1162, 1191, 1201, 1212, 100112, 101112, 102112, 103222, 104211, 105213, 106213, 107101, 108101, 109211, 110112, 111312, 112101, 113101, 114211, 115112, 116312, 118110, 119220, 120101, 121101, 122211, 123112, 124112, 126110, 127220, 129110, 130220],
  [1002, 1022, 1031, 1041, 1051, 1061, 1073, 1082, 1111, 1123, 1142, 1151, 1163, 1192, 1213, 100202, 101211, 102011, 103211, 104213, 105112, 106132, 108101, 109101, 110303, 111213, 112202, 113101, 114121, 115123, 116213, 118110, 119330, 120202, 122220, 123123, 124303, 127330, 129220, 130330],
  [1002, 1022, 1042, 1062, 1072, 1082, 1122, 1142, 1162, 1192, 1212, 100202, 101202, 103220, 104222, 105222, 106022, 110202, 111202, 112202, 114220, 115222, 116202, 119220, 120202, 122220, 123222, 124202, 127220, 129220, 130220],
  [1002, 1011, 1021, 1042, 1051, 1062, 1073, 1082, 1101, 1122, 1142, 1162, 1192, 1201, 1212, 100211, 101202, 102101, 103121, 104123, 105222, 106132, 107101, 109110, 110312, 111202, 112202, 114220, 115222, 116202, 119220, 120202, 121101, 122121, 123222, 124312, 126110, 127220, 129220, 130220],
  [1001, 1021, 1031, 1042, 1051, 1062, 1073, 1082, 1111, 1123, 1141, 1151, 1163, 1191, 1213, 100101, 101112, 102011, 103121, 104123, 105222, 106132, 108101, 109101, 110303, 111213, 112101, 113101, 114211, 115213, 116213, 118110, 119330, 120101, 122110, 123213, 124303, 127330, 129110, 130330],
  [1001, 1011, 1022, 1031, 1042, 1052, 1062, 1072, 1082, 1101, 1111, 1123, 1141, 1151, 1163, 1191, 1201, 1213, 100112, 101112, 102112, 103222, 104222, 105222, 106222, 107101, 108101, 109211, 110213, 111213, 112101, 113101, 114211, 115213, 116213, 118110, 119330, 120101, 121101, 122211, 123213, 124213, 126110, 127330, 129110, 130330]
]

def signBits : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
def joined : List Nat := keyCodes.foldr (· ++ ·) []

/-- local-gauge sign of one configuration under weight `w` -/
def localParity (w : Nat → Bool) (c : List Nat) : Bool :=
  parity (countTrue w c)

/-- the recorded machine sign parity over the certificate -/
def machineXor : Bool := xorList signBits

/-! ## The two decidable facts -/

theorem certificate_even :
    (joined.all (fun k => countNat k joined % 2 == 0)) = true := by
  decide

theorem machine_xor_true : machineXor = true := by decide

/-! ## The theorem -/

theorem localXor_decomp (w : Nat → Bool) :
    ∀ cs : List (List Nat),
      xorList (cs.map (localParity w))
        = parity (countTrue w (cs.foldr (· ++ ·) [])) := by
  intro cs
  induction cs with
  | nil => simp [xorList, countTrue, parity]
  | cons c rest ih =>
    simp [xorList, ih, localParity, List.foldr, countTrue_append, parity_add]

/-- **No local gauge.**  No face/edge-local sign assignment reproduces
the recorded sign table over the certificate. -/
theorem no_local_gauge :
    ¬ ∃ w : Nat → Bool,
        (keyCodes.map (localParity w)) = signBits := by
  intro ⟨w, hw⟩
  have h1 : xorList (keyCodes.map (localParity w)) = machineXor := by
    rw [hw]; rfl
  have h2 : xorList (keyCodes.map (localParity w)) = false := by
    rw [localXor_decomp w keyCodes]
    have hev : ∀ k ∈ joined, countNat k joined % 2 = 0 := by
      intro k hk
      have := certificate_even
      have hall := List.all_eq_true.mp this k hk
      simpa using hall
    have hpar := countTrue_even_of_counts_even w joined hev
    show parity (countTrue w joined) = false
    simp [parity, hpar]
  rw [machine_xor_true] at h1
  rw [h2] at h1
  exact Bool.noConfusion h1

/-! ## Frontier interfaces (typed targets; consumers of future proofs)

These mirror the main tree's certificate discipline: machinery typed
now, physical/geometric content to be supplied by named producers. -/

/-- The support law (P9): decomposability into two closed surfaces
implies a positive amplitude.  `decomposable` and `amplitudePos` to be
bound to the main tree's Haar engine. -/
structure SupportLawWitness where
  decomposable : List Nat → Prop
  amplitudePos : List Nat → Prop
  law : ∀ c, decomposable c → amplitudePos c

/-- The ABK identification target (P12–P15): κ as the Arf–Brown–
Kervaire class of the embedded strand cover. -/
structure ABKIdentification where
  kappa : List Nat → Bool
  brown : List Nat → Fin 8
  identify : ∀ c, (kappa c = true ↔ brown c = ⟨4, by decide⟩)

/-- The enveloped-cone contraction target (P16–P18): the blocking map
contracts the Hilbert projective metric on the flowed heat-kernel
cone, uniformly along the flow, with the κ-graded sector dominated. -/
structure EnvelopedConeContraction where
  q : Nat → Nat  -- contraction data placeholder: numerator/denominator pair to be refined
  strict : Prop
  uniformAlongFlow : Prop
  gradedSectorDominated : Prop

end DualKappa
