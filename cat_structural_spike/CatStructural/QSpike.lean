/-
CatStructural/QSpike.lean

The `Q'`-mirror substrate: the genuinely-setoid instance.

`QS` below mirrors, field for field, the representation of
`YMGap.Constructive.Q'` in the main tree (`lean/YMGap/Constructive/
Rationals.lean`): numerator `num : Int`, denominator-predecessor
`denPred : Nat` (denominator positive structurally), UNNORMALIZED, with
semantic equivalence / order by cross-product comparison on `Int`.
This spike package cannot import the main tree (deliberate isolation),
so the definitions are restated; on promotion this file is deleted and
the substrate laws below are proved for `Q'` itself — the proofs
transfer verbatim because the representation is identical.

Why this instance matters more than the `Int` one: here `eqv` is a
REAL setoid — `⟨1,1⟩` (= 1/2) and `⟨2,3⟩` (= 2/4) are equivalent but
structurally distinct — so this file is the actual test that the
generic categorical layer (`DomOver.lean`) works under the CReal-style
setoid discipline, not just under `Eq`.  The end-to-end demo runs the
generic chain and `gap_persistsG` over `QS` masses with unnormalized
representations, and exhibits two structurally different domination
witnesses proved `DomG.eqv` by kernel `decide`.

All substrate laws are proved by the same cross-product techniques as
the main tree's `Q'` lemma stock (`le_trans'`, `mul_le_mul_of_nonneg_
right`, ...): expand denominators via the `sub_add_cancel` dance once
(`denZ_mul`), shuffle products with AC `simp`, apply the `Int`
monotonicity/cancellation lemma.  Mathlib-free, Classical-free,
sorry-free, kernel `decide` only.
-/

import CatStructural.Substrate
import CatStructural.DomOver

set_option linter.unusedSimpArgs false

namespace CatStructural

/-- Mirror of `YMGap.Constructive.Q'`: unnormalized rational,
    denominator `denPred + 1` positive by construction. -/
structure QS where
  num : Int
  denPred : Nat
deriving DecidableEq, Repr

namespace QS

/-- The (positive) denominator. -/
@[inline] def den (q : QS) : Nat := q.denPred + 1

theorem den_pos (q : QS) : 0 < q.den := Nat.succ_pos _

/-- The denominator as an `Int` — the form all cross-products use. -/
@[inline] def denZ (q : QS) : Int := (q.den : Int)

theorem denZ_pos (q : QS) : 0 < q.denZ :=
  Int.natCast_pos.mpr (den_pos q)

theorem denZ_nonneg (q : QS) : 0 ≤ q.denZ :=
  Int.le_of_lt (denZ_pos q)

/-- Semantic equivalence: `a/b ≈ c/d` iff `a·d = c·b`. -/
@[inline] def eqv (p q : QS) : Prop := p.num * q.denZ = q.num * p.denZ

/-- Semantic ≤ by cross-product. -/
@[inline] def le (p q : QS) : Prop := p.num * q.denZ ≤ q.num * p.denZ

/-- Semantic < by cross-product. -/
@[inline] def lt (p q : QS) : Prop := p.num * q.denZ < q.num * p.denZ

instance (p q : QS) : Decidable (eqv p q) :=
  inferInstanceAs (Decidable (_ = _))
instance (p q : QS) : Decidable (le p q) :=
  inferInstanceAs (Decidable (_ ≤ _))
instance (p q : QS) : Decidable (lt p q) :=
  inferInstanceAs (Decidable (_ < _))

/-- Multiplication: `(a/b)·(c/d) = (ac)/(bd)`, denominator stored as
    predecessor via truncating subtraction (well-defined: `bd ≥ 1`). -/
@[inline] def mul (p q : QS) : QS :=
  ⟨p.num * q.num, p.den * q.den - 1⟩

def zero : QS := ⟨0, 0⟩
def one : QS := ⟨1, 0⟩

/-! ### Additive arithmetic, mirroring `Q'` verbatim

Needed by the Θ-certificate bridge (`StepBridge.lean`): the actual
per-step certificates of `YMGap/RG/BlockSpin.lean` state their S4
decrease as `sigma_in - eta ≤ sigma_out`, so the bridge's `QS` demo
must compute the same subtraction.  Definitions are field-for-field
`Q'.neg` / `Q'.add` / `Q'.sub`. -/

/-- Negation: `-(n/d) = (-n)/d`.  Mirror of `Q'.neg`. -/
@[inline] def neg (q : QS) : QS := ⟨-q.num, q.denPred⟩

/-- Addition: `a/b + c/d = (ad + cb)/(bd)`.  Mirror of `Q'.add`. -/
@[inline] def add (p q : QS) : QS :=
  ⟨p.num * q.denZ + q.num * p.denZ, p.den * q.den - 1⟩

/-- Subtraction: `p - q = p + (-q)`.  Mirror of `Q'.sub`. -/
@[inline] def sub (p q : QS) : QS := add p (neg q)

/-- The one denominator computation everything routes through:
    `(p·q).den = p.den · q.den`, cast to `Int`. -/
theorem denZ_mul (p q : QS) : (mul p q).denZ = p.denZ * q.denZ := by
  show (((p.den * q.den - 1) + 1 : Nat) : Int)
      = ((p.den : Nat) : Int) * ((q.den : Nat) : Int)
  have h : (p.den * q.den - 1) + 1 = p.den * q.den :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos p) (den_pos q))))
  rw [h]
  exact Int.natCast_mul _ _

/-- `0 ≤ p` iff the numerator is nonnegative. -/
theorem zero_le_iff (p : QS) : le zero p ↔ 0 ≤ p.num := by
  show (0 : Int) * p.denZ ≤ p.num * (1 : Int) ↔ 0 ≤ p.num
  simp

/-- `0 < p` iff the numerator is positive. -/
theorem zero_lt_iff (p : QS) : lt zero p ↔ 0 < p.num := by
  show (0 : Int) * p.denZ < p.num * (1 : Int) ↔ 0 < p.num
  simp

/-! ### The substrate laws -/

theorem eqv_refl (a : QS) : eqv a a := rfl

theorem eqv_symm {a b : QS} (h : eqv a b) : eqv b a := h.symm

theorem eqv_trans {a b c : QS} (h₁ : eqv a b) (h₂ : eqv b c) :
    eqv a c := by
  have key : (a.num * c.denZ) * b.denZ = (c.num * a.denZ) * b.denZ := by
    calc (a.num * c.denZ) * b.denZ
        = (a.num * b.denZ) * c.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ = (b.num * a.denZ) * c.denZ := by rw [h₁]
      _ = (b.num * c.denZ) * a.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ = (c.num * b.denZ) * a.denZ := by rw [h₂]
      _ = (c.num * a.denZ) * b.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (denZ_pos b)) key

theorem le_of_eqv {a b : QS} (h : eqv a b) : le a b :=
  Int.le_of_eq h

theorem le_trans {a b c : QS} (h₁ : le a b) (h₂ : le b c) : le a c := by
  have s₁ : (a.num * b.denZ) * c.denZ ≤ (b.num * a.denZ) * c.denZ :=
    Int.mul_le_mul_of_nonneg_right h₁ (denZ_nonneg c)
  have s₂ : (b.num * c.denZ) * a.denZ ≤ (c.num * b.denZ) * a.denZ :=
    Int.mul_le_mul_of_nonneg_right h₂ (denZ_nonneg a)
  have chain : (a.num * c.denZ) * b.denZ ≤ (c.num * a.denZ) * b.denZ := by
    calc (a.num * c.denZ) * b.denZ
        = (a.num * b.denZ) * c.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ ≤ (b.num * a.denZ) * c.denZ := s₁
      _ = (b.num * c.denZ) * a.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ ≤ (c.num * b.denZ) * a.denZ := s₂
      _ = (c.num * a.denZ) * b.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  exact Int.le_of_mul_le_mul_right chain (denZ_pos b)

theorem le_of_lt {a b : QS} (h : lt a b) : le a b :=
  Int.le_of_lt h

theorem lt_of_lt_of_le {a b c : QS} (h₁ : lt a b) (h₂ : le b c) :
    lt a c := by
  have s₁ : (a.num * b.denZ) * c.denZ < (b.num * a.denZ) * c.denZ :=
    Int.mul_lt_mul_of_pos_right h₁ (denZ_pos c)
  have s₂ : (b.num * c.denZ) * a.denZ ≤ (c.num * b.denZ) * a.denZ :=
    Int.mul_le_mul_of_nonneg_right h₂ (denZ_nonneg a)
  have chain : (a.num * c.denZ) * b.denZ < (c.num * a.denZ) * b.denZ := by
    calc (a.num * c.denZ) * b.denZ
        = (a.num * b.denZ) * c.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ < (b.num * a.denZ) * c.denZ := s₁
      _ = (b.num * c.denZ) * a.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ ≤ (c.num * b.denZ) * a.denZ := s₂
      _ = (c.num * a.denZ) * b.denZ := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  exact Int.lt_of_mul_lt_mul_right chain (denZ_nonneg b)

theorem mul_congr {a a' b b' : QS} (h₁ : eqv a a') (h₂ : eqv b b') :
    eqv (mul a b) (mul a' b') := by
  show (a.num * b.num) * (mul a' b').denZ
      = (a'.num * b'.num) * (mul a b).denZ
  rw [denZ_mul, denZ_mul]
  calc (a.num * b.num) * (a'.denZ * b'.denZ)
      = (a.num * a'.denZ) * (b.num * b'.denZ) := by
        simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
    _ = (a'.num * a.denZ) * (b'.num * b.denZ) := by rw [h₁, h₂]
    _ = (a'.num * b'.num) * (a.denZ * b.denZ) := by
        simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

theorem mul_assoc_eqv (a b c : QS) :
    eqv (mul (mul a b) c) (mul a (mul b c)) := by
  show ((a.num * b.num) * c.num) * (mul a (mul b c)).denZ
      = (a.num * (b.num * c.num)) * (mul (mul a b) c).denZ
  rw [denZ_mul, denZ_mul, denZ_mul, denZ_mul]
  simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

theorem mul_comm_eqv (a b : QS) : eqv (mul a b) (mul b a) := by
  show (a.num * b.num) * (mul b a).denZ = (b.num * a.num) * (mul a b).denZ
  rw [denZ_mul, denZ_mul]
  simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

theorem one_mul_eqv (a : QS) : eqv (mul one a) a := by
  show ((1 : Int) * a.num) * a.denZ = a.num * (mul one a).denZ
  rw [denZ_mul]
  show ((1 : Int) * a.num) * a.denZ = a.num * (((1 : Nat) : Int) * a.denZ)
  simp

theorem zero_lt_one : lt zero one := by decide

theorem mul_nonneg {a b : QS} (h₁ : le zero a) (h₂ : le zero b) :
    le zero (mul a b) := by
  rw [zero_le_iff] at h₁ h₂
  rw [zero_le_iff]
  exact Int.mul_nonneg h₁ h₂

theorem mul_pos {a b : QS} (h₁ : lt zero a) (h₂ : lt zero b) :
    lt zero (mul a b) := by
  rw [zero_lt_iff] at h₁ h₂
  rw [zero_lt_iff]
  exact Int.mul_pos h₁ h₂

theorem mul_le_mul_left {a b c : QS} (h : le a b) (hc : le zero c) :
    le (mul c a) (mul c b) := by
  show (c.num * a.num) * (mul c b).denZ ≤ (c.num * b.num) * (mul c a).denZ
  rw [denZ_mul, denZ_mul]
  have hcn : (0 : Int) ≤ c.num := (zero_le_iff c).mp hc
  have hfac : (0 : Int) ≤ c.num * c.denZ :=
    Int.mul_nonneg hcn (denZ_nonneg c)
  have scaled : (a.num * b.denZ) * (c.num * c.denZ)
              ≤ (b.num * a.denZ) * (c.num * c.denZ) :=
    Int.mul_le_mul_of_nonneg_right h hfac
  calc (c.num * a.num) * (c.denZ * b.denZ)
      = (a.num * b.denZ) * (c.num * c.denZ) := by
        simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
    _ ≤ (b.num * a.denZ) * (c.num * c.denZ) := scaled
    _ = (c.num * b.num) * (c.denZ * a.denZ) := by
        simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

theorem mul_right_cancel_eqv {a b c : QS} (hc : lt zero c)
    (h : eqv (mul a c) (mul b c)) : eqv a b := by
  have hcn : (0 : Int) < c.num := (zero_lt_iff c).mp hc
  have hfac : (0 : Int) < c.num * c.denZ :=
    Int.mul_pos hcn (denZ_pos c)
  have h' : (a.num * c.num) * ((mul b c).denZ) =
            (b.num * c.num) * ((mul a c).denZ) := h
  rw [denZ_mul, denZ_mul] at h'
  have key : (a.num * b.denZ) * (c.num * c.denZ)
           = (b.num * a.denZ) * (c.num * c.denZ) := by
    calc (a.num * b.denZ) * (c.num * c.denZ)
        = (a.num * c.num) * (b.denZ * c.denZ) := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ = (b.num * c.num) * (a.denZ * c.denZ) := h'
      _ = (b.num * a.denZ) * (c.num * c.denZ) := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hfac) key

theorem le_of_mul_le_mul_left {a b c : QS}
    (h : le (mul c a) (mul c b)) (hc : lt zero c) : le a b := by
  have hcn : (0 : Int) < c.num := (zero_lt_iff c).mp hc
  have hfac : (0 : Int) < c.num * c.denZ :=
    Int.mul_pos hcn (denZ_pos c)
  have h' : (c.num * a.num) * ((mul c b).denZ) ≤
            (c.num * b.num) * ((mul c a).denZ) := h
  rw [denZ_mul, denZ_mul] at h'
  have key : (a.num * b.denZ) * (c.num * c.denZ)
           ≤ (b.num * a.denZ) * (c.num * c.denZ) := by
    calc (a.num * b.denZ) * (c.num * c.denZ)
        = (c.num * a.num) * (c.denZ * b.denZ) := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      _ ≤ (c.num * b.num) * (c.denZ * a.denZ) := h'
      _ = (b.num * a.denZ) * (c.num * c.denZ) := by
          simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  exact Int.le_of_mul_le_mul_right key hfac

theorem pos_cancel {d n m : QS} (hd : lt zero d) (hn : lt zero n)
    (h : le n (mul d m)) : lt zero m := by
  rw [zero_lt_iff]
  have hdn : (0 : Int) < d.num := (zero_lt_iff d).mp hd
  have hnn : (0 : Int) < n.num := (zero_lt_iff n).mp hn
  have h' : n.num * ((mul d m).denZ) ≤ (d.num * m.num) * n.denZ := h
  rw [denZ_mul] at h'
  false_or_by_contra
  rename_i hm
  have hm' : m.num ≤ 0 := Int.not_lt.mp (fun h'' => hm (by exact h''))
  -- RHS ≤ 0:
  have hR : (d.num * m.num) * n.denZ ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg
      (Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hdn) hm')
      (denZ_nonneg n)
  -- LHS > 0:
  have hL : (0 : Int) < n.num * (d.denZ * m.denZ) :=
    Int.mul_pos hnn (Int.mul_pos (denZ_pos d) (denZ_pos m))
  exact absurd (Int.lt_of_lt_of_le hL (Int.le_trans h' hR)) (by decide)

end QS

/-- The `Q'`-mirror substrate: the instance where `eqv` is genuinely a
    setoid (cross-product equivalence of unnormalized rationals), the
    dress rehearsal for wiring `DomOver` into the main tree.  Reducible
    so kernel `decide` sees through to `Int` comparisons. -/
@[reducible] def qSubstrate : GapSubstrate where
  Carrier := QS
  eqv := QS.eqv
  le := QS.le
  lt := QS.lt
  zero := QS.zero
  one := QS.one
  mul := QS.mul
  eqv_refl := QS.eqv_refl
  eqv_symm := QS.eqv_symm
  eqv_trans := QS.eqv_trans
  le_of_eqv := QS.le_of_eqv
  le_trans := QS.le_trans
  le_of_lt := QS.le_of_lt
  lt_of_lt_of_le := QS.lt_of_lt_of_le
  mul_congr := QS.mul_congr
  mul_assoc_eqv := QS.mul_assoc_eqv
  mul_comm_eqv := QS.mul_comm_eqv
  one_mul_eqv := QS.one_mul_eqv
  zero_lt_one := QS.zero_lt_one
  mul_nonneg := QS.mul_nonneg
  mul_pos := QS.mul_pos
  mul_le_mul_left := QS.mul_le_mul_left
  mul_right_cancel_eqv := QS.mul_right_cancel_eqv
  le_of_mul_le_mul_left := QS.le_of_mul_le_mul_left
  pos_cancel := QS.pos_cancel

namespace QSpikeDemo

/-! ## End-to-end demo over the setoid substrate

Masses `3/4 → 9/16` with a `3/4` step ratio, everything kernel-checked
through the GENERIC layer, with deliberately unnormalized data. -/

/-- `3/4`. -/
def threeQuarters : QS := ⟨3, 3⟩
/-- `9/16`. -/
def nineSixteenths : QS := ⟨9, 15⟩

def demoM : Nat → MassG qSubstrate
  | 0 => ⟨threeQuarters, by decide⟩
  | _ => ⟨nineSixteenths, by decide⟩

/-- The tail step's bound, as a closed proposition (so kernel `decide`
    applies; the wildcard match arm's expected type mentions the scale
    variable before reduction, but is definitionally this closed
    statement). -/
theorem tail_bound :
    qSubstrate.le (QS.mul QS.one nineSixteenths)
                  (QS.mul QS.one nineSixteenths) := by decide

def demoStep : ∀ k, DomG (demoM k) (demoM (k + 1))
  | 0 => ⟨threeQuarters, QS.one, by decide, by decide, by decide⟩
  | _ + 1 => ⟨QS.one, QS.one, by decide, by decide, tail_bound⟩

theorem demoStep_num_pos (k : Nat) :
    qSubstrate.lt qSubstrate.zero (demoStep k).num := by
  match k with
  | 0 => decide
  | _ + 1 => exact (by decide : qSubstrate.lt qSubstrate.zero QS.one)

theorem demoChain_num_pos (n : Nat) :
    qSubstrate.lt qSubstrate.zero (chainG demoM demoStep n).num := by
  induction n with
  | zero => decide
  | succ n ih => exact qSubstrate.mul_pos (demoStep_num_pos n) ih

/-- **Generic gap persistence over the setoid substrate**: every scale's
    mass is strictly positive, obtained by instantiating `gap_persistsG`
    at `QS` — no re-proof, and the anchor positivity is kernel-decided
    on unnormalized rational data. -/
theorem demo_gap_all (n : Nat) :
    qSubstrate.lt qSubstrate.zero ((demoM n).val) :=
  gap_persistsG demoM demoStep (by decide) demoChain_num_pos n

/-! ## The setoid at work: structurally different, semantically equal

Two domination witnesses for the same step whose every field differs
structurally — ratio `1/2` carried as `(1/1)/(2/1)` versus `(2/4)/(1/1)`
— proved equivalent in the hom-setoid by kernel `decide`.  Under `Eq`
these are simply different records; `DomG.eqv` is doing real work. -/

/-- `1/2` bound witness in the form num `1`, den `2`. -/
def halfA : DomG (demoM 0) (demoM 0) :=
  ⟨⟨1, 0⟩, ⟨2, 0⟩, by decide, by decide, by decide⟩

/-- The same ratio in the form num `2/4`, den `1`. -/
def halfB : DomG (demoM 0) (demoM 0) :=
  ⟨⟨2, 3⟩, ⟨1, 0⟩, by decide, by decide, by decide⟩

/-- The two witnesses are hom-setoid equivalent (kernel-checked) while
    being structurally distinct in every field. -/
theorem halfA_eqv_halfB : DomG.eqv halfA halfB := by
  show QS.eqv (QS.mul halfA.num halfB.den) (QS.mul halfB.num halfA.den)
  decide

/-- ... and they are NOT equal as records (kernel-checked), so the
    equivalence above is genuinely coarser than `Eq`: the setoid
    discipline is load-bearing, not decorative. -/
theorem halfA_ne_halfB : halfA.num ≠ halfB.num := by decide

end QSpikeDemo

#print axioms qSubstrate
#print axioms QSpikeDemo.demo_gap_all
#print axioms QSpikeDemo.halfA_eqv_halfB
#print axioms QSpikeDemo.halfA_ne_halfB

end CatStructural
