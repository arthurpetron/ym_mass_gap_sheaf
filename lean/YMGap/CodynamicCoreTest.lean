/-
# Codynamic core — non-vacuous computed tests

Mirrors `Codynamic/Tests.agda`.  A synthetic instance (one color; a unary
symbol `f` and a constant `k`; a two-point carrier) with a toy cost
structure on `Nat`.  The order/equivalence evidence fields are trivial
(`le := True`), exactly as the Agda `toyC` — but the VALUES computed by
`eval`, `run`, `endRec`, and the `nBound` FOLD are genuine `Nat`
computations, asserted here by `rfl` (so the kernel executes them).

The last `example`s show the theorems actually APPLY: `nstep_d` (the
n-step Grönwall bound) and `nBound_mono` instantiate and typecheck against
the real, computed fold values.
-/
import YMGap.CodynamicCore

namespace YMGap.CodynamicCore.Test

open YMGap.CodynamicCore

/-! ## A toy cost structure on `Nat` (trivial order, genuine values) -/

abbrev toyCosts : Costs where
  Q := Nat
  zero := 0
  add := (· + ·)
  max := Nat.max
  le := fun _ _ => True
  eqv := fun _ _ => True
  le_refl := trivial
  le_trans := fun _ _ => trivial
  add_mono := fun _ _ => trivial
  eqv_refl := trivial
  eqv_symm := fun _ => trivial
  eqv_trans := fun _ _ => trivial
  add_congr_right := fun _ => trivial
  add_assoc := fun _ _ _ => trivial
  zero_add := fun _ => trivial
  le_max_left := trivial
  le_max_right := trivial
  max_lub := fun _ _ => trivial

/-! ## Synthetic signature: one color; `f` unary, `k` a constant -/

/-- The single color. -/
abbrev c0 : Fin 1 := ⟨0, by decide⟩
/-- The symbol `f` (unary). -/
abbrev fOp : Fin 2 := ⟨0, by decide⟩
/-- The symbol `k` (constant). -/
abbrev kOp : Fin 2 := ⟨1, by decide⟩

abbrev Sg2 : Signature 1 :=
  ⟨2, fun i => ⟨(match i.val with | 0 => [c0] | _ => []), c0⟩⟩

abbrev D2 : TypedSet 1 := ⟨2, fun _ => c0⟩

/-- Recorded point 0. -/
def d0 : Term Sg2 D2 c0 := Term.var ⟨0, by decide⟩
/-- Recorded point 1. -/
def d1 : Term Sg2 D2 c0 := Term.var ⟨1, by decide⟩
/-- The unary symbol applied. -/
def fTm (t : Term Sg2 D2 c0) : Term Sg2 D2 c0 :=
  @Term.app 1 Sg2 D2 fOp (All.cons t All.nil)
/-- The constant. -/
def kTm : Term Sg2 D2 c0 := @Term.app 1 Sg2 D2 kOp All.nil

/-- Term size computes: `size (f d0) = 2`. -/
example : tsize (fTm d0) = 2 := rfl
/-- `size k = 1`. -/
example : tsize kTm = 1 := rfl

/-! ## The toy metric model: `Val = Nat`, `f x = x+1`, `k = 7`, `d = |·-·|` -/

/-- The toy interpretation kernel (free length index, so the dependent
`All` match is not stuck on `(profile ω).dom`): `k ↦ 7`, `f x ↦ x+1`. -/
def natFold : {w : List (Color 1)} → All (fun _ : Color 1 => Nat) w → Nat
  | [], .nil => 7
  | _ :: _, .cons x _ => x + 1

abbrev toyM : MetricVal Sg2 D2 toyCosts where
  Val := fun _ => Nat
  point := fun i => i.val
  interp := fun _ args => natFold args
  d := fun x y => (x - y) + (y - x)
  d_refl := fun _ => trivial
  d_sym := fun _ _ => trivial
  triangle := fun _ _ _ => trivial
  nonneg := fun _ _ => trivial

/-- `eval` computes: `eval (f (f d0)) = 2`. -/
example : (eval toyM (fTm (fTm d0)) : Nat) = 2 := rfl
/-- `eval k = 7`. -/
example : (eval toyM kTm : Nat) = 7 := rfl

/-! ## The Lipschitz control: the doubling modulus -/

abbrev toyL : Lipschitz toyM where
  scale := fun _ x => x + x
  scale_mono := by intros; trivial
  scale_zero := fun _ => trivial
  lip := fun _ _ _ => trivial

/-! ## A two-step trajectory with defects 2 and 5 under doubling -/

def s1 : Step toyM c0 :=
  { rule := fOp, pos := Pos.phere, sides := All.cons (0 : Nat) All.nil }

def tr2 : Traj toyM c0 c0 :=
  Traj.tcons { step := s1, recVal := (3 : Nat) }
    (Traj.tcons { step := s1, recVal := (9 : Nat) } Traj.tnil)

/-- The computed run: `f (f 0) = 2`. -/
example : (run toyM (0 : Nat) tr2 : Nat) = 2 := rfl
/-- The recorded endpoint follows the y-chain: `9`. -/
example : (endRec toyM (0 : Nat) tr2 : Nat) = 9 := rfl
/-- **The n-step fold computes**: `nBound = 2·(2·0 + 2) + 5 = 9`
(exactly the Agda `test-16-nBound`). -/
example : (nBound toyM toyL (0 : Nat) (0 : Nat) tr2 : Nat) = 9 := rfl

/-! ## The theorems APPLY (evidence trivial in the toy order, values genuine) -/

/-- `nstep_d` instantiates: a certificate for the initial discrepancy is
transported to the final one, bounded by the computed fold `9`. -/
example :
    toyCosts.le (toyM.d (run toyM (0 : Nat) tr2) (endRec toyM (0 : Nat) tr2))
      (nBound toyM toyL (0 : Nat) (0 : Nat) tr2) :=
  nstep_d toyM toyL (0 : Nat) (0 : Nat) (0 : Nat) trivial tr2

/-- `nBound_mono` instantiates. -/
example {b b' : Nat} (h : toyCosts.le b b') :
    toyCosts.le (nBound toyM toyL b (0 : Nat) tr2) (nBound toyM toyL b' (0 : Nat) tr2) :=
  nBound_mono toyM toyL (0 : Nat) tr2 h

/-! ## Axiom gate on the load-bearing declarations -/

#print axioms qCosts
#print axioms dAll_refl
#print axioms maxOver_ub
#print axioms dAll_fill
#print axioms nBound
#print axioms nBound_mono
#print axioms nstep_d
#print axioms deriv_d
#print axioms eqBound_append
#print axioms unit_defect

end YMGap.CodynamicCore.Test
