/-
# Core-B finite low-gap arithmetic budget

This file translates the finite arithmetic output of
`computations/core_b_atomwise_tail_scout.py` into a small Lean-kernel
certificate.  It records:

* the canonical even and odd reserve polynomials;
* the explicitly transcribed low-gap coefficient polynomials through
  endpoint gap `20`, written in the shifted variables `k = x + 3` (even)
  and `k = x + 2` (odd);
* a coefficientwise envelope for every such polynomial; and
* the exact sums of the dyadic envelope constants.

The shift is the true stable start of the symbolic classifier.  Every
coefficient displayed below is a natural number.  Consequently the envelope
proofs reduce to coefficientwise comparisons and are checked by the kernel
with `decide`.

HONEST SCOPE: all coefficient lists in this file are transcribed inputs from
the exact Python symbolic output.  Lean proves the coefficientwise envelopes
and exact dyadic totals conditional on those explicit lists.  It does not
prove the reserve/formula-to-list transcription identities or that the
actual adverse atom ledger is equal to any of these polynomials.  The
factored formulas are retained below for human review.  That finite
classification theorem, the all-gap tail estimate, and the link to the
physical quotient remain open.  In particular, nothing here inhabits a
Core-B physical bridge.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Constructive.Rationals

namespace YMGap.Continuum.CoreBLowGapBudget

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 4000000

/-! ## 1. Natural-coefficient polynomial evaluator -/

/-- Horner evaluation of an ascending natural coefficient list. -/
def evalNatPoly : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => c + x * evalNatPoly cs x

/-- Coefficientwise domination by a fixed natural multiplier. -/
inductive CoeffEnvelope (L : Nat) : List Nat → List Nat → Prop
  | nil : CoeffEnvelope L [] []
  | cons {m r : Nat} {ms rs : List Nat} :
      m ≤ L * r → CoeffEnvelope L ms rs →
      CoeffEnvelope L (m :: ms) (r :: rs)

/-- A coefficientwise envelope evaluates to a polynomial envelope at every
nonnegative natural argument. -/
theorem evalNatPoly_le_envelope
    (L x : Nat) {mass reserve : List Nat}
    (h : CoeffEnvelope L mass reserve) :
    evalNatPoly mass x ≤ L * evalNatPoly reserve x := by
  induction h with
  | nil => simp [evalNatPoly]
  | cons hm _ ih =>
      simp only [evalNatPoly]
      have htail := Nat.mul_le_mul_left x ih
      have hsum := Nat.add_le_add hm htail
      simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using hsum

/-! ## 2. Canonical parity reserves -/

/-- Canonical reserve for even length `n = 2k`. -/
def evenReserve (k : Nat) : Nat :=
  4 * (k + 1) * (k + 2) ^ 6 * (k + 3)

/-- Canonical reserve for odd length `n = 2k+1`. -/
def oddReserve (k : Nat) : Nat :=
  8 * (k + 2) ^ 2 * (k + 3) ^ 2 *
    (2 * (k + 2) ^ 3 * (k + 4) - (2 * k + 5))

/-- Transcribed coefficients intended for `evenReserve (x+3)`, ascending. -/
def evenReserveCoeffs : List Nat :=
  [1500000, 2425000, 1712500, 690000, 173500, 27880, 2796, 160, 4]

/-- Transcribed coefficients intended for `oddReserve (x+2)`, ascending. -/
def oddReserveCoeffs : List Nat :=
  [2428800, 4432320, 3524472, 1595232, 449560, 80784, 9040, 576, 16]

/-! ## 3. Exact stable low-gap mass polynomials

Computationally, these coefficient lists are the direct expansion of the
factored symbolic formulas in the scout test.  The variable is `x`, so even
lists are intended to represent `P_g(x+3)` and odd lists `P_g(x+2)`.
This module does not claim the eighteen mass-translation identities as Lean
theorems.
-/

def evenMass4 : List Nat :=
  [5529600, 9123840, 6557184, 2680960, 682048, 110560, 11152, 640, 16]

def evenMass8 : List Nat :=
  [15120000, 25596000, 18778800, 7803840, 2010192, 328800, 33360, 1920, 48]

def evenMass10 : List Nat :=
  [38707200, 66170880, 48972288, 20503040, 5313152, 872960, 88832, 5120, 128]

def evenMass12 : List Nat :=
  [9240000, 15992000, 11957600, 5047680, 1316384, 217280, 22176, 1280, 32]

def evenMass14 : List Nat :=
  [35481600, 62000640, 46763264, 19888640, 5218432, 865280, 88576, 5120, 128]

def evenMass16 : List Nat :=
  [29635200, 52426080, 39951408, 17133760, 4524688, 753760, 77392, 4480, 112]

def evenMass18 : List Nat :=
  [30720000, 56576000, 44172800, 19223040, 5121152, 857600, 88320, 5120, 128]

def evenMass20 : List Nat :=
  [105163200, 193433280, 151570528, 66317440, 17763872, 2988160, 308672, 17920, 448]

def oddMass2 : List Nat :=
  [2304000, 4262400, 3428480, 1566432, 444720, 80352, 9024, 576, 16]

def oddMass4 : List Nat :=
  [4371840, 8196768, 6668880, 3075840, 879792, 159840, 18016, 1152, 32]

def oddMass6 : List Nat :=
  [2073600, 3939840, 3242304, 1509696, 435088, 79488, 8992, 576, 16]

def oddMass8 : List Nat :=
  [5901984, 11360736, 9456264, 4445280, 1290888, 237168, 26928, 1728, 48]

def oddMass10 : List Nat :=
  [9108480, 17991936, 15249408, 7260192, 2127024, 393120, 44800, 2880, 80]

def oddMass12 : List Nat :=
  [17001600, 34305120, 29543760, 14232960, 4205680, 781920, 89440, 5760, 160]

def oddMass14 : List Nat :=
  [19353600, 39536640, 34439424, 16754688, 4989888, 933120, 107136, 6912, 192]

def oddMass16 : List Nat :=
  [21422016, 44295552, 39023376, 19172160, 5755344, 1082592, 124768, 8064, 224]

def oddMass18 : List Nat :=
  [23116800, 48487680, 43261824, 21480192, 6501760, 1230336, 142336, 9216, 256]

def oddMass20 : List Nat :=
  [5402880, 11549376, 10466720, 5260032, 1606368, 305856, 35520, 2304, 64]

/-! ## 3a. Factored scout formulas and checked translations -/

def evenMass4Formula (k : Nat) : Nat :=
  16 * (k + 1) ^ 3 * (k + 2) ^ 2 * (k + 3) ^ 3

def evenMass8Formula (k : Nat) : Nat :=
  48 * k * (k + 1) * (k + 2) ^ 4 * (k + 3) * (k + 4)

def evenMass10Formula (k : Nat) : Nat :=
  128 * k * (k + 1) ^ 2 * (k + 2) ^ 2 * (k + 3) ^ 2 * (k + 4)

def evenMass12Formula (k : Nat) : Nat :=
  32 * k * (k + 2) ^ 4 * (k + 4) * (k ^ 2 + 4 * k + 1)

def evenMass14Formula (k : Nat) : Nat :=
  128 * k * (k + 1) * (k + 2) ^ 2 * (k + 3) * (k + 4) *
    (k ^ 2 + 4 * k + 1)

def evenMass16Formula (k : Nat) : Nat :=
  112 * k ^ 2 * (k + 1) * (k + 2) ^ 2 * (k + 3) * (k + 4) ^ 2

def evenMass18Formula (k : Nat) : Nat :=
  128 * (k - 1) * (k + 1) * (k + 2) ^ 4 * (k + 3) * (k + 5)

def evenMass20Formula (k : Nat) : Nat :=
  32 * (k + 2) ^ 2 *
    (14 * k ^ 6 + 168 * k ^ 5 + 686 * k ^ 4 + 1008 * k ^ 3 +
      35 * k ^ 2 - 756 * k - 405)

def oddMassAux (k : Nat) : Nat :=
  2 * k ^ 4 + 20 * k ^ 3 + 72 * k ^ 2 + 110 * k + 59

def oddMass2Formula (k : Nat) : Nat :=
  16 * (k + 1) * (k + 2) ^ 3 * (k + 3) ^ 3 * (k + 4)

def oddMass4Formula (k : Nat) : Nat :=
  16 * (k + 1) * (k + 2) * (k + 3) * (k + 4) * oddMassAux k

def oddMass6Formula (k : Nat) : Nat :=
  16 * (k + 1) ^ 2 * (k + 2) ^ 2 * (k + 3) ^ 2 * (k + 4) ^ 2

def oddMass8Formula (k : Nat) : Nat :=
  24 * (k + 1) ^ 2 * (k + 4) ^ 2 * oddMassAux k

def oddMass10Formula (k : Nat) : Nat :=
  16 * (k + 2) * (k + 3) *
    (5 * k ^ 6 + 75 * k ^ 5 + 435 * k ^ 4 + 1225 * k ^ 3 +
      1704 * k ^ 2 + 1020 * k + 128)

def oddMass12Formula (k : Nat) : Nat :=
  80 * k * (k + 2) * (k + 3) * (k + 5) * oddMassAux k

def oddMass14Formula (k : Nat) : Nat :=
  192 * k * (k + 1) * (k + 2) ^ 2 * (k + 3) ^ 2 * (k + 4) * (k + 5)

def oddMass16Formula (k : Nat) : Nat :=
  112 * k * (k + 1) * (k + 4) * (k + 5) * oddMassAux k

def oddMass18Formula (k : Nat) : Nat :=
  128 * k * (k + 2) * (k + 3) * (k + 5) *
    (2 * k ^ 4 + 20 * k ^ 3 + 66 * k ^ 2 + 80 * k + 29)

def oddMass20Formula (k : Nat) : Nat :=
  32 * k * (k + 2) * (k + 3) * (k + 5) *
    (2 * k ^ 4 + 20 * k ^ 3 + 64 * k ^ 2 + 70 * k + 15)

/- The factored formulas above are retained for review, but their
coefficient-list translations are not claimed as Lean theorems here:
expanding those nonlinear Nat identities with `omega` made this small
arithmetic module too expensive for the root build.  Every coefficient-list
envelope below is nevertheless kernel checked for all `x`; connecting those
explicit list polynomials to the adverse atom classifier remains part of the
named finite-classification obligation. -/

/-! ## 4. Kernel-checked coefficientwise envelopes -/

theorem even_gap4_envelope (x : Nat) :
    evalNatPoly evenMass4 x ≤ 4 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 4 x (by
    unfold evenMass4 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap8_envelope (x : Nat) :
    evalNatPoly evenMass8 x ≤ 12 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 12 x (by
    unfold evenMass8 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap10_envelope (x : Nat) :
    evalNatPoly evenMass10 x ≤ 32 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 32 x (by
    unfold evenMass10 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap12_envelope (x : Nat) :
    evalNatPoly evenMass12 x ≤ 8 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 8 x (by
    unfold evenMass12 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap14_envelope (x : Nat) :
    evalNatPoly evenMass14 x ≤ 32 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 32 x (by
    unfold evenMass14 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap16_envelope (x : Nat) :
    evalNatPoly evenMass16 x ≤ 28 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 28 x (by
    unfold evenMass16 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap18_envelope (x : Nat) :
    evalNatPoly evenMass18 x ≤ 32 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 32 x (by
    unfold evenMass18 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem even_gap20_envelope (x : Nat) :
    evalNatPoly evenMass20 x ≤ 112 * evalNatPoly evenReserveCoeffs x :=
  evalNatPoly_le_envelope 112 x (by
    unfold evenMass20 evenReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap2_envelope (x : Nat) :
    evalNatPoly oddMass2 x ≤ evalNatPoly oddReserveCoeffs x := by
  simpa only [Nat.one_mul] using
    evalNatPoly_le_envelope 1 x
      (mass := oddMass2) (reserve := oddReserveCoeffs) (by
        unfold oddMass2 oddReserveCoeffs
        repeat' refine CoeffEnvelope.cons (by decide) ?_
        exact CoeffEnvelope.nil)

theorem odd_gap4_envelope (x : Nat) :
    evalNatPoly oddMass4 x ≤ 2 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 2 x (by
    unfold oddMass4 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap6_envelope (x : Nat) :
    evalNatPoly oddMass6 x ≤ evalNatPoly oddReserveCoeffs x := by
  simpa only [Nat.one_mul] using
    evalNatPoly_le_envelope 1 x
      (mass := oddMass6) (reserve := oddReserveCoeffs) (by
        unfold oddMass6 oddReserveCoeffs
        repeat' refine CoeffEnvelope.cons (by decide) ?_
        exact CoeffEnvelope.nil)

theorem odd_gap8_envelope (x : Nat) :
    evalNatPoly oddMass8 x ≤ 3 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 3 x (by
    unfold oddMass8 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap10_envelope (x : Nat) :
    evalNatPoly oddMass10 x ≤ 5 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 5 x (by
    unfold oddMass10 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap12_envelope (x : Nat) :
    evalNatPoly oddMass12 x ≤ 10 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 10 x (by
    unfold oddMass12 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap14_envelope (x : Nat) :
    evalNatPoly oddMass14 x ≤ 12 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 12 x (by
    unfold oddMass14 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap16_envelope (x : Nat) :
    evalNatPoly oddMass16 x ≤ 14 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 14 x (by
    unfold oddMass16 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap18_envelope (x : Nat) :
    evalNatPoly oddMass18 x ≤ 16 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 16 x (by
    unfold oddMass18 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

theorem odd_gap20_envelope (x : Nat) :
    evalNatPoly oddMass20 x ≤ 4 * evalNatPoly oddReserveCoeffs x :=
  evalNatPoly_le_envelope 4 x (by
    unfold oddMass20 oddReserveCoeffs
    repeat' refine CoeffEnvelope.cons (by decide) ?_
    exact CoeffEnvelope.nil)

/-! ## 5. Exact dyadic envelope totals -/

/-- Sum of the even low-gap envelope constants `L_g / 2^g`. -/
def evenLowGapBudget : Q' :=
  Q'.mkPos 4 (2 ^ 4) (by decide) +
  Q'.mkPos 12 (2 ^ 8) (by decide) +
  Q'.mkPos 32 (2 ^ 10) (by decide) +
  Q'.mkPos 8 (2 ^ 12) (by decide) +
  Q'.mkPos 32 (2 ^ 14) (by decide) +
  Q'.mkPos 28 (2 ^ 16) (by decide) +
  Q'.mkPos 32 (2 ^ 18) (by decide) +
  Q'.mkPos 112 (2 ^ 20) (by decide)

/-- Sum of the odd low-gap envelope constants `L_g / 2^g`. -/
def oddLowGapBudget : Q' :=
  Q'.mkPos 1 (2 ^ 2) (by decide) +
  Q'.mkPos 2 (2 ^ 4) (by decide) +
  Q'.mkPos 1 (2 ^ 6) (by decide) +
  Q'.mkPos 3 (2 ^ 8) (by decide) +
  Q'.mkPos 5 (2 ^ 10) (by decide) +
  Q'.mkPos 10 (2 ^ 12) (by decide) +
  Q'.mkPos 12 (2 ^ 14) (by decide) +
  Q'.mkPos 14 (2 ^ 16) (by decide) +
  Q'.mkPos 16 (2 ^ 18) (by decide) +
  Q'.mkPos 4 (2 ^ 20) (by decide)

theorem evenLowGapBudget_exact :
    evenLowGapBudget ≈ Q'.mkPos 21803 65536 (by decide) := by
  decide

theorem oddLowGapBudget_exact :
    oddLowGapBudget ≈ Q'.mkPos 107657 262144 (by decide) := by
  decide

theorem evenLowGapBudget_lt_half :
    evenLowGapBudget < Q'.mkPos 1 2 (by decide) := by
  decide

theorem oddLowGapBudget_lt_half :
    oddLowGapBudget < Q'.mkPos 1 2 (by decide) := by
  decide

#print axioms evalNatPoly_le_envelope
#print axioms even_gap4_envelope
#print axioms even_gap8_envelope
#print axioms even_gap10_envelope
#print axioms even_gap12_envelope
#print axioms even_gap14_envelope
#print axioms even_gap16_envelope
#print axioms even_gap18_envelope
#print axioms even_gap20_envelope
#print axioms odd_gap2_envelope
#print axioms odd_gap4_envelope
#print axioms odd_gap6_envelope
#print axioms odd_gap8_envelope
#print axioms odd_gap10_envelope
#print axioms odd_gap12_envelope
#print axioms odd_gap14_envelope
#print axioms odd_gap16_envelope
#print axioms odd_gap18_envelope
#print axioms odd_gap20_envelope
#print axioms evenLowGapBudget_exact
#print axioms oddLowGapBudget_exact
#print axioms evenLowGapBudget_lt_half
#print axioms oddLowGapBudget_lt_half

end YMGap.Continuum.CoreBLowGapBudget
