/-
Constructive exact certificate for the cubic even-gap tail used in Core B.

For `g = 22 + 2j`, write `g = 2m` with `m = 11 + j`.  Then

    g^3 / 2^g = 8m^3 / 4^m.

The polynomial

    P(m) = 288m^3 + 288m^2 + 480m + 352

satisfies the exact recurrence

    4 P(m) = 864m^3 + P(m+1).

Consequently `F(m) = P(m)/(27 * 4^m)` is a telescoping potential:

    8m^3/4^m + F(m+1) = F(m).

At `m = 11`, `F(11) = 3311/884736`.  This module packages that exact
identity together with a constructive geometric remainder estimate and
the explicit Type-level modulus `δ.den`.

This is deliberately only the arithmetic cubic-majorant certificate.  It
does not assert the analytic comparison from the adverse Core-B mass to
`g^3 / 2^g`; that comparison remains a separate consumer obligation.
-/

import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.CoreBCubicEvenTail

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-! ## The telescoping potential -/

/-- Numerator of the exact telescoping potential. -/
def potentialNumerator (m : Nat) : Nat :=
  288 * m ^ 3 + 288 * m ^ 2 + 480 * m + 352

/-- The cubic even-gap summand, written at half-index `m`. -/
def cubicTermAtHalfIndex (m : Nat) : Q' :=
  Q'.mkPos (Int.ofNat (8 * m ^ 3)) (4 ^ m)
    (Nat.pow_pos (by decide))

/-- Exact rational potential whose discrete derivative is the cubic term. -/
def tailPotentialAtHalfIndex (m : Nat) : Q' :=
  Q'.mkPos (potentialNumerator m) (27 * 4 ^ m)
    (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))

/-- Numerator conversion from half-index `m` to even gap `g = 2m`. -/
theorem evenGapNumerator (m : Nat) : (2 * m) ^ 3 = 8 * m ^ 3 := by
  simp only [Nat.pow_succ, Nat.pow_zero]
  ac_rfl

/-- Denominator conversion from half-index `m` to even gap `g = 2m`. -/
theorem evenGapDenominator (m : Nat) : 2 ^ (2 * m) = 4 ^ m := by
  rw [Nat.pow_mul]

/-- `8m^3/4^m` is exactly the desired even-gap term `(2m)^3/2^(2m)`. -/
theorem cubicTermAtHalfIndex_eq_evenGap (m : Nat) :
    cubicTermAtHalfIndex m ≈
      Q'.mkPos (Int.ofNat ((2 * m) ^ 3)) (2 ^ (2 * m))
        (Nat.pow_pos (by decide)) := by
  show (cubicTermAtHalfIndex m).num *
      ((Q'.mkPos (Int.ofNat ((2 * m) ^ 3)) (2 ^ (2 * m))
        (Nat.pow_pos (by decide))).den : Int) =
    (Q'.mkPos (Int.ofNat ((2 * m) ^ 3)) (2 ^ (2 * m))
      (Nat.pow_pos (by decide))).num *
        ((cubicTermAtHalfIndex m).den : Int)
  simp only [cubicTermAtHalfIndex, Q'.mkPos_num, Q'.mkPos_den]
  rw [evenGapNumerator, evenGapDenominator]

/-- Polynomial identity underlying the exact telescoping recurrence. -/
theorem potentialNumerator_recurrence (m : Nat) :
    4 * potentialNumerator m =
      864 * m ^ 3 + potentialNumerator (m + 1) := by
  unfold potentialNumerator
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.add_mul, Nat.mul_add]
  omega

/-- One exact telescoping step:
`8m^3/4^m + F(m+1) ≈ F(m)`. -/
theorem cubicTerm_potential_step (m : Nat) :
    cubicTermAtHalfIndex m + tailPotentialAtHalfIndex (m + 1) ≈
      tailPotentialAtHalfIndex m := by
  show (cubicTermAtHalfIndex m + tailPotentialAtHalfIndex (m + 1)).num *
      ((tailPotentialAtHalfIndex m).den : Int) =
    (tailPotentialAtHalfIndex m).num *
      (((cubicTermAtHalfIndex m +
        tailPotentialAtHalfIndex (m + 1)).den : Int))
  rw [Q'.add_den_cast]
  change (((cubicTermAtHalfIndex m).num *
      ((tailPotentialAtHalfIndex (m + 1)).den : Int) +
      (tailPotentialAtHalfIndex (m + 1)).num *
        ((cubicTermAtHalfIndex m).den : Int)) *
          ((tailPotentialAtHalfIndex m).den : Int)) =
    (tailPotentialAtHalfIndex m).num *
      (((cubicTermAtHalfIndex m).den : Int) *
        ((tailPotentialAtHalfIndex (m + 1)).den : Int))
  simp only [cubicTermAtHalfIndex, tailPotentialAtHalfIndex,
    Q'.mkPos_num, Q'.mkPos_den, Int.natCast_mul, Nat.pow_succ]
  have hp := potentialNumerator_recurrence m
  have hpI : (4 : Int) * (potentialNumerator m : Int) =
      (864 : Int) * (m ^ 3 : Nat) +
        (potentialNumerator (m + 1) : Int) := by
    have hcast := congrArg (fun n : Nat => (n : Int)) hp
    simpa only [Int.natCast_mul, Int.natCast_add] using hcast
  let M3 : Int := (m ^ 3 : Nat)
  let Q : Int := (4 ^ m : Nat)
  let P : Int := (potentialNumerator m : Nat)
  let Pnext : Int := (potentialNumerator (m + 1) : Nat)
  change ((8 * M3 * (27 * (Q * 4)) + Pnext * Q) * (27 * Q)) =
    P * (Q * (27 * (Q * 4)))
  have hL :
      ((8 : Int) * M3 * (27 * (Q * 4)) + Pnext * Q) * (27 * Q) =
        (((864 : Int) * M3 + Pnext) * Q) * (27 * Q) := by
    simp only [Int.add_mul]
    rw [show (8 : Int) * M3 * (27 * (Q * 4)) * (27 * Q) =
        864 * M3 * Q * (27 * Q) by
      rw [show (864 : Int) = 8 * 27 * 4 by decide]
      ac_rfl]
  have hR :
      P * (Q * (27 * (Q * 4))) =
        (((4 : Int) * P) * Q) * (27 * Q) := by
    ac_rfl
  calc
    ((8 : Int) * M3 * (27 * (Q * 4)) + Pnext * Q) * (27 * Q)
        = (((864 : Int) * M3 + Pnext) * Q) * (27 * Q) := hL
    _ = (((4 : Int) * P) * Q) * (27 * Q) := by
      change (((864 : Int) * (m ^ 3 : Nat) +
          (potentialNumerator (m + 1) : Nat)) * Q) * (27 * Q) =
        (((4 : Int) * (potentialNumerator m : Nat)) * Q) * (27 * Q)
      rw [← hpI]
    _ = P * (Q * (27 * (Q * 4))) := hR.symm

/-! ## Generic exact-tail and geometric-tail combinators -/

/-- A one-step potential identity telescopes over every finite prefix. -/
theorem finSum_with_remainder
    (a r : Nat → Q') (hstep : ∀ n, a n + r (n + 1) ≈ r n) :
    ∀ N, finSum a N + r N ≈ r 0
  | 0 => by
      rw [finSum_zero, Q'.zero_add']
      exact Q'.eqv_refl _
  | N + 1 => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (finSum a N) (a N) (r (N + 1)))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (finSum a N)
            (a N + r (N + 1)) (r N) (hstep N))
          (finSum_with_remainder a r hstep N))

/-- A nonnegative one-step ratio bound gives the corresponding power bound. -/
theorem geometric_domination_of_step
    (a : Nat → Q') (ratio : Q') (hratio : (0 : Q') ≤ ratio)
    (hstep : ∀ n, a (n + 1) ≤ ratio * a n) :
    ∀ N, a N ≤ a 0 * ratio ^ N
  | 0 => Q'.ge_of_eqv (Q'.mul_one_eqv (a 0))
  | N + 1 => by
      refine Q'.le_trans' _ _ _ (hstep N) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ ratio
          (geometric_domination_of_step a ratio hratio hstep N) hratio) ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv ratio (a 0) (ratio ^ N))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (ratio * a 0) (a 0 * ratio) (ratio ^ N)
          (Q'.mul_comm_eqv ratio (a 0))) ?_
      exact Q'.mul_assoc_eqv (a 0) ratio (ratio ^ N)

/-! ## The even-gap tail starting at `g = 22` -/

/-- Tail summand at `g = 22 + 2j`. -/
def evenGapTailTerm (j : Nat) : Q' :=
  cubicTermAtHalfIndex (11 + j)

/-- Exact remainder after `N` terms. -/
def evenGapTailRemainder (N : Nat) : Q' :=
  tailPotentialAtHalfIndex (11 + N)

/-- The gap corresponding to tail index `j` is exactly `22 + 2j`. -/
theorem evenGapTail_gap_index (j : Nat) : 2 * (11 + j) = 22 + 2 * j := by
  omega

/-- The tail summand is the requested cubic-over-power term at gap
`g = 22 + 2j`. -/
theorem evenGapTailTerm_eq_cubic (j : Nat) :
    evenGapTailTerm j ≈
      Q'.mkPos (Int.ofNat ((22 + 2 * j) ^ 3)) (2 ^ (22 + 2 * j))
        (Nat.pow_pos (by decide)) := by
  refine Q'.eqv_trans _ _ _
    (cubicTermAtHalfIndex_eq_evenGap (11 + j)) ?_
  rw [evenGapTail_gap_index]
  exact Q'.eqv_refl _

/-- Exact one-step identity for the indexed tail. -/
theorem evenGapTail_step (j : Nat) :
    evenGapTailTerm j + evenGapTailRemainder (j + 1) ≈
      evenGapTailRemainder j := by
  simpa only [evenGapTailTerm, evenGapTailRemainder, Nat.add_assoc] using
    cubicTerm_potential_step (11 + j)

/-- Every finite prefix plus its exact remainder equals the initial potential. -/
theorem evenGapTail_exact_initial (N : Nat) :
    finSum evenGapTailTerm N + evenGapTailRemainder N ≈
      evenGapTailRemainder 0 :=
  finSum_with_remainder evenGapTailTerm evenGapTailRemainder
    evenGapTail_step N

/-- The initial potential is the exact rational `3311/884736`. -/
theorem evenGapTailRemainder_zero_exact :
    evenGapTailRemainder 0 ≈ Q'.mkPos 3311 884736 (by decide) := by
  decide

/-- Exact finite-plus-remainder form of
`Σ_{j≥0} (22+2j)^3 / 2^(22+2j) = 3311/884736`. -/
theorem evenGapTail_exact (N : Nat) :
    finSum evenGapTailTerm N + evenGapTailRemainder N ≈
      Q'.mkPos 3311 884736 (by decide) :=
  Q'.eqv_trans _ _ _ (evenGapTail_exact_initial N)
    evenGapTailRemainder_zero_exact

/-- The potential is nonnegative. -/
theorem tailPotentialAtHalfIndex_nonneg (m : Nat) :
    (0 : Q') ≤ tailPotentialAtHalfIndex m := by
  show (0 : Int) * ((tailPotentialAtHalfIndex m).den : Int) ≤
    (tailPotentialAtHalfIndex m).num * ((0 : Q').den : Int)
  simp only [Int.zero_mul, tailPotentialAtHalfIndex, Q'.mkPos_num]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (by decide)

/-- Every exact tail remainder is nonnegative. -/
theorem evenGapTailRemainder_nonneg (N : Nat) :
    (0 : Q') ≤ evenGapTailRemainder N :=
  tailPotentialAtHalfIndex_nonneg _

/-- Every finite prefix is bounded by the exact full-tail value. -/
theorem evenGapTail_partial_le_exact (N : Nat) :
    finSum evenGapTailTerm N ≤ Q'.mkPos 3311 884736 (by decide) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (evenGapTailRemainder_nonneg N))
    (Q'.le_of_eqv (evenGapTail_exact N))

/-! ## Geometric remainder and explicit modulus -/

/-- Past `m = 11`, the potential numerator grows by at most a factor two. -/
theorem potentialNumerator_half_ratio (d : Nat) :
    potentialNumerator (11 + d + 1) ≤
      2 * potentialNumerator (11 + d) := by
  unfold potentialNumerator
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.add_mul, Nat.mul_add]
  omega

/-- Because the denominator grows by four while the numerator grows by at
most two, the potential remainder contracts by a factor `1/2`. -/
theorem tailPotential_step_half (d : Nat) :
    tailPotentialAtHalfIndex (11 + d + 1) ≤
      half * tailPotentialAtHalfIndex (11 + d) := by
  show (tailPotentialAtHalfIndex (11 + d + 1)).num *
      ((half * tailPotentialAtHalfIndex (11 + d)).den : Int) ≤
    (half * tailPotentialAtHalfIndex (11 + d)).num *
      ((tailPotentialAtHalfIndex (11 + d + 1)).den : Int)
  rw [Q'.mul_den_cast]
  change (tailPotentialAtHalfIndex (11 + d + 1)).num *
      (((half).den : Int) *
        ((tailPotentialAtHalfIndex (11 + d)).den : Int)) ≤
    (half.num * (tailPotentialAtHalfIndex (11 + d)).num) *
      ((tailPotentialAtHalfIndex (11 + d + 1)).den : Int)
  simp only [tailPotentialAtHalfIndex, half, Q'.mkPos_num, Q'.mkPos_den,
    Int.natCast_mul, Nat.pow_succ]
  have hp := potentialNumerator_half_ratio d
  have hpI :
      (potentialNumerator (11 + d + 1) : Int) ≤
        (2 : Int) * (potentialNumerator (11 + d) : Int) := by
    have hcast := Int.ofNat_le.mpr hp
    simpa only [Int.natCast_mul] using hcast
  let Q : Int := (4 ^ (11 + d) : Nat)
  let P : Int := (potentialNumerator (11 + d) : Nat)
  let Pnext : Int := (potentialNumerator (11 + d + 1) : Nat)
  change Pnext * (2 * (27 * Q)) ≤ (1 * P) * (27 * (Q * 4))
  have hcommon : (0 : Int) ≤ 27 * Q :=
    Int.mul_nonneg (by decide) (Int.natCast_nonneg _)
  have hmul : Pnext * (27 * Q) ≤ (2 * P) * (27 * Q) :=
    Int.mul_le_mul_of_nonneg_right hpI hcommon
  calc
    Pnext * (2 * (27 * Q)) = (Pnext * (27 * Q)) * 2 := by ac_rfl
    _ ≤ ((2 * P) * (27 * Q)) * 2 :=
      Int.mul_le_mul_of_nonneg_right hmul (by decide)
    _ = (1 * P) * (27 * (Q * 4)) := by ac_rfl

/-- The exact tail remainder is bounded by a geometric half-power. -/
theorem evenGapTailRemainder_geometric (N : Nat) :
    evenGapTailRemainder N ≤
      evenGapTailRemainder 0 * half ^ N := by
  apply geometric_domination_of_step evenGapTailRemainder half half_nonneg
  intro n
  simpa only [evenGapTailRemainder, Nat.add_assoc] using
    tailPotential_step_half n

/-- The initial exact remainder is at most one. -/
theorem evenGapTailRemainder_zero_le_one :
    evenGapTailRemainder 0 ≤ (1 : Q') := by
  decide

/-- Half-powers are antitone under an added natural exponent. -/
theorem half_pow_antitone (i : Nat) :
    ∀ e, half ^ (i + e) ≤ half ^ i
  | 0 => Q'.le_refl' _
  | e + 1 => by
      show half * half ^ (i + e) ≤ half ^ i
      have hpnn : (0 : Q') ≤ half ^ (i + e) :=
        Q'.pow_nonneg half half_nonneg _
      have hstep : half * half ^ (i + e) ≤
          (1 : Q') * half ^ (i + e) :=
        Q'.mul_le_mul_of_nonneg_right half 1 _
          (by decide) hpnn
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv _)))
        (half_pow_antitone i e)

/-- Explicit constructive modulus: for every positive rational `δ`, all
remainders from index `δ.den` onward are at most `δ`. -/
theorem evenGapTailRemainder_modulus
    (δ : Q') (hδ : (0 : Q') < δ) (e : Nat) :
    evenGapTailRemainder (δ.den + e) ≤ δ := by
  refine Q'.le_trans' _ _ _
    (evenGapTailRemainder_geometric (δ.den + e)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (evenGapTailRemainder 0) 1
      (half ^ (δ.den + e)) evenGapTailRemainder_zero_le_one
      (Q'.pow_nonneg half half_nonneg _)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.one_mul_eqv (half ^ (δ.den + e)))) ?_
  exact Q'.le_trans' _ _ _ (half_pow_antitone δ.den e)
    (pow_half_le δ hδ)

/-! ## Reusable exact-tail certificate -/

/-- Constructive data certifying an exact nonnegative rational tail and an
explicit modulus for its remainder. -/
structure QExactTailCertificate (term : Nat → Q') : Type where
  value : Q'
  remainder : Nat → Q'
  modulus : Q' → Nat
  partial_plus_remainder :
    ∀ N, finSum term N + remainder N ≈ value
  remainder_nonneg :
    ∀ N, (0 : Q') ≤ remainder N
  remainder_small :
    ∀ δ, (0 : Q') < δ → ∀ e, remainder (modulus δ + e) ≤ δ

/-- Exact constructive certificate for the cubic even-gap tail beginning
at `g = 22`. -/
def evenGapTailCertificate : QExactTailCertificate evenGapTailTerm where
  value := Q'.mkPos 3311 884736 (by decide)
  remainder := evenGapTailRemainder
  modulus := fun δ => δ.den
  partial_plus_remainder := evenGapTail_exact
  remainder_nonneg := evenGapTailRemainder_nonneg
  remainder_small := evenGapTailRemainder_modulus

end YMGap.Continuum.CoreBCubicEvenTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapNumerator
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapDenominator
#print axioms YMGap.Continuum.CoreBCubicEvenTail.cubicTermAtHalfIndex_eq_evenGap
#print axioms YMGap.Continuum.CoreBCubicEvenTail.potentialNumerator_recurrence
#print axioms YMGap.Continuum.CoreBCubicEvenTail.cubicTerm_potential_step
#print axioms YMGap.Continuum.CoreBCubicEvenTail.finSum_with_remainder
#print axioms YMGap.Continuum.CoreBCubicEvenTail.geometric_domination_of_step
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTailTerm_eq_cubic
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTail_exact
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTail_partial_le_exact
#print axioms YMGap.Continuum.CoreBCubicEvenTail.potentialNumerator_half_ratio
#print axioms YMGap.Continuum.CoreBCubicEvenTail.tailPotential_step_half
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTailRemainder_geometric
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTailRemainder_modulus
#print axioms YMGap.Continuum.CoreBCubicEvenTail.evenGapTailCertificate
