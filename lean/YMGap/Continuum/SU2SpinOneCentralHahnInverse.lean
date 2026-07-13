/-
# Constructive inverse of the physical spin-one Hahn matrix

The adjugate identities are division-free.  This successor proves the named
strict positivity needed by `Q'.recipPos`, scales the symbolic adjugate by the
derived reciprocal, and obtains genuine left and right inverse identities for
the physical central-shell matrix.  No determinant-nonzero or inverse premise
is assumed; the shell-level interface derives positivity from `2 <= t <= n`.
-/

import YMGap.Continuum.SU2CentralHahnDeterminantScale

namespace YMGap.Continuum.SU2SpinOneCentralHahnInverse

open YMGap.Constructive
open YMGap.Continuum.SU2SpinOneCentralHahnDeterminant
open YMGap.Continuum.SU2SpinOneCentralHahnAdjugate
open YMGap.Continuum.SU2ThreeByThreeAdjugate
open YMGap.Continuum.SU2CentralHahnDeterminantScale

/-- The exact determinant scale of the physical spin-one central-shell matrix. -/
def spinOneDetScale (n : Nat) : Q' :=
  (((2 : Q') * Q'.ofNat n) * (Q'.ofNat n + 1)) * (Q'.ofNat n + 2)

/-- The determinant scale is strictly positive as soon as the second label is
positive (in particular on every physical central shell). -/
theorem spinOneDetScale_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < spinOneDetScale n := by
  cases n with
  | zero => omega
  | succ n =>
      have hnq : (0 : Q') < Q'.ofNat (n + 1) := Q'.ofNat_succ_pos n
      exact Q'.mul_pos
        (Q'.mul_pos (Q'.mul_pos (by decide) hnq)
          (Q'.add_pos hnq (by decide)))
        (Q'.add_pos hnq (by decide))

/-- The rational determinant used for inversion is exactly the `m=2`
specialization of the general prospective Hahn determinant scale. -/
theorem spinOneDetScale_eq_general_scale (n : Nat) :
    (spinOneDetScale n).eqv (Q'.ofNat (centralHahnDetScale 2 n)) := by
  rw [centralHahnDetScale_two]
  unfold spinOneDetScale Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show (2 : Q').num = 2 from rfl,
    show ((2 : Q').den : Int) = 1 from rfl,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  push_cast
  rfl

/-- The actual reciprocal-scaled adjugate. -/
def physicalHahnInverse (n t : Nat) (hn : 0 < n) : Nat -> Nat -> Q' :=
  fun r c =>
    Q'.recipPos (spinOneDetScale n) (spinOneDetScale_pos n hn) *
      adj3 (symbolicHahn n t) r c

private theorem add3_congr {a0 a1 a2 b0 b1 b2 : Q'}
    (h0 : a0.eqv b0) (h1 : a1.eqv b1) (h2 : a2.eqv b2) :
    (a0 + a1 + a2).eqv (b0 + b1 + b2) := by
  have h01 : (a0 + a1).eqv (b0 + b1) :=
    Q'.eqv_trans _ (b0 + a1) _
      (Q'.add_eqv_congr_right a0 b0 a1 h0)
      (Q'.add_eqv_congr_left b0 a1 b1 h1)
  exact Q'.eqv_trans _ (b0 + b1 + a2) _
    (Q'.add_eqv_congr_right (a0 + a1) (b0 + b1) a2 h01)
    (Q'.add_eqv_congr_left (b0 + b1) a2 b2 h2)

private theorem factor_three (s x y z : Q') :
    (s * x + s * y + s * z).eqv (s * (x + y + z)) := by
  refine Q'.eqv_trans _ (s * (x + y) + s * z) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.mul_add_eqv s x y))
  · exact Q'.eqv_symm (Q'.mul_add_eqv s (x + y) z)

private theorem matMul3_scale_left (s : Q')
    (A B : Nat -> Nat -> Q') (r c : Nat) :
    (matMul3 (fun i j => s * A i j) B r c).eqv
      (s * matMul3 A B r c) := by
  unfold matMul3
  refine Q'.eqv_trans _
    (s * (A r 0 * B 0 c) + s * (A r 1 * B 1 c) +
      s * (A r 2 * B 2 c)) _ ?_ ?_
  · exact add3_congr
      (Q'.mul_assoc_eqv s (A r 0) (B 0 c))
      (Q'.mul_assoc_eqv s (A r 1) (B 1 c))
      (Q'.mul_assoc_eqv s (A r 2) (B 2 c))
  · exact factor_three s _ _ _

private theorem mul_scale_right_term (a s b : Q') :
    (a * (s * b)).eqv (s * (a * b)) := by
  refine Q'.eqv_trans _ ((a * s) * b) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a s b)) ?_
  refine Q'.eqv_trans _ ((s * a) * b) _
    (Q'.mul_eqv_congr_right _ _ b (Q'.mul_comm_eqv a s)) ?_
  exact Q'.mul_assoc_eqv s a b

private theorem matMul3_scale_right (s : Q')
    (A B : Nat -> Nat -> Q') (r c : Nat) :
    (matMul3 A (fun i j => s * B i j) r c).eqv
      (s * matMul3 A B r c) := by
  unfold matMul3
  refine Q'.eqv_trans _
    (s * (A r 0 * B 0 c) + s * (A r 1 * B 1 c) +
      s * (A r 2 * B 2 c)) _ ?_ ?_
  · exact add3_congr
      (mul_scale_right_term (A r 0) s (B 0 c))
      (mul_scale_right_term (A r 1) s (B 1 c))
      (mul_scale_right_term (A r 2) s (B 2 c))
  · exact factor_three s _ _ _

private theorem reciprocal_mul_scale (n : Nat) (hn : 0 < n) :
    (Q'.recipPos (spinOneDetScale n) (spinOneDetScale_pos n hn) *
      spinOneDetScale n).eqv 1 := by
  refine Q'.eqv_trans _
    (spinOneDetScale n *
      Q'.recipPos (spinOneDetScale n) (spinOneDetScale_pos n hn)) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.mul_recipPos_eqv _ _

/-- The reciprocal-scaled adjugate is a genuine left inverse. -/
theorem physicalHahnInverse_mul (n t r c : Nat) (hn : 0 < n)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (physicalHahnInverse n t hn) (physicalHahn n t) r c).eqv
      (if r = c then 1 else 0) := by
  let s := Q'.recipPos (spinOneDetScale n) (spinOneDetScale_pos n hn)
  refine Q'.eqv_trans _
    (s * matMul3 (adj3 (symbolicHahn n t)) (physicalHahn n t) r c) _ ?_ ?_
  · exact matMul3_scale_left s (adj3 (symbolicHahn n t))
      (physicalHahn n t) r c
  · by_cases hrc : r = c
    · simp only [if_pos hrc]
      refine Q'.eqv_trans _ (s * spinOneDetScale n) _
        (Q'.mul_eqv_congr_left s _ _ ?_) ?_
      · have hscaled :=
          physical_adjugate_mul_explicit n t r c ht htn hr hc
        rw [if_pos hrc] at hscaled
        simpa only [spinOneDetScale] using hscaled
      · exact reciprocal_mul_scale n hn
    · simp only [if_neg hrc]
      refine Q'.eqv_trans _ (s * 0) _
        (Q'.mul_eqv_congr_left s _ _ ?_) ?_
      · have hscaled :=
          physical_adjugate_mul_explicit n t r c ht htn hr hc
        rw [if_neg hrc] at hscaled
        exact hscaled
      · exact Q'.mul_zero_eqv s

/-- The same reciprocal-scaled adjugate is a genuine right inverse. -/
theorem physicalHahn_mul_inverse (n t r c : Nat) (hn : 0 < n)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (physicalHahn n t) (physicalHahnInverse n t hn) r c).eqv
      (if r = c then 1 else 0) := by
  let s := Q'.recipPos (spinOneDetScale n) (spinOneDetScale_pos n hn)
  refine Q'.eqv_trans _
    (s * matMul3 (physicalHahn n t) (adj3 (symbolicHahn n t)) r c) _ ?_ ?_
  · exact matMul3_scale_right s (physicalHahn n t)
      (adj3 (symbolicHahn n t)) r c
  · by_cases hrc : r = c
    · simp only [if_pos hrc]
      refine Q'.eqv_trans _ (s * spinOneDetScale n) _
        (Q'.mul_eqv_congr_left s _ _ ?_) ?_
      · have hscaled :=
          physical_mul_adjugate_explicit n t r c ht htn hr hc
        rw [if_pos hrc] at hscaled
        simpa only [spinOneDetScale] using hscaled
      · exact reciprocal_mul_scale n hn
    · simp only [if_neg hrc]
      refine Q'.eqv_trans _ (s * 0) _
        (Q'.mul_eqv_congr_left s _ _ ?_) ?_
      · have hscaled :=
          physical_mul_adjugate_explicit n t r c ht htn hr hc
        rw [if_neg hrc] at hscaled
        exact hscaled
      · exact Q'.mul_zero_eqv s

/-- Shell-facing inverse whose positivity proof is derived from the physical
range rather than supplied as an independent premise. -/
def centralShellHahnInverse (n t : Nat) (ht : 2 <= t) (htn : t <= n) :
    Nat -> Nat -> Q' :=
  physicalHahnInverse n t (by omega)

/-- Premise-free-within-the-shell left inverse. -/
theorem centralShellHahnInverse_mul (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (centralShellHahnInverse n t ht htn) (physicalHahn n t) r c).eqv
      (if r = c then 1 else 0) := by
  exact physicalHahnInverse_mul n t r c (by omega) ht htn hr hc

/-- Premise-free-within-the-shell right inverse. -/
theorem physicalHahn_mul_centralShellHahnInverse (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (physicalHahn n t) (centralShellHahnInverse n t ht htn) r c).eqv
      (if r = c then 1 else 0) := by
  exact physicalHahn_mul_inverse n t r c (by omega) ht htn hr hc

end YMGap.Continuum.SU2SpinOneCentralHahnInverse

#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.spinOneDetScale_pos
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.spinOneDetScale_eq_general_scale
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.physicalHahnInverse_mul
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.physicalHahn_mul_inverse
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.centralShellHahnInverse_mul
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnInverse.physicalHahn_mul_centralShellHahnInverse
