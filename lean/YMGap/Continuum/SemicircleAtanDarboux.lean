/-
# Exact Darboux convergence for the semicircle arctangent quadratures

This successor to `SemicircleRationalPolygonBridge` closes the convergence leg
for its rational arctangent sums.  For

    U_n = Σ_{j<n} 2n/(n²+j²),   L_n = Σ_{j<n} 2n/(n²+(j+1)²),

it proves, without a completeness assumption,

* exact multiplicative refinement: `U_(PQ) ≤ U_P` and `L_P ≤ L_(PQ)`;
* the exact telescope `U_n ≈ L_n + 1/n`;
* the arbitrary common-refinement bracket `L_m ≤ U_n`;
* a constructive Cauchy real `atanIntegral` with the explicit rational modulus
  obtained from the preceding three facts;
* unconditional convergence of both `atanRiemannSeq` and the already-built
  rational polygon sequence to `atanIntegral`.

All cell comparisons are cross-multiplied over `Nat`/`Int`; all amplitudes are
exact rationals.  The value identification

    atanIntegral ≃ Constructive.Pi.halfPi

is not asserted here.  It is the remaining branch-controlled Machin addition
leg: `halfPi = 8·at5 - 2·at239`, while `atanIntegral` is the integral of
`2/(1+x²)` on `[0,1]`.

## Axiom gate

Every declaration below is checked at EOF.  Dependencies are contained in
`{propext, Quot.sound}`; there is no `Classical.*`, `native_decide`, `sorry`, or
custom axiom.
-/

import YMGap.Continuum.SemicircleRationalPolygonBridge

namespace YMGap.Continuum.SemicircleAtanDarboux

open YMGap.Constructive
open YMGap.Continuum.SemicircleRationalPolygon
open YMGap.Continuum.SemicircleValueRes

def rightCell (n j : Nat) (hn : 0 < n) : Q' := atanCell n (j+1) hn

def rightRiemannQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => rightCell n j hn) n

/-- A `1/Q` share of the coarse left cell `atanCell P i`. -/
def coarseShare (P Q i : Nat) (hP : 0 < P) (hQ : 0 < Q) : Q' :=
  Q'.mkPos (2*(P:Int)) (Q * cden P i)
    (Nat.mul_pos hQ (cden_pos hP i))

theorem refined_left_cell_le_share
    (P Q i s : Nat) (hP : 0 < P) (hQ : 0 < Q) :
    atanCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ) ≤ coarseShare P Q i hP hQ := by
  show (atanCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ)).num *
      ((coarseShare P Q i hP hQ).den : Int)
    ≤ (coarseShare P Q i hP hQ).num *
      ((atanCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ)).den : Int)
  unfold atanCell coarseShare
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hs0 : i*Q ≤ i*Q+s := Nat.le_add_right _ _
  have hsq : (i*Q)*(i*Q) ≤ (i*Q+s)*(i*Q+s) :=
    Nat.mul_le_mul hs0 hs0
  have hbase : Q*Q*(P*P+i*i) ≤ (P*Q)*(P*Q)+(i*Q+s)*(i*Q+s) := by
    have hPP : Q*Q*(P*P) = (P*Q)*(P*Q) := by ac_rfl
    have hii : Q*Q*(i*i) = (i*Q)*(i*Q) := by ac_rfl
    rw [Nat.mul_add, hPP, hii]
    exact Nat.add_le_add_left hsq _
  have hscaled : (2*P*Q) * (Q*(P*P+i*i)) ≤
      (2*P) * ((P*Q)*(P*Q)+(i*Q+s)*(i*Q+s)) := by
    have heL : (2*P*Q) * (Q*(P*P+i*i)) =
        (2*P) * (Q*Q*(P*P+i*i)) := by ac_rfl
    rw [heL]
    exact Nat.mul_le_mul_left (2*P) hbase
  have hI : (((2*P*Q) * (Q*(P*P+i*i)) : Nat) : Int) ≤
      (((2*P) * ((P*Q)*(P*Q)+(i*Q+s)*(i*Q+s)) : Nat) : Int) := by
    exact_mod_cast hscaled
  unfold cden
  push_cast at hI ⊢
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hI

theorem finSum_coarseShare_eqv (P Q i : Nat) (hP : 0 < P) (hQ : 0 < Q) :
    (RationalTail.finSum (fun _ => coarseShare P Q i hP hQ) Q).eqv
      (atanCell P i hP) := by
  refine Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv (coarseShare P Q i hP hQ) Q) ?_
  show (Q'.ofNat Q * coarseShare P Q i hP hQ).eqv (atanCell P i hP)
  show (Q'.ofNat Q * coarseShare P Q i hP hQ).num *
      ((atanCell P i hP).den : Int)
    = (atanCell P i hP).num *
      ((Q'.ofNat Q * coarseShare P Q i hP hQ).den : Int)
  have hnum : (Q'.ofNat Q * coarseShare P Q i hP hQ).num =
      (Q:Int) * (2*(P:Int)) := by
    show (Q'.ofNat Q).num * (coarseShare P Q i hP hQ).num = _
    unfold coarseShare
    rw [Q'.mkPos_num]
    rfl
  have hden : ((Q'.ofNat Q * coarseShare P Q i hP hQ).den : Int) =
      (Q:Int) * ((cden P i : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    unfold coarseShare
    rw [Q'.mkPos_den]
    push_cast
    change (1 : Int) * ((Q:Int) * ((cden P i : Nat) : Int)) = _
    rw [Int.one_mul]
  unfold atanCell
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]
  ac_rfl

/-- A `1/Q` share of the coarse right cell `atanCell P (i+1)`. -/
def coarseRightShare (P Q i : Nat) (hP : 0 < P) (hQ : 0 < Q) : Q' :=
  Q'.mkPos (2*(P:Int)) (Q * cden P (i+1))
    (Nat.mul_pos hQ (cden_pos hP (i+1)))

theorem coarseRightShare_le_refined_right_cell
    (P Q i s : Nat) (hP : 0 < P) (hQ : 0 < Q) (hs : s < Q) :
    coarseRightShare P Q i hP hQ ≤
      rightCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ) := by
  show (coarseRightShare P Q i hP hQ).num *
      ((rightCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ)).den : Int)
    ≤ (rightCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ)).num *
      ((coarseRightShare P Q i hP hQ).den : Int)
  unfold coarseRightShare rightCell atanCell
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hsQ : s + 1 ≤ Q := hs
  have hidx : i*Q+s+1 ≤ (i+1)*Q := by
    rw [Nat.succ_mul]
    omega
  have hsq : (i*Q+s+1)*(i*Q+s+1) ≤ ((i+1)*Q)*((i+1)*Q) :=
    Nat.mul_le_mul hidx hidx
  have hbase : (P*Q)*(P*Q)+(i*Q+s+1)*(i*Q+s+1) ≤
      Q*Q*(P*P+(i+1)*(i+1)) := by
    have hPP : (P*Q)*(P*Q) = Q*Q*(P*P) := by ac_rfl
    have hii : ((i+1)*Q)*((i+1)*Q) = Q*Q*((i+1)*(i+1)) := by ac_rfl
    calc
      (P*Q)*(P*Q)+(i*Q+s+1)*(i*Q+s+1)
          ≤ (P*Q)*(P*Q)+((i+1)*Q)*((i+1)*Q) :=
            Nat.add_le_add_left hsq _
      _ = Q*Q*(P*P+(i+1)*(i+1)) := by
            rw [hPP, hii]
            exact (Nat.mul_add (Q*Q) (P*P) ((i+1)*(i+1))).symm
  have hscaled : (2*P) * ((P*Q)*(P*Q)+(i*Q+s+1)*(i*Q+s+1)) ≤
      (2*P*Q) * (Q*(P*P+(i+1)*(i+1))) := by
    have heR : (2*P*Q) * (Q*(P*P+(i+1)*(i+1))) =
        (2*P) * (Q*Q*(P*P+(i+1)*(i+1))) := by ac_rfl
    rw [heR]
    exact Nat.mul_le_mul_left (2*P) hbase
  have hI : (((2*P) * ((P*Q)*(P*Q)+(i*Q+s+1)*(i*Q+s+1)) : Nat) : Int) ≤
      (((2*P*Q) * (Q*(P*P+(i+1)*(i+1))) : Nat) : Int) := by
    exact_mod_cast hscaled
  unfold cden
  push_cast at hI ⊢
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hI

theorem finSum_coarseRightShare_eqv
    (P Q i : Nat) (hP : 0 < P) (hQ : 0 < Q) :
    (RationalTail.finSum (fun _ => coarseRightShare P Q i hP hQ) Q).eqv
      (rightCell P i hP) := by
  refine Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv (coarseRightShare P Q i hP hQ) Q) ?_
  show (Q'.ofNat Q * coarseRightShare P Q i hP hQ).eqv (atanCell P (i+1) hP)
  show (Q'.ofNat Q * coarseRightShare P Q i hP hQ).num *
      ((atanCell P (i+1) hP).den : Int)
    = (atanCell P (i+1) hP).num *
      ((Q'.ofNat Q * coarseRightShare P Q i hP hQ).den : Int)
  have hnum : (Q'.ofNat Q * coarseRightShare P Q i hP hQ).num =
      (Q:Int) * (2*(P:Int)) := by
    show (Q'.ofNat Q).num * (coarseRightShare P Q i hP hQ).num = _
    unfold coarseRightShare
    rw [Q'.mkPos_num]
    rfl
  have hden : ((Q'.ofNat Q * coarseRightShare P Q i hP hQ).den : Int) =
      (Q:Int) * ((cden P (i+1) : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    unfold coarseRightShare
    rw [Q'.mkPos_den]
    push_cast
    change (1 : Int) * ((Q:Int) * ((cden P (i+1) : Nat) : Int)) = _
    rw [Int.one_mul]
  unfold atanCell
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]
  ac_rfl

theorem refined_left_sum_le_coarse (P Q : Nat) (hP : 0 < P) (hQ : 0 < Q) :
    atanRiemannQ (P*Q) (Nat.mul_pos hP hQ) ≤ atanRiemannQ P hP := by
  unfold atanRiemannQ
  have hblock := finSum_block
    (fun j => atanCell (P*Q) j (Nat.mul_pos hP hQ)) Q P
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hblock) ?_
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro i
  refine Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _
      (fun s => refined_left_cell_le_share P Q i s hP hQ) Q) ?_
  exact Q'.le_of_eqv (finSum_coarseShare_eqv P Q i hP hQ)

theorem coarse_right_sum_le_refined (P Q : Nat) (hP : 0 < P) (hQ : 0 < Q) :
    rightRiemannQ P hP ≤ rightRiemannQ (P*Q) (Nat.mul_pos hP hQ) := by
  unfold rightRiemannQ
  have hblock := finSum_block
    (fun j => rightCell (P*Q) j (Nat.mul_pos hP hQ)) Q P
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hblock)
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro i
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (finSum_coarseRightShare_eqv P Q i hP hQ)) ?_
  have hprefix : ∀ m : Nat, m ≤ Q →
      RationalTail.finSum (fun _ => coarseRightShare P Q i hP hQ) m ≤
        RationalTail.finSum
          (fun s => rightCell (P*Q) (i*Q+s) (Nat.mul_pos hP hQ)) m := by
    intro m hm
    induction m with
    | zero => exact Q'.le_refl' 0
    | succ m ih =>
        rw [RationalTail.finSum_succ, RationalTail.finSum_succ]
        exact Q'.add_le_add (ih (Nat.le_trans (Nat.le_succ m) hm))
          (coarseRightShare_le_refined_right_cell P Q i m hP hQ
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))
  exact hprefix Q (Nat.le_refl Q)

theorem rightCell_le_leftCell (n j : Nat) (hn : 0 < n) :
    rightCell n j hn ≤ atanCell n j hn := by
  show (rightCell n j hn).num * ((atanCell n j hn).den : Int) ≤
    (atanCell n j hn).num * ((rightCell n j hn).den : Int)
  unfold rightCell atanCell
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hj : j ≤ j+1 := Nat.le_succ j
  have hsq : j*j ≤ (j+1)*(j+1) := Nat.mul_le_mul hj hj
  have hd : cden n j ≤ cden n (j+1) := Nat.add_le_add_left hsq _
  have hscale : (2*n) * cden n j ≤ (2*n) * cden n (j+1) :=
    Nat.mul_le_mul_left (2*n) hd
  exact_mod_cast hscale

theorem rightRiemannQ_le_atanRiemannQ (n : Nat) (hn : 0 < n) :
    rightRiemannQ n hn ≤ atanRiemannQ n hn := by
  unfold rightRiemannQ atanRiemannQ
  exact ExpNeg.finSum_le_finSum_of_termwise _ _
    (fun j => rightCell_le_leftCell n j hn) n

theorem atanCell_zero_eqv_two_over (n : Nat) (hn : 0 < n) :
    (atanCell n 0 hn).eqv (Q'.mkPos 2 n hn) := by
  show (atanCell n 0 hn).num * ((Q'.mkPos 2 n hn).den : Int) =
    (Q'.mkPos 2 n hn).num * ((atanCell n 0 hn).den : Int)
  unfold atanCell cden
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  rw [Int.add_zero]
  ac_rfl

theorem atanCell_diag_eqv_one_over (n : Nat) (hn : 0 < n) :
    (atanCell n n hn).eqv (Q'.mkPos 1 n hn) := by
  show (atanCell n n hn).num * ((Q'.mkPos 1 n hn).den : Int) =
    (Q'.mkPos 1 n hn).num * ((atanCell n n hn).den : Int)
  unfold atanCell cden
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  rw [Int.one_mul, ← Int.two_mul]
  ac_rfl

theorem two_over_sub_one_over_eqv_one_over (n : Nat) (hn : 0 < n) :
    (Q'.mkPos 2 n hn + (-Q'.mkPos 1 n hn)).eqv (Q'.mkPos 1 n hn) := by
  have hsplit : (Q'.mkPos 2 n hn).eqv
      (Q'.mkPos 1 n hn + Q'.mkPos 1 n hn) := by
    show (Q'.mkPos 2 n hn).num *
        ((Q'.mkPos 1 n hn + Q'.mkPos 1 n hn).den : Int) =
      (Q'.mkPos 1 n hn + Q'.mkPos 1 n hn).num *
        ((Q'.mkPos 2 n hn).den : Int)
    have hden : ((Q'.mkPos 1 n hn + Q'.mkPos 1 n hn).den : Int) =
        (n : Int) * (n : Int) := by
      rw [Q'.add_den_cast]
      have hd : (Q'.mkPos 1 n hn).den = n := Q'.mkPos_den _ _ _
      rw [hd]
    have hnum : (Q'.mkPos 1 n hn + Q'.mkPos 1 n hn).num =
        (1 : Int) * (n : Int) + (1 : Int) * (n : Int) := by
      show (Q'.mkPos 1 n hn).num * ((Q'.mkPos 1 n hn).den : Int) +
          (Q'.mkPos 1 n hn).num * ((Q'.mkPos 1 n hn).den : Int) = _
      rw [Q'.mkPos_num, Q'.mkPos_den]
    rw [Q'.mkPos_num, Q'.mkPos_den, hden, hnum]
    rw [Int.one_mul, ← Int.two_mul]
    ac_rfl
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-Q'.mkPos 1 n hn) hsplit) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q'.mkPos 1 n hn) (Q'.mkPos 1 n hn)
      (-Q'.mkPos 1 n hn)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.mkPos 1 n hn) _ 0
      (Q'.add_neg_self_eqv (Q'.mkPos 1 n hn))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (Q'.mkPos 1 n hn))

/-- Exact Darboux gap: the left sum is the right sum plus `1/n`. -/
theorem atanRiemannQ_eqv_right_add_one_over (n : Nat) (hn : 0 < n) :
    (atanRiemannQ n hn).eqv
      (rightRiemannQ n hn + Q'.mkPos 1 n hn) := by
  let g : RationalTail.QSeq := fun j => atanCell n j hn
  have hpeel := RationalTail.finSum_peel_left g n
  have hbase : (atanRiemannQ n hn + atanCell n n hn).eqv
      (atanCell n 0 hn + rightRiemannQ n hn) := by
    unfold atanRiemannQ rightRiemannQ rightCell
    change (RationalTail.finSum g n + g n).eqv
      (g 0 + RationalTail.finSum (fun i => g (i+1)) n)
    rw [← RationalTail.finSum_succ]
    exact hpeel
  have hcancel : ((atanRiemannQ n hn + atanCell n n hn) +
      (-atanCell n n hn)).eqv (atanRiemannQ n hn) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (atanRiemannQ n hn) (atanCell n n hn)
        (-atanCell n n hn)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (atanRiemannQ n hn) _ 0
        (Q'.add_neg_self_eqv (atanCell n n hn))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (atanRiemannQ n hn))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-atanCell n n hn) hbase) ?_
  have hreorder : ((atanCell n 0 hn + rightRiemannQ n hn) +
      (-atanCell n n hn)).eqv
      (rightRiemannQ n hn + (atanCell n 0 hn + (-atanCell n n hn))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (atanCell n 0 hn) (rightRiemannQ n hn)
        (-atanCell n n hn)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (atanCell n 0 hn) _ _
        (Q'.add_comm_eqv (rightRiemannQ n hn) (-atanCell n n hn))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (atanCell n 0 hn)
        (-atanCell n n hn) (rightRiemannQ n hn))) ?_
    exact Q'.add_comm_eqv
      (atanCell n 0 hn + (-atanCell n n hn)) (rightRiemannQ n hn)
  refine Q'.eqv_trans _ _ _ hreorder ?_
  refine Q'.add_eqv_congr_left (rightRiemannQ n hn) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-atanCell n n hn)
      (atanCell_zero_eqv_two_over n hn)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.mkPos 2 n hn) _ _
      (by
        have hdiag := atanCell_diag_eqv_one_over n hn
        exact Q'.neg_eqv_congr _ _ hdiag))
    (two_over_sub_one_over_eqv_one_over n hn)

/-- Common-refinement bracket: every right sum lies below every left sum. -/
theorem rightRiemannQ_le_atanRiemannQ_cross
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    rightRiemannQ m hm ≤ atanRiemannQ n hn := by
  have h1 := coarse_right_sum_le_refined m n hm hn
  have h2 := rightRiemannQ_le_atanRiemannQ (m*n) (Nat.mul_pos hm hn)
  have h3 := refined_left_sum_le_coarse n m hn hm
  have h3' : atanRiemannQ (m*n) (Nat.mul_pos hm hn) ≤ atanRiemannQ n hn := by
    simpa only [Nat.mul_comm m n] using h3
  have h12 : rightRiemannQ m hm ≤ atanRiemannQ (m*n) (Nat.mul_pos hm hn) :=
    Q'.le_trans' _ _ _ h1 h2
  exact Q'.le_trans' _ _ _ h12 h3'

theorem atanRiemannQ_le_other_add_one_over
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    atanRiemannQ m hm ≤ atanRiemannQ n hn + Q'.mkPos 1 m hm := by
  have hgap := Q'.le_of_eqv (atanRiemannQ_eqv_right_add_one_over m hm)
  have hcross := rightRiemannQ_le_atanRiemannQ_cross m n hm hn
  exact Q'.le_trans' _ _ _ hgap
    (Q'.add_le_add_right _ _ _ hcross)

theorem one_over_le_two_over (n : Nat) (hn : 0 < n) :
    Q'.mkPos 1 n hn ≤ Q'.mkPos 2 n hn := by
  show (Q'.mkPos 1 n hn).num * ((Q'.mkPos 2 n hn).den : Int) ≤
    (Q'.mkPos 2 n hn).num * ((Q'.mkPos 1 n hn).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hnI : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
  exact Int.mul_le_mul_of_nonneg_right (by decide) hnI

/-- Constructive integral of `2/(1+x²)` on `[0,1]`, built from its left sums. -/
def atanIntegral : CReal where
  approx N := atanRiemannQ (N+1) (Nat.succ_pos N)
  cauchy := by
    intro ε hε
    refine ⟨2*ε.den, fun m n hm hn => ?_⟩
    have hmcut : Q'.mkPos 2 (m+1) (Nat.succ_pos m) ≤ ε := by
      apply two_over_succ_le hε
      omega
    have hncut : Q'.mkPos 2 (n+1) (Nat.succ_pos n) ≤ ε := by
      apply two_over_succ_le hε
      omega
    have hmone : Q'.mkPos 1 (m+1) (Nat.succ_pos m) ≤ ε :=
      Q'.le_trans' _ _ _ (one_over_le_two_over (m+1) (Nat.succ_pos m)) hmcut
    have hnone : Q'.mkPos 1 (n+1) (Nat.succ_pos n) ≤ ε :=
      Q'.le_trans' _ _ _ (one_over_le_two_over (n+1) (Nat.succ_pos n)) hncut
    constructor
    · exact Q'.le_trans' _ _ _
        (atanRiemannQ_le_other_add_one_over (m+1) (n+1)
          (Nat.succ_pos m) (Nat.succ_pos n))
        (Q'.add_le_add_left _ _ _ hmone)
    · exact Q'.le_trans' _ _ _
        (atanRiemannQ_le_other_add_one_over (n+1) (m+1)
          (Nat.succ_pos n) (Nat.succ_pos m))
        (Q'.add_le_add_left _ _ _ hnone)

theorem atanRiemannSeq_converges :
    CReal.ConvergesTo atanRiemannSeq atanIntegral :=
  CReal.convergesTo_self atanIntegral

theorem polygonSeq_converges :
    CReal.ConvergesTo polygonSeq atanIntegral :=
  polygonSeq_converges_of_atanRiemannSeq atanRiemannSeq_converges

end YMGap.Continuum.SemicircleAtanDarboux

#print axioms YMGap.Continuum.SemicircleAtanDarboux.refined_left_cell_le_share
#print axioms YMGap.Continuum.SemicircleAtanDarboux.finSum_coarseShare_eqv
#print axioms YMGap.Continuum.SemicircleAtanDarboux.coarseRightShare_le_refined_right_cell
#print axioms YMGap.Continuum.SemicircleAtanDarboux.finSum_coarseRightShare_eqv
#print axioms YMGap.Continuum.SemicircleAtanDarboux.refined_left_sum_le_coarse
#print axioms YMGap.Continuum.SemicircleAtanDarboux.coarse_right_sum_le_refined
#print axioms YMGap.Continuum.SemicircleAtanDarboux.rightRiemannQ_le_atanRiemannQ
#print axioms YMGap.Continuum.SemicircleAtanDarboux.atanRiemannQ_eqv_right_add_one_over
#print axioms YMGap.Continuum.SemicircleAtanDarboux.rightRiemannQ_le_atanRiemannQ_cross
#print axioms YMGap.Continuum.SemicircleAtanDarboux.atanRiemannQ_le_other_add_one_over
#print axioms YMGap.Continuum.SemicircleAtanDarboux.atanIntegral
#print axioms YMGap.Continuum.SemicircleAtanDarboux.atanRiemannSeq_converges
#print axioms YMGap.Continuum.SemicircleAtanDarboux.polygonSeq_converges
