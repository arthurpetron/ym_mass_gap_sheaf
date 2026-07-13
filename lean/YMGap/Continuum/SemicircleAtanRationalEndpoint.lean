/-
# Constructive atan integrals at arbitrary positive rational endpoints

This successor generalizes the exact Darboux engine from endpoint `1` to every
positive rational endpoint `A/B`.  Its left cells are

    2ABn / ((Bn)² + (Aj)²),  0 ≤ j < n,

the uniform left quadrature for `2/(1+x²)` on `[0,A/B]`.  The file proves:

* exact left/right multiplicative refinement through `P · Q`;
* the common-refinement bracket between arbitrary resolutions;
* a Darboux gap bounded by the exact first cell `2A/(Bn)`;
* an explicit constructive Cauchy modulus and the resulting
  `rationalAtanIntegral A B`;
* specialization at `A=B=1` is equivalent to the frozen `atanIntegral`.

This creates the actual integral objects at every rational slope in the
branch-safe Machin path.  It does not assume their change-of-variables or
power-series values; those are the next analytic lemmas.

All declarations are constructive and axiom-gated at EOF.  Dependencies are
contained in `{propext, Quot.sound}`; no `Classical.*`, `native_decide`, `sorry`,
custom axiom, or measured input occurs.
-/

import YMGap.Continuum.SemicircleAtanMachinPath

namespace YMGap.Continuum.SemicircleAtanRationalEndpoint

open YMGap.Constructive
open YMGap.Continuum.SemicircleValueRes
open YMGap.Continuum.SemicircleRationalPolygon
open YMGap.Continuum.SemicircleAtanDarboux

def scaledDen (A B n j : Nat) : Nat :=
  (B*n)*(B*n)+(A*j)*(A*j)

theorem scaledDen_pos {B n : Nat} (hB : 0 < B) (hn : 0 < n) (A j : Nat) :
    0 < scaledDen A B n j := by
  unfold scaledDen
  exact Nat.add_pos_left (Nat.mul_pos (Nat.mul_pos hB hn) (Nat.mul_pos hB hn)) _

def scaledCell (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  Q'.mkPos (2*(A:Int)*(B:Int)*(n:Int)) (scaledDen A B n j)
    (scaledDen_pos hB hn A j)

def scaledRightCell (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  scaledCell A B n (j+1) hB hn

def scaledLeftSum (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => scaledCell A B n j hB hn) n

def scaledRightSum (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => scaledRightCell A B n j hB hn) n

def scaledCoarseShare (A B P Q i : Nat)
    (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) : Q' :=
  Q'.mkPos (2*(A:Int)*(B:Int)*(P:Int)) (Q*scaledDen A B P i)
    (Nat.mul_pos hQ (scaledDen_pos hB hP A i))

theorem scaled_refined_left_cell_le_share
    (A B P Q i s : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    scaledCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ) ≤
      scaledCoarseShare A B P Q i hB hP hQ := by
  show (scaledCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ)).num *
      ((scaledCoarseShare A B P Q i hB hP hQ).den : Int) ≤
    (scaledCoarseShare A B P Q i hB hP hQ).num *
      ((scaledCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ)).den : Int)
  unfold scaledCell scaledCoarseShare
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hs0 : i*Q ≤ i*Q+s := Nat.le_add_right _ _
  have hAi : A*(i*Q) ≤ A*(i*Q+s) := Nat.mul_le_mul_left A hs0
  have hsq : (A*(i*Q))*(A*(i*Q)) ≤
      (A*(i*Q+s))*(A*(i*Q+s)) := Nat.mul_le_mul hAi hAi
  have hbase : Q*Q*scaledDen A B P i ≤ scaledDen A B (P*Q) (i*Q+s) := by
    unfold scaledDen
    have hBP : Q*Q*((B*P)*(B*P)) = (B*(P*Q))*(B*(P*Q)) := by ac_rfl
    have hAiQ : Q*Q*((A*i)*(A*i)) = (A*(i*Q))*(A*(i*Q)) := by ac_rfl
    rw [Nat.mul_add, hBP, hAiQ]
    exact Nat.add_le_add_left hsq _
  have hscaled :
      (2*A*B*(P*Q)) * (Q*scaledDen A B P i) ≤
      (2*A*B*P) * scaledDen A B (P*Q) (i*Q+s) := by
    have heL : (2*A*B*(P*Q)) * (Q*scaledDen A B P i) =
        (2*A*B*P) * (Q*Q*scaledDen A B P i) := by ac_rfl
    rw [heL]
    exact Nat.mul_le_mul_left (2*A*B*P) hbase
  have hI : (((2*A*B*(P*Q)) * (Q*scaledDen A B P i) : Nat) : Int) ≤
      (((2*A*B*P) * scaledDen A B (P*Q) (i*Q+s) : Nat) : Int) := by
    exact_mod_cast hscaled
  push_cast at hI ⊢
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hI

theorem scaled_finSum_coarseShare_eqv
    (A B P Q i : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (RationalTail.finSum (fun _ => scaledCoarseShare A B P Q i hB hP hQ) Q).eqv
      (scaledCell A B P i hB hP) := by
  refine Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv
      (scaledCoarseShare A B P Q i hB hP hQ) Q) ?_
  show (Q'.ofNat Q * scaledCoarseShare A B P Q i hB hP hQ).eqv
    (scaledCell A B P i hB hP)
  show (Q'.ofNat Q * scaledCoarseShare A B P Q i hB hP hQ).num *
      ((scaledCell A B P i hB hP).den : Int) =
    (scaledCell A B P i hB hP).num *
      ((Q'.ofNat Q * scaledCoarseShare A B P Q i hB hP hQ).den : Int)
  unfold scaledCoarseShare scaledCell
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  have hQnum : (Q'.ofNat Q).num = (Q : Int) := rfl
  have hQden : ((Q'.ofNat Q).den : Int) = 1 := rfl
  rw [hQnum, hQden, Int.one_mul]
  push_cast
  ac_rfl

theorem scaled_refined_left_sum_le_coarse
    (A B P Q : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    scaledLeftSum A B (P*Q) hB (Nat.mul_pos hP hQ) ≤
      scaledLeftSum A B P hB hP := by
  unfold scaledLeftSum
  have hblock := finSum_block
    (fun j => scaledCell A B (P*Q) j hB (Nat.mul_pos hP hQ)) Q P
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hblock) ?_
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro i
  refine Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _
      (fun s => scaled_refined_left_cell_le_share A B P Q i s hB hP hQ) Q) ?_
  exact Q'.le_of_eqv (scaled_finSum_coarseShare_eqv A B P Q i hB hP hQ)

def scaledCoarseRightShare (A B P Q i : Nat)
    (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) : Q' :=
  Q'.mkPos (2*(A:Int)*(B:Int)*(P:Int)) (Q*scaledDen A B P (i+1))
    (Nat.mul_pos hQ (scaledDen_pos hB hP A (i+1)))

theorem scaled_coarseRightShare_le_refined_right
    (A B P Q i s : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q)
    (hs : s < Q) :
    scaledCoarseRightShare A B P Q i hB hP hQ ≤
      scaledRightCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ) := by
  show (scaledCoarseRightShare A B P Q i hB hP hQ).num *
      ((scaledRightCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ)).den : Int) ≤
    (scaledRightCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ)).num *
      ((scaledCoarseRightShare A B P Q i hB hP hQ).den : Int)
  unfold scaledCoarseRightShare scaledRightCell scaledCell
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hidx : i*Q+s+1 ≤ (i+1)*Q := by
    rw [Nat.succ_mul]
    omega
  have hAi : A*(i*Q+s+1) ≤ A*((i+1)*Q) := Nat.mul_le_mul_left A hidx
  have hsq : (A*(i*Q+s+1))*(A*(i*Q+s+1)) ≤
      (A*((i+1)*Q))*(A*((i+1)*Q)) := Nat.mul_le_mul hAi hAi
  have hbase : scaledDen A B (P*Q) (i*Q+s+1) ≤
      Q*Q*scaledDen A B P (i+1) := by
    unfold scaledDen
    have hBP : (B*(P*Q))*(B*(P*Q)) = Q*Q*((B*P)*(B*P)) := by ac_rfl
    have hAiQ : (A*((i+1)*Q))*(A*((i+1)*Q)) =
        Q*Q*((A*(i+1))*(A*(i+1))) := by ac_rfl
    calc
      (B*(P*Q))*(B*(P*Q)) + (A*(i*Q+s+1))*(A*(i*Q+s+1))
          ≤ (B*(P*Q))*(B*(P*Q)) + (A*((i+1)*Q))*(A*((i+1)*Q)) :=
            Nat.add_le_add_left hsq _
      _ = Q*Q*((B*P)*(B*P) + (A*(i+1))*(A*(i+1))) := by
            rw [hBP, hAiQ]
            exact (Nat.mul_add (Q*Q) ((B*P)*(B*P))
              ((A*(i+1))*(A*(i+1)))).symm
  have hscaled :
      (2*A*B*P) * scaledDen A B (P*Q) (i*Q+s+1) ≤
      (2*A*B*(P*Q)) * (Q*scaledDen A B P (i+1)) := by
    have heR : (2*A*B*(P*Q)) * (Q*scaledDen A B P (i+1)) =
        (2*A*B*P) * (Q*Q*scaledDen A B P (i+1)) := by ac_rfl
    rw [heR]
    exact Nat.mul_le_mul_left (2*A*B*P) hbase
  have hI : (((2*A*B*P) * scaledDen A B (P*Q) (i*Q+s+1) : Nat) : Int) ≤
      (((2*A*B*(P*Q)) * (Q*scaledDen A B P (i+1)) : Nat) : Int) := by
    exact_mod_cast hscaled
  push_cast at hI ⊢
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hI

theorem scaled_finSum_coarseRightShare_eqv
    (A B P Q i : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (RationalTail.finSum
      (fun _ => scaledCoarseRightShare A B P Q i hB hP hQ) Q).eqv
      (scaledRightCell A B P i hB hP) := by
  refine Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv
      (scaledCoarseRightShare A B P Q i hB hP hQ) Q) ?_
  show (Q'.ofNat Q * scaledCoarseRightShare A B P Q i hB hP hQ).eqv
    (scaledCell A B P (i+1) hB hP)
  show (Q'.ofNat Q * scaledCoarseRightShare A B P Q i hB hP hQ).num *
      ((scaledCell A B P (i+1) hB hP).den : Int) =
    (scaledCell A B P (i+1) hB hP).num *
      ((Q'.ofNat Q * scaledCoarseRightShare A B P Q i hB hP hQ).den : Int)
  unfold scaledCoarseRightShare scaledCell
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  have hQnum : (Q'.ofNat Q).num = (Q : Int) := rfl
  have hQden : ((Q'.ofNat Q).den : Int) = 1 := rfl
  rw [hQnum, hQden, Int.one_mul]
  push_cast
  ac_rfl

theorem scaled_coarse_right_sum_le_refined
    (A B P Q : Nat) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    scaledRightSum A B P hB hP ≤
      scaledRightSum A B (P*Q) hB (Nat.mul_pos hP hQ) := by
  unfold scaledRightSum
  have hblock := finSum_block
    (fun j => scaledRightCell A B (P*Q) j hB (Nat.mul_pos hP hQ)) Q P
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hblock)
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro i
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (scaled_finSum_coarseRightShare_eqv A B P Q i hB hP hQ)) ?_
  have hprefix : ∀ m : Nat, m ≤ Q →
      RationalTail.finSum
        (fun _ => scaledCoarseRightShare A B P Q i hB hP hQ) m ≤
      RationalTail.finSum
        (fun s => scaledRightCell A B (P*Q) (i*Q+s) hB (Nat.mul_pos hP hQ)) m := by
    intro m hm
    induction m with
    | zero => exact Q'.le_refl' 0
    | succ m ih =>
        rw [RationalTail.finSum_succ, RationalTail.finSum_succ]
        exact Q'.add_le_add (ih (Nat.le_trans (Nat.le_succ m) hm))
          (scaled_coarseRightShare_le_refined_right A B P Q i m hB hP hQ
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))
  exact hprefix Q (Nat.le_refl Q)

theorem scaledCell_nonneg (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) :
    (0 : Q') ≤ scaledCell A B n j hB hn := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold scaledCell
  rw [Q'.mkPos_num]
  exact Int.mul_nonneg
    (Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg A)) (Int.natCast_nonneg B))
    (Int.natCast_nonneg n)

theorem scaledRightCell_le_scaledCell
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) :
    scaledRightCell A B n j hB hn ≤ scaledCell A B n j hB hn := by
  show (scaledRightCell A B n j hB hn).num *
      ((scaledCell A B n j hB hn).den : Int) ≤
    (scaledCell A B n j hB hn).num *
      ((scaledRightCell A B n j hB hn).den : Int)
  unfold scaledRightCell scaledCell
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hj : j ≤ j+1 := Nat.le_succ j
  have hAj : A*j ≤ A*(j+1) := Nat.mul_le_mul_left A hj
  have hsq : (A*j)*(A*j) ≤ (A*(j+1))*(A*(j+1)) := Nat.mul_le_mul hAj hAj
  have hd : scaledDen A B n j ≤ scaledDen A B n (j+1) :=
    Nat.add_le_add_left hsq _
  have hscale : (2*A*B*n)*scaledDen A B n j ≤
      (2*A*B*n)*scaledDen A B n (j+1) := Nat.mul_le_mul_left _ hd
  exact_mod_cast hscale

theorem scaledRightSum_le_scaledLeftSum
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    scaledRightSum A B n hB hn ≤ scaledLeftSum A B n hB hn := by
  unfold scaledRightSum scaledLeftSum
  exact ExpNeg.finSum_le_finSum_of_termwise _ _
    (fun j => scaledRightCell_le_scaledCell A B n j hB hn) n

def scaledMesh (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  Q'.mkPos (2*(A:Int)) (B*n) (Nat.mul_pos hB hn)

theorem scaledCell_zero_eqv_mesh
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (scaledCell A B n 0 hB hn).eqv (scaledMesh A B n hB hn) := by
  show (scaledCell A B n 0 hB hn).num *
      ((scaledMesh A B n hB hn).den : Int) =
    (scaledMesh A B n hB hn).num *
      ((scaledCell A B n 0 hB hn).den : Int)
  unfold scaledCell scaledMesh scaledDen
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  simp only [Int.mul_zero, Int.add_zero]
  ac_rfl

/-- The Darboux gap is bounded by the first cell, i.e. by the endpoint mesh
`2A/(Bn)`. -/
theorem scaledLeftSum_le_right_add_mesh
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    scaledLeftSum A B n hB hn ≤
      scaledRightSum A B n hB hn + scaledMesh A B n hB hn := by
  let g : RationalTail.QSeq := fun j => scaledCell A B n j hB hn
  have hpeel := RationalTail.finSum_peel_left g n
  have hbase : (scaledLeftSum A B n hB hn + scaledCell A B n n hB hn).eqv
      (scaledCell A B n 0 hB hn + scaledRightSum A B n hB hn) := by
    unfold scaledLeftSum scaledRightSum scaledRightCell
    change (RationalTail.finSum g n + g n).eqv
      (g 0 + RationalTail.finSum (fun i => g (i+1)) n)
    rw [← RationalTail.finSum_succ]
    exact hpeel
  have hnonneg := scaledCell_nonneg A B n n hB hn
  have hfront : scaledLeftSum A B n hB hn ≤
      scaledLeftSum A B n hB hn + scaledCell A B n n hB hn :=
    Q'.add_le_self_of_nonneg _ _ hnonneg
  have hto : scaledLeftSum A B n hB hn + scaledCell A B n n hB hn ≤
      scaledCell A B n 0 hB hn + scaledRightSum A B n hB hn :=
    Q'.le_of_eqv hbase
  refine Q'.le_trans' _ _ _ hfront (Q'.le_trans' _ _ _ hto ?_)
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (scaledCell A B n 0 hB hn) (scaledRightSum A B n hB hn)) ?_)
  exact Q'.add_eqv_congr_left (scaledRightSum A B n hB hn) _ _
    (scaledCell_zero_eqv_mesh A B n hB hn)

theorem scaledRightSum_le_scaledLeftSum_cross
    (A B m n : Nat) (hB : 0 < B) (hm : 0 < m) (hn : 0 < n) :
    scaledRightSum A B m hB hm ≤ scaledLeftSum A B n hB hn := by
  have h1 := scaled_coarse_right_sum_le_refined A B m n hB hm hn
  have h2 := scaledRightSum_le_scaledLeftSum A B (m*n) hB (Nat.mul_pos hm hn)
  have h3 := scaled_refined_left_sum_le_coarse A B n m hB hn hm
  have h3' : scaledLeftSum A B (m*n) hB (Nat.mul_pos hm hn) ≤
      scaledLeftSum A B n hB hn := by
    simpa only [Nat.mul_comm m n] using h3
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3')

theorem scaledLeftSum_le_other_add_mesh
    (A B m n : Nat) (hB : 0 < B) (hm : 0 < m) (hn : 0 < n) :
    scaledLeftSum A B m hB hm ≤
      scaledLeftSum A B n hB hn + scaledMesh A B m hB hm := by
  have hgap := scaledLeftSum_le_right_add_mesh A B m hB hm
  have hcross := scaledRightSum_le_scaledLeftSum_cross A B m n hB hm hn
  exact Q'.le_trans' _ _ _ hgap
    (Q'.add_le_add_right _ _ _ hcross)

theorem scaledMesh_succ_le {q : Q'} (hq : (0 : Q') < q)
    (A B N : Nat) (hB : 0 < B)
    (hN : 2*A*q.den ≤ B*(N+1)) :
    scaledMesh A B (N+1) hB (Nat.succ_pos N) ≤ q := by
  unfold scaledMesh
  show (Q'.mkPos (2*(A:Int)) (B*(N+1))
      (Nat.mul_pos hB (Nat.succ_pos N))).num * (q.den : Int) ≤
    q.num * ((Q'.mkPos (2*(A:Int)) (B*(N+1))
      (Nat.mul_pos hB (Nat.succ_pos N))).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hNI : (2*(A:Int)) * (q.den : Int) ≤ ((B*(N+1) : Nat) : Int) := by
    exact_mod_cast hN
  have hqnum : (1 : Int) ≤ q.num := by
    have hp := Q'.num_pos_of_pos hq
    omega
  have hscale : ((B*(N+1) : Nat) : Int) ≤
      q.num * ((B*(N+1) : Nat) : Int) := by
    have hnon : (0 : Int) ≤ ((B*(N+1) : Nat) : Int) := Int.natCast_nonneg _
    have := Int.mul_le_mul_of_nonneg_right hqnum hnon
    simpa only [Int.one_mul] using this
  exact Int.le_trans hNI hscale

/-- The constructive integral of `2/(1+x²)` from `0` to the positive rational
endpoint `A/B`, represented by exact uniform left sums. -/
def rationalAtanIntegral (A B : Nat) (hB : 0 < B) : CReal where
  approx N := scaledLeftSum A B (N+1) hB (Nat.succ_pos N)
  cauchy := by
    intro ε hε
    refine ⟨2*A*ε.den, fun m n hm hn => ?_⟩
    have hmNat : 2*A*ε.den ≤ B*(m+1) := by
      calc
        2*A*ε.den ≤ m := hm
        _ ≤ m+1 := Nat.le_succ m
        _ = 1*(m+1) := (Nat.one_mul _).symm
        _ ≤ B*(m+1) := Nat.mul_le_mul_right (m+1) hB
    have hnNat : 2*A*ε.den ≤ B*(n+1) := by
      calc
        2*A*ε.den ≤ n := hn
        _ ≤ n+1 := Nat.le_succ n
        _ = 1*(n+1) := (Nat.one_mul _).symm
        _ ≤ B*(n+1) := Nat.mul_le_mul_right (n+1) hB
    have hmMesh : scaledMesh A B (m+1) hB (Nat.succ_pos m) ≤ ε :=
      scaledMesh_succ_le hε A B m hB hmNat
    have hnMesh : scaledMesh A B (n+1) hB (Nat.succ_pos n) ≤ ε :=
      scaledMesh_succ_le hε A B n hB hnNat
    constructor
    · exact Q'.le_trans' _ _ _
        (scaledLeftSum_le_other_add_mesh A B (m+1) (n+1) hB
          (Nat.succ_pos m) (Nat.succ_pos n))
        (Q'.add_le_add_left _ _ _ hmMesh)
    · exact Q'.le_trans' _ _ _
        (scaledLeftSum_le_other_add_mesh A B (n+1) (m+1) hB
          (Nat.succ_pos n) (Nat.succ_pos m))
        (Q'.add_le_add_left _ _ _ hnMesh)

def rationalAtanSeq (A B : Nat) (hB : 0 < B) (N : Nat) : CReal :=
  CReal.ofQ' (scaledLeftSum A B (N+1) hB (Nat.succ_pos N))

theorem rationalAtanSeq_converges (A B : Nat) (hB : 0 < B) :
    CReal.ConvergesTo (rationalAtanSeq A B hB)
      (rationalAtanIntegral A B hB) :=
  CReal.convergesTo_self (rationalAtanIntegral A B hB)

theorem scaledCell_one_one_eqv_atanCell (n j : Nat) (hn : 0 < n) :
    (scaledCell 1 1 n j (by decide) hn).eqv (atanCell n j hn) := by
  show (scaledCell 1 1 n j (by decide) hn).num * ((atanCell n j hn).den : Int) =
    (atanCell n j hn).num * ((scaledCell 1 1 n j (by decide) hn).den : Int)
  unfold scaledCell scaledDen atanCell cden
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  simp only [Int.one_mul]

theorem scaledLeftSum_one_one_eqv_atanRiemann (n : Nat) (hn : 0 < n) :
    (scaledLeftSum 1 1 n (by decide) hn).eqv (atanRiemannQ n hn) := by
  unfold scaledLeftSum atanRiemannQ
  exact RationalTail.finSum_eqv_congr _ _
    (fun j => scaledCell_one_one_eqv_atanCell n j hn) n

theorem rationalAtanSeq_one_one_term (N : Nat) :
    CReal.Equiv (rationalAtanSeq 1 1 (by decide) N) (atanRiemannSeq N) := by
  intro ε hε
  refine ⟨0, fun _ _ => ?_⟩
  change scaledLeftSum 1 1 (N+1) (by decide) (Nat.succ_pos N) ≤
      atanRiemannQ (N+1) (Nat.succ_pos N) + ε ∧
    atanRiemannQ (N+1) (Nat.succ_pos N) ≤
      scaledLeftSum 1 1 (N+1) (by decide) (Nat.succ_pos N) + ε
  have he := scaledLeftSum_one_one_eqv_atanRiemann (N+1) (Nat.succ_pos N)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε))⟩

/-- The generic rational-endpoint construction specializes at `1/1` to the
previous Darboux integral `atanIntegral`. -/
theorem rationalAtanIntegral_one_one_eqv :
    CReal.Equiv (rationalAtanIntegral 1 1 (by decide)) atanIntegral :=
  CReal.Equiv_of_limit_of_equal
    rationalAtanSeq_one_one_term
    (rationalAtanSeq_converges 1 1 (by decide))
    atanRiemannSeq_converges

end YMGap.Continuum.SemicircleAtanRationalEndpoint

#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_refined_left_cell_le_share
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_finSum_coarseShare_eqv
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_refined_left_sum_le_coarse
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_coarseRightShare_le_refined_right
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_finSum_coarseRightShare_eqv
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaled_coarse_right_sum_le_refined
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaledLeftSum_le_right_add_mesh
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaledRightSum_le_scaledLeftSum_cross
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.scaledMesh_succ_le
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.rationalAtanIntegral
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.rationalAtanSeq_converges
#print axioms YMGap.Continuum.SemicircleAtanRationalEndpoint.rationalAtanIntegral_one_one_eqv
