/-
# A rational polygon/common-refinement bridge for the semicircle value

This successor to `SemicircleMachinBridgeBounds` supplies an exact geometric
sequence between the semicircle Riemann sums and the Machin/arctangent side.

For `0 <= j <= n`, the rational parametrisation

    x_j = (n^2-j^2)/(n^2+j^2),   y_j = 2nj/(n^2+j^2)

lies exactly on the unit circle.  The oriented cross product of consecutive
points is the exact doubled area of one inscribed polygon triangle:

    cross_j = 2n (n^2+j(j+1)) / (D_j D_(j+1)).

The left Riemann cell for `2/(1+t^2)` at `t=j/n` splits exactly as

    2n/D_j = cross_j + 2n(j+1)/(D_j D_(j+1)).

The final summand is nonnegative and the total defect over `j<n` is at most
`2/n`, proved as an exact rational inequality.  Exact finite bracketing follows,
and a genuine `CReal.ConvergesTo` transfer theorem proves that whenever the
arctangent-integrand Riemann sequence has a limit, the polygon sequence has the
same limit.  No new residual record is introduced; the remaining value step is
to identify that arctangent Riemann limit with the existing Machin `halfPi` and
to compare the polygon partition with `seqSemi`.

No decimal input, classical choice, new axiom, or unproved declaration is used.
-/

import YMGap.Continuum.SemicircleMachinBridgeBounds

namespace YMGap.Continuum.SemicircleRationalPolygon

open YMGap.Constructive

theorem sq_sub_add_four_mul (A B : Int) :
    (A-B)*(A-B) + (2*A)*(2*B) = (A+B)*(A+B) := by
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
  have hBA : B * A = A * B := Int.mul_comm B A
  have h4 : (2 * A) * (2 * B) = A * B + A * B + (A * B + A * B) := by
    have h2A : (2 : Int) * A = A + A := by
      show (1 + 1) * A = A + A
      rw [Int.add_mul, Int.one_mul]
    have h2B : (2 : Int) * B = B + B := by
      show (1 + 1) * B = B + B
      rw [Int.add_mul, Int.one_mul]
    simp only [h2A, h2B, Int.add_mul, Int.mul_add]
  rw [hBA, h4]
  omega

def cden (n j : Nat) : Nat := n*n + j*j

theorem cden_pos {n : Nat} (hn : 0 < n) (j : Nat) : 0 < cden n j := by
  unfold cden
  exact Nat.add_pos_left (Nat.mul_pos hn hn) _

def cx (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos ((n:Int)*(n:Int) - (j:Int)*(j:Int)) (cden n j) (cden_pos hn j)

def cy (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos (2*(n:Int)*(j:Int)) (cden n j) (cden_pos hn j)

theorem raw_pythagorean (n j : Nat) :
    (((n:Int)*(n:Int) - (j:Int)*(j:Int)) *
       ((n:Int)*(n:Int) - (j:Int)*(j:Int)))
      + (2*(n:Int)*(j:Int)) * (2*(n:Int)*(j:Int))
    = ((n:Int)*(n:Int) + (j:Int)*(j:Int)) *
      ((n:Int)*(n:Int) + (j:Int)*(j:Int)) := by
  have h := sq_sub_add_four_mul ((n:Int)*(n:Int)) ((j:Int)*(j:Int))
  have hy : (2*(n:Int)*(j:Int)) * (2*(n:Int)*(j:Int))
      = (2*((n:Int)*(n:Int))) * (2*((j:Int)*(j:Int))) := by ac_rfl
  rw [hy]
  exact h

theorem circle_point (n j : Nat) (hn : 0 < n) :
    (cx n j hn * cx n j hn + cy n j hn * cy n j hn).eqv (1 : Q') := by
  have hxnum : (cx n j hn).num = (n:Int)*(n:Int) - (j:Int)*(j:Int) := by
    unfold cx; exact Q'.mkPos_num _ _ _
  have hynum : (cy n j hn).num = 2*(n:Int)*(j:Int) := by
    unfold cy; exact Q'.mkPos_num _ _ _
  have hxden : ((cx n j hn).den : Int) = ((cden n j : Nat) : Int) := by
    unfold cx; rw [Q'.mkPos_den]
  have hyden : ((cy n j hn).den : Int) = ((cden n j : Nat) : Int) := by
    unfold cy; rw [Q'.mkPos_den]
  have hxxnum : (cx n j hn * cx n j hn).num =
      ((n:Int)*(n:Int) - (j:Int)*(j:Int)) * ((n:Int)*(n:Int) - (j:Int)*(j:Int)) := by
    show (cx n j hn).num * (cx n j hn).num = _
    rw [hxnum]
  have hyynum : (cy n j hn * cy n j hn).num =
      (2*(n:Int)*(j:Int)) * (2*(n:Int)*(j:Int)) := by
    show (cy n j hn).num * (cy n j hn).num = _
    rw [hynum]
  have hxxden : ((cx n j hn * cx n j hn).den : Int) =
      ((cden n j : Nat) : Int) * ((cden n j : Nat) : Int) := by
    rw [Q'.mul_den_cast, hxden]
  have hyyden : ((cy n j hn * cy n j hn).den : Int) =
      ((cden n j : Nat) : Int) * ((cden n j : Nat) : Int) := by
    rw [Q'.mul_den_cast, hyden]
  have hsumNum : (cx n j hn * cx n j hn + cy n j hn * cy n j hn).num =
      (((n:Int)*(n:Int) - (j:Int)*(j:Int)) * ((n:Int)*(n:Int) - (j:Int)*(j:Int))) *
        (((cden n j : Nat) : Int) * ((cden n j : Nat) : Int))
      + ((2*(n:Int)*(j:Int)) * (2*(n:Int)*(j:Int))) *
        (((cden n j : Nat) : Int) * ((cden n j : Nat) : Int)) := by
    show (cx n j hn * cx n j hn).num * ((cy n j hn * cy n j hn).den : Int)
      + (cy n j hn * cy n j hn).num * ((cx n j hn * cx n j hn).den : Int) = _
    rw [hxxnum, hyynum, hxxden, hyyden]
  have hsumDen : ((cx n j hn * cx n j hn + cy n j hn * cy n j hn).den : Int) =
      (((cden n j : Nat) : Int) * ((cden n j : Nat) : Int)) *
        (((cden n j : Nat) : Int) * ((cden n j : Nat) : Int)) := by
    rw [Q'.add_den_cast, hxxden, hyyden]
  show (cx n j hn * cx n j hn + cy n j hn * cy n j hn).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((cx n j hn * cx n j hn + cy n j hn * cy n j hn).den : Int)
  rw [hsumNum, hsumDen]
  rw [show ((1 : Q').den : Int) = 1 by decide, show (1 : Q').num = 1 by decide]
  rw [Int.mul_one, Int.one_mul]
  have hraw := raw_pythagorean n j
  have hdcast : ((cden n j : Nat) : Int) =
      (n:Int)*(n:Int) + (j:Int)*(j:Int) := by
    unfold cden
    push_cast
    rfl
  rw [hdcast]
  -- both addends have the common denominator square; cancel it after `hraw`.
  rw [← Int.add_mul]
  rw [hraw]

theorem raw_cross_next (n j : Int) :
    (n*n-j*j) * (2*n*(j+1)) - (2*n*j)*(n*n-(j+1)*(j+1))
      = 2*n*(n*n+j*(j+1)) := by
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]
  omega

def crossCell (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos
    (2*(n:Int)*((n:Int)*(n:Int) + (j:Int)*((j:Int)+1)))
    (cden n j * cden n (j+1))
    (Nat.mul_pos (cden_pos hn j) (cden_pos hn (j+1)))

def polygonCross (n j : Nat) (hn : 0 < n) : Q' :=
  cx n j hn * cy n (j+1) hn + -(cy n j hn * cx n (j+1) hn)

theorem cx_mul_cy_eqv (n j l : Nat) (hn : 0 < n) :
    (cx n j hn * cy n l hn).eqv
      (Q'.mkPos
        (((n:Int)*(n:Int) - (j:Int)*(j:Int)) * (2*(n:Int)*(l:Int)))
        (cden n j * cden n l)
        (Nat.mul_pos (cden_pos hn j) (cden_pos hn l))) := by
  have hnum : (cx n j hn * cy n l hn).num =
      ((n:Int)*(n:Int) - (j:Int)*(j:Int)) * (2*(n:Int)*(l:Int)) := by
    show (cx n j hn).num * (cy n l hn).num = _
    unfold cx cy
    rw [Q'.mkPos_num, Q'.mkPos_num]
  have hden : ((cx n j hn * cy n l hn).den : Int) =
      ((cden n j * cden n l : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    unfold cx cy
    rw [Q'.mkPos_den, Q'.mkPos_den]
    push_cast
    rfl
  show (cx n j hn * cy n l hn).num *
      ((Q'.mkPos _ (cden n j * cden n l) _).den : Int)
    = (Q'.mkPos _ (cden n j * cden n l) _).num *
      ((cx n j hn * cy n l hn).den : Int)
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]

theorem cy_mul_cx_eqv (n j l : Nat) (hn : 0 < n) :
    (cy n j hn * cx n l hn).eqv
      (Q'.mkPos
        ((2*(n:Int)*(j:Int)) * ((n:Int)*(n:Int) - (l:Int)*(l:Int)))
        (cden n j * cden n l)
        (Nat.mul_pos (cden_pos hn j) (cden_pos hn l))) := by
  have hnum : (cy n j hn * cx n l hn).num =
      (2*(n:Int)*(j:Int)) * ((n:Int)*(n:Int) - (l:Int)*(l:Int)) := by
    show (cy n j hn).num * (cx n l hn).num = _
    unfold cx cy
    rw [Q'.mkPos_num, Q'.mkPos_num]
  have hden : ((cy n j hn * cx n l hn).den : Int) =
      ((cden n j * cden n l : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    unfold cx cy
    rw [Q'.mkPos_den, Q'.mkPos_den]
    push_cast
    rfl
  show (cy n j hn * cx n l hn).num *
      ((Q'.mkPos _ (cden n j * cden n l) _).den : Int)
    = (Q'.mkPos _ (cden n j * cden n l) _).num *
      ((cy n j hn * cx n l hn).den : Int)
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]

theorem polygonCross_eqv_crossCell (n j : Nat) (hn : 0 < n) :
    (polygonCross n j hn).eqv (crossCell n j hn) := by
  let P := cden n j * cden n (j+1)
  have hP : 0 < P := Nat.mul_pos (cden_pos hn j) (cden_pos hn (j+1))
  let A : Int := ((n:Int)*(n:Int) - (j:Int)*(j:Int)) * (2*(n:Int)*((j:Int)+1))
  let B : Int := (2*(n:Int)*(j:Int)) *
    ((n:Int)*(n:Int) - ((j:Int)+1)*((j:Int)+1))
  have eA : (cx n j hn * cy n (j+1) hn).eqv (Q'.mkPos A P hP) := by
    unfold A P
    have e := cx_mul_cy_eqv n j (j+1) hn
    rw [show (((j+1 : Nat) : Int)) = (j:Int)+1 by omega] at e
    exact e
  have eB : (cy n j hn * cx n (j+1) hn).eqv (Q'.mkPos B P hP) := by
    unfold B P
    have e := cy_mul_cx_eqv n j (j+1) hn
    rw [show (((j+1 : Nat) : Int)) = (j:Int)+1 by omega] at e
    exact e
  have esum : (polygonCross n j hn).eqv
      (Q'.mkPos A P hP + Q'.mkPos (-B) P hP) := by
    unfold polygonCross
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ eA)
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ eB))
  have ecommon : (Q'.mkPos A P hP + Q'.mkPos (-B) P hP).eqv
      (Q'.mkPos (A + -B) P hP) :=
    SemicircleIntegral.mkPos_add_same_den A (-B) P hP
  refine Q'.eqv_trans _ _ _ esum (Q'.eqv_trans _ _ _ ecommon ?_)
  unfold crossCell A B P
  apply Q'.eqv_of_eq
  congr 1
  have hraw := raw_cross_next (n:Int) (j:Int)
  exact hraw

/-- Left-endpoint Riemann cell for `2/(1+t^2)` on `[0,1]`, `t=j/n`. -/
def atanCell (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos (2*(n:Int)) (cden n j) (cden_pos hn j)

/-- Exact sector-versus-chord defect. -/
def sectorDefect (n j : Nat) (hn : 0 < n) : Q' :=
  Q'.mkPos (2*(n:Int)*((j:Int)+1))
    (cden n j * cden n (j+1))
    (Nat.mul_pos (cden_pos hn j) (cden_pos hn (j+1)))

/-- Per-cell exact identity: chord cross + defect = arctangent Riemann cell. -/
theorem crossCell_add_defect_eqv_atanCell (n j : Nat) (hn : 0 < n) :
    (crossCell n j hn + sectorDefect n j hn).eqv (atanCell n j hn) := by
  let P := cden n j * cden n (j+1)
  have hP : 0 < P := Nat.mul_pos (cden_pos hn j) (cden_pos hn (j+1))
  let A : Int := 2*(n:Int)*((n:Int)*(n:Int) + (j:Int)*((j:Int)+1))
  let E : Int := 2*(n:Int)*((j:Int)+1)
  have esame : (crossCell n j hn + sectorDefect n j hn).eqv
      (Q'.mkPos (A + E) P hP) := by
    unfold crossCell sectorDefect A E P
    exact SemicircleIntegral.mkPos_add_same_den _ _ _ _
  refine Q'.eqv_trans _ _ _ esame ?_
  unfold atanCell A E P
  show (Q'.mkPos _ (cden n j * cden n (j+1)) _).num *
      ((Q'.mkPos (2*(n:Int)) (cden n j) _).den : Int)
    = (Q'.mkPos (2*(n:Int)) (cden n j) _).num *
      ((Q'.mkPos _ (cden n j * cden n (j+1)) _).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  unfold cden
  push_cast
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
    Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
  omega

theorem sectorDefect_nonneg (n j : Nat) (hn : 0 < n) :
    (0 : Q') ≤ sectorDefect n j hn := by
  unfold sectorDefect
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  exact Int.mul_nonneg
    (Int.mul_nonneg (by decide) (Int.natCast_nonneg n)) (by omega)

/-- Each defect is at most `2/n^2` for `j<n`. -/
theorem sectorDefect_le_two_over_sq (n j : Nat) (hn : 0 < n) (hj : j < n) :
    sectorDefect n j hn ≤ Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn) := by
  show (sectorDefect n j hn).num *
      ((Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).den : Int)
    ≤ (Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).num *
      ((sectorDefect n j hn).den : Int)
  unfold sectorDefect
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hjn : j + 1 ≤ n := hj
  have hjprod : n * (j+1) ≤ cden n j := by
    have h1 : n * (j+1) ≤ n*n := Nat.mul_le_mul_left n hjn
    exact Nat.le_trans h1 (Nat.le_add_right (n*n) (j*j))
  have hnnext : n*n ≤ cden n (j+1) := Nat.le_add_right (n*n) ((j+1)*(j+1))
  have hprod : (n*(j+1)) * (n*n) ≤ cden n j * cden n (j+1) :=
    Nat.mul_le_mul hjprod hnnext
  have hscaled : 2 * ((n*(j+1)) * (n*n)) ≤
      2 * (cden n j * cden n (j+1)) := Nat.mul_le_mul_left 2 hprod
  have hcast : (2 * ((n*(j+1)) * (n*n)) : Nat) ≤
      2 * (cden n j * cden n (j+1)) := hscaled
  have hcastI : ((2 * ((n*(j+1)) * (n*n)) : Nat) : Int) ≤
      ((2 * (cden n j * cden n (j+1)) : Nat) : Int) := by
    exact_mod_cast hcast
  push_cast at hcastI
  simpa only [Int.mul_assoc] using hcastI

def polygonSemiQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => crossCell n j hn) n

def atanRiemannQ (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => atanCell n j hn) n

def sectorDefectSum (n : Nat) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => sectorDefect n j hn) n

/-- Finite polygon/Riemann identity, exactly summed. -/
theorem polygon_add_defect_eqv_atanRiemann (n : Nat) (hn : 0 < n) :
    (polygonSemiQ n hn + sectorDefectSum n hn).eqv (atanRiemannQ n hn) := by
  unfold polygonSemiQ sectorDefectSum atanRiemannQ
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (RationalTail.finSum_add _ _ n)) ?_
  exact RationalTail.finSum_eqv_congr _ _
    (fun j => crossCell_add_defect_eqv_atanCell n j hn) n

/-- Quantified total sector/chord tail: at most `2/n`. -/
theorem sectorDefectSum_le_two_over_n (n : Nat) (hn : 0 < n) :
    sectorDefectSum n hn ≤ Q'.mkPos 2 n hn := by
  unfold sectorDefectSum
  have hterms : RationalTail.finSum (fun j => sectorDefect n j hn) n ≤
      RationalTail.finSum (fun _ => Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)) n := by
    have hprefix : ∀ m : Nat, m ≤ n →
        RationalTail.finSum (fun j => sectorDefect n j hn) m ≤
          RationalTail.finSum (fun _ => Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)) m := by
      intro m hm
      induction m with
      | zero => exact Q'.le_refl' 0
      | succ m ih =>
          rw [RationalTail.finSum_succ, RationalTail.finSum_succ]
          exact Q'.add_le_add (ih (Nat.le_trans (Nat.le_succ m) hm))
            (sectorDefect_le_two_over_sq n m hn (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))
    exact hprefix n (Nat.le_refl n)
  refine Q'.le_trans' _ _ _ hterms ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv
      (Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)) n) ?_)
  show (Q'.ofNat n * Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).eqv
    (Q'.mkPos 2 n hn)
  show (Q'.ofNat n * Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).num *
      ((Q'.mkPos 2 n hn).den : Int)
    = (Q'.mkPos 2 n hn).num *
      ((Q'.ofNat n * Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).den : Int)
  have hLnum : (Q'.ofNat n * Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).num =
      (n:Int) * 2 := by
    show (Q'.ofNat n).num * (Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).num = _
    rw [Q'.mkPos_num]
    rfl
  have hLden : ((Q'.ofNat n * Q'.mkPos 2 (n*n) (Nat.mul_pos hn hn)).den : Int) =
      ((n*n : Nat) : Int) := by
    rw [Q'.mul_den_cast, Q'.mkPos_den]
    change (1 : Int) * ((n*n : Nat) : Int) = ((n*n : Nat) : Int)
    rw [Int.one_mul]
  rw [hLnum, hLden, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  ac_rfl

theorem sectorDefectSum_nonneg (n : Nat) (hn : 0 < n) :
    (0 : Q') ≤ sectorDefectSum n hn := by
  unfold sectorDefectSum
  have hprefix : ∀ m : Nat,
      (0 : Q') ≤ RationalTail.finSum (fun j => sectorDefect n j hn) m := by
    intro m
    induction m with
    | zero => exact Q'.le_refl' 0
    | succ m ih =>
        rw [RationalTail.finSum_succ]
        exact Q'.zero_le_add _ _ ih (sectorDefect_nonneg n m hn)
  exact hprefix n

/-- Exact finite lower bracket: the inscribed polygon lies below the
arctangent left sum. -/
theorem polygonSemiQ_le_atanRiemannQ (n : Nat) (hn : 0 < n) :
    polygonSemiQ n hn ≤ atanRiemannQ n hn := by
  have hnonneg := sectorDefectSum_nonneg n hn
  have hadd : polygonSemiQ n hn ≤ polygonSemiQ n hn + sectorDefectSum n hn :=
    Q'.add_le_self_of_nonneg _ _ hnonneg
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (polygon_add_defect_eqv_atanRiemann n hn))

/-- Exact finite upper bracket, with the derived `2/n` tail. -/
theorem atanRiemannQ_le_polygon_add_two_over_n (n : Nat) (hn : 0 < n) :
    atanRiemannQ n hn ≤ polygonSemiQ n hn + Q'.mkPos 2 n hn := by
  have hback : atanRiemannQ n hn ≤ polygonSemiQ n hn + sectorDefectSum n hn :=
    Q'.ge_of_eqv (polygon_add_defect_eqv_atanRiemann n hn)
  have htail := sectorDefectSum_le_two_over_n n hn
  exact Q'.le_trans' _ _ _ hback
    (Q'.add_le_add_left _ _ _ htail)

def polygonSeq (N : Nat) : CReal :=
  CReal.ofQ' (polygonSemiQ (N+1) (Nat.succ_pos N))

def atanRiemannSeq (N : Nat) : CReal :=
  CReal.ofQ' (atanRiemannQ (N+1) (Nat.succ_pos N))

/-- Explicit cutoff for `2/(N+1) ≤ q`. -/
theorem two_over_succ_le {q : Q'} (hq : (0 : Q') < q) {N : Nat}
    (hN : 2 * q.den ≤ N + 1) :
    Q'.mkPos 2 (N+1) (Nat.succ_pos N) ≤ q := by
  show (2 : Int) * (q.den : Int) ≤ q.num * ((N+1 : Nat) : Int)
  have hqnum : (1 : Int) ≤ q.num := by
    have hp : (0 : Int) < q.num := Q'.num_pos_of_pos hq
    omega
  have hNI : (2 : Int) * (q.den : Int) ≤ ((N+1 : Nat) : Int) := by
    exact_mod_cast hN
  have hscale : ((N+1 : Nat) : Int) ≤ q.num * ((N+1 : Nat) : Int) := by
    have hn0 : (0 : Int) ≤ ((N+1 : Nat) : Int) := Int.natCast_nonneg _
    have := Int.mul_le_mul_of_nonneg_right hqnum hn0
    simpa only [Int.one_mul] using this
  exact Int.le_trans hNI hscale

/-- Genuine common-limit transfer.  The exact brackets and `2/(N+1)` cutoff
turn convergence of the arctangent Riemann sequence into convergence of the
inscribed-polygon sequence to the same `CReal`. -/
theorem polygonSeq_converges_of_atanRiemannSeq {L : CReal}
    (hconv : CReal.ConvergesTo atanRiemannSeq L) :
    CReal.ConvergesTo polygonSeq L := by
  intro ε hε
  let q : Q' := HalfPow.half * ε
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  obtain ⟨Natan, hNatan⟩ := hconv q hq
  let Ntail : Nat := 2 * q.den
  refine ⟨max Natan Ntail, fun N hN => ?_⟩
  have hNatN : Natan ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have htailN : Ntail ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨Napx, hclose⟩ := hNatan N hNatN
  refine ⟨Napx, fun k hk => ?_⟩
  have htailCut : Q'.mkPos 2 (N+1) (Nat.succ_pos N) ≤ q := by
    apply two_over_succ_le hq
    unfold Ntail at htailN
    omega
  have hlo := polygonSemiQ_le_atanRiemannQ (N+1) (Nat.succ_pos N)
  have hhi := atanRiemannQ_le_polygon_add_two_over_n (N+1) (Nat.succ_pos N)
  obtain ⟨hAtoL, hLtoA⟩ := hclose k hk
  change polygonSemiQ (N+1) (Nat.succ_pos N) ≤ L.approx k + ε ∧
    L.approx k ≤ polygonSemiQ (N+1) (Nat.succ_pos N) + ε
  have hqq : (q + q).eqv ε := ExpNeg.two_halves ε
  constructor
  · have hpq : polygonSemiQ (N+1) (Nat.succ_pos N) ≤ L.approx k + q :=
      Q'.le_trans' _ _ _ hlo hAtoL
    have hqeps : q ≤ ε := by
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hq)) (Q'.le_of_eqv hqq)
    exact Q'.le_trans' _ _ _ hpq (Q'.add_le_add_left _ _ _ hqeps)
  · have hApolyq : atanRiemannQ (N+1) (Nat.succ_pos N) ≤
        polygonSemiQ (N+1) (Nat.succ_pos N) + q :=
      Q'.le_trans' _ _ _ hhi (Q'.add_le_add_left _ _ _ htailCut)
    have hchain : L.approx k ≤
        (polygonSemiQ (N+1) (Nat.succ_pos N) + q) + q :=
      Q'.le_trans' _ _ _ hLtoA (Q'.add_le_add_right _ _ _ hApolyq)
    refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
    exact Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (polygonSemiQ (N+1) (Nat.succ_pos N)) q q)
      (Q'.add_eqv_congr_left _ _ _ hqq)

end YMGap.Continuum.SemicircleRationalPolygon

#print axioms YMGap.Continuum.SemicircleRationalPolygon.sq_sub_add_four_mul
#print axioms YMGap.Continuum.SemicircleRationalPolygon.raw_pythagorean
#print axioms YMGap.Continuum.SemicircleRationalPolygon.circle_point
#print axioms YMGap.Continuum.SemicircleRationalPolygon.raw_cross_next
#print axioms YMGap.Continuum.SemicircleRationalPolygon.polygonCross_eqv_crossCell
#print axioms YMGap.Continuum.SemicircleRationalPolygon.crossCell_add_defect_eqv_atanCell
#print axioms YMGap.Continuum.SemicircleRationalPolygon.sectorDefect_le_two_over_sq
#print axioms YMGap.Continuum.SemicircleRationalPolygon.polygon_add_defect_eqv_atanRiemann
#print axioms YMGap.Continuum.SemicircleRationalPolygon.sectorDefectSum_le_two_over_n
#print axioms YMGap.Continuum.SemicircleRationalPolygon.sectorDefectSum_nonneg
#print axioms YMGap.Continuum.SemicircleRationalPolygon.polygonSemiQ_le_atanRiemannQ
#print axioms YMGap.Continuum.SemicircleRationalPolygon.atanRiemannQ_le_polygon_add_two_over_n
#print axioms YMGap.Continuum.SemicircleRationalPolygon.two_over_succ_le
#print axioms YMGap.Continuum.SemicircleRationalPolygon.polygonSeq_converges_of_atanRiemannSeq
