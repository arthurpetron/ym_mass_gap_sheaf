/-
# Coordinate realization on the actual quaternion point completion

Four supplied constructive-real coordinates with explicit inner rates and
semantic squared norm one produce an actual rational-unit Cauchy row.
The only sign choices are decidable choices on rational approximations.
The semantic norm witness is used inside proofs, never to select a cutoff.

Conversely every supplied point row has four coordinate reals with explicit
rates. Coordinates descend to RC on the existing Point quotient; no CReal
representative of an arbitrary quotient point is chosen. Recovery is semantic.
This is not compactness, a matrix SU(2) identification, or a Haar extension.
-/

import YMGap.RepTheory.RationalQuaternionNormRepair
import YMGap.RepTheory.RationalQuaternionCompletedDistance
import YMGap.Constructive.CRealExp

namespace YMGap.RepTheory.RationalQuaternionCoordinateCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)
private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)
private theorem sq_nonnegative (a : Q') : (0:Q') ≤ a*a :=
  SumOfSquares.q_mul_self_nonneg a
private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => a)

private theorem square_le_of_abs_le {a e : Q'} (he : (0:Q') ≤ e)
    (ha : Q'.abs a ≤ e) : a*a ≤ e*e :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (abs_square a))
    (Q'.mul_le_mul_of_nonneg ha ha he (Q'.abs_nonneg a))

private theorem abs_le_of_square_le {a e : Q'} (he : (0:Q') < e)
    (h : a*a ≤ e*e) : Q'.abs a ≤ e :=
  CReal.le_of_sq_le_sq he (Q'.abs_nonneg a)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square a)) h)

private theorem le_add_of_sub {a b e : Q'} (h : a + -b ≤ e) : a ≤ b+e := by
  have ht := Q'.add_le_add_left b (a + -b) e h
  have hi : b+(a + -b) ≈ a := poly_identity_of_normal_eq
    (.var 1+(.var 0 + -(.var 1))) (.var 0) (by decide) (fun | 0 => a | _ => b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hi) ht

private theorem bounds_of_abs_sub {a b e : Q'} (h : Q'.abs (a + -b) ≤ e) :
    a ≤ b+e ∧ b ≤ a+e := by
  have hi : b + -a ≈ -(a + -b) := poly_identity_of_normal_eq
    (.var 1 + -(.var 0)) (- (.var 0 + -(.var 1))) (by decide) (fun | 0 => a | _ => b)
  exact ⟨le_add_of_sub (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h),
    le_add_of_sub (Q'.le_trans' _ _ _ (Q'.le_of_eqv hi)
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) h))⟩

private theorem constant_le_reflect {a b : Q'} (h : leEv (ofQ' a) (ofQ' b)) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  obtain ⟨M,hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
  have ht : a ≤ b+Q'.invSucc N := hM M (Nat.le_refl M)
  have he : b+Q'.ofNat 1*Q'.invSucc N ≈ b+Q'.invSucc N :=
    ac (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (show Q'.ofNat 1 ≈ (1:Q') by decide) (Q'.eqv_refl _)) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv he)

private theorem pointwise_equiv {a b : CReal} (h : ∀ n, a.approx n ≈ b.approx n) :
    Equiv a b := by
  intro e he
  refine ⟨0,fun n _ => ⟨?_,?_⟩⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n)) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (h n)) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-- The supplied coordinates, with their literal rational approximations. -/
def rawRow (x : Fin 4 → CReal) (n : Nat) : RationalQuaternion :=
  ⟨(x 0).approx n,(x 1).approx n,(x 2).approx n,(x 3).approx n⟩

theorem coordinate_rawRow (x : Fin 4 → CReal) (n : Nat) (j : Fin 4) :
    coordinate (rawRow x n) j = (x j).approx n := by
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero => rfl
    | succ j => cases j with
      | zero => rfl
      | succ j => cases j with
        | zero => rfl
        | succ j => omega

def coordinateNorm (x : Fin 4 → CReal) : CReal :=
  CReal.add (CReal.add (CReal.mul (x 0) (x 0)) (CReal.mul (x 1) (x 1)))
    (CReal.add (CReal.mul (x 2) (x 2)) (CReal.mul (x 3) (x 3)))

theorem coordinateNorm_approx (x : Fin 4 → CReal) (n : Nat) :
    (coordinateNorm x).approx n = normSq (rawRow x n) := rfl

def commonRate {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j)) (e : Q') : Nat :=
  max (max ((R 0).rate e) ((R 1).rate e)) (max ((R 2).rate e) ((R 3).rate e))

theorem coordinate_rate_le {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (e : Q') (j : Fin 4) : (R j).rate e ≤ commonRate R e := by
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  | succ j => cases j with
    | zero => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    | succ j => cases j with
      | zero => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      | succ j => cases j with
        | zero => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        | succ j => omega

private theorem common_regular {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    {e : Q'} (he : (0:Q') < e) {p q : Nat} (hp : commonRate R e ≤ p)
    (hq : commonRate R e ≤ q) (j : Fin 4) :
    Q'.abs ((x j).approx p + -(x j).approx q) ≤ e := by
  have h := (R j).regular e he p q
    (Nat.le_trans (coordinate_rate_le R e j) hp)
    (Nat.le_trans (coordinate_rate_le R e j) hq)
  exact CReal.abs_sub_le_of_bounds h.1 h.2

/-- A computable bootstrap index; it contains no semantic norm-zero witness. -/
def bootstrap {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j)) : Nat :=
  commonRate R HalfPow.half

theorem coordinate_tail_bound {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (n : Nat) (hn : bootstrap R ≤ n)
    (j : Fin 4) : Q'.abs ((x j).approx n) ≤ (2:Q') := by
  obtain ⟨M,hM⟩ := hx 1 (by decide)
  let q := max M (bootstrap R)
  have hnorm : normSq (rawRow x q) ≤ (2:Q') := Q'.le_trans' _ _ _
    (hM q (Nat.le_max_left _ _)).1 (by decide : (1:Q')+1 ≤ 2)
  have hsq : (x j).approx q*(x j).approx q ≤ (2:Q') := by
    have h := coordinate_square_le (rawRow x q) j
    rw [coordinate_rawRow] at h
    exact Q'.le_trans' _ _ _ h hnorm
  have habs : Q'.abs ((x j).approx q) ≤ Q'.mkPos 3 2 (by decide) :=
    abs_le_of_square_le (by decide)
      (Q'.le_trans' _ _ _ hsq (by decide : (2:Q') ≤
        Q'.mkPos 3 2 (by decide)*Q'.mkPos 3 2 (by decide)))
  have hdiff := common_regular R (e := HalfPow.half) (by decide) hn
    (Nat.le_max_right M (bootstrap R)) j
  exact Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub ((x j).approx n) ((x j).approx q))
    (Q'.le_trans' _ _ _ (Q'.add_le_add habs hdiff) (by decide))

private theorem square_difference_bound {a b d : Q'} (ha : Q'.abs a ≤ (2:Q'))
    (hb : Q'.abs b ≤ (2:Q')) (hd : Q'.abs (a + -b) ≤ d) :
    Q'.abs (a*a + -(b*b)) ≤ 4*d := by
  have hi : a*a + -(b*b) ≈ (a + -b)*(a+b) := poly_identity_of_normal_eq
    (.var 0*.var 0 + -(.var 1*.var 1)) ((.var 0 + -(.var 1))*(.var 0+.var 1))
    (by decide) (fun | 0 => a | _ => b)
  have hs : Q'.abs (a+b) ≤ (4:Q') := Q'.le_trans' _ _ _ (Q'.abs_add_le' a b)
    (Q'.le_trans' _ _ _ (Q'.add_le_add ha hb) (by decide))
  have hd0 : (0:Q') ≤ d := Q'.le_trans' _ _ _ (Q'.abs_nonneg _) hd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hi))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg hd hs hd0 (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.mul_comm_eqv d 4))))

private theorem four_difference_identity (a b c d e f g h : Q') :
    ((a+b)+(c+d))+ -((e+f)+(g+h)) ≈
      ((a + -e)+(b + -f))+((c + -g)+(d + -h)) :=
  poly_identity_of_normal_eq
    (((.var 0+.var 1)+(.var 2+.var 3))+ -((.var 4+.var 5)+(.var 6+.var 7)))
    (((.var 0 + -(.var 4))+(.var 1 + -(.var 5)))+
      ((.var 2 + -(.var 6))+(.var 3 + -(.var 7)))) (by decide)
    (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h)

private theorem abs_four_add_le (a b c d : Q') :
    Q'.abs ((a+b)+(c+d)) ≤ (Q'.abs a+Q'.abs b)+(Q'.abs c+Q'.abs d) :=
  Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
    (Q'.add_le_add (Q'.abs_add_le' _ _) (Q'.abs_add_le' _ _))

private theorem four_scaled_sum (d : Q') :
    (4*d+4*d)+(4*d+4*d) ≈ 16*d := by
  have h8 : 4*d+4*d ≈ 8*d := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv 4 4 d))
    (mc (by decide : (4:Q')+4 ≈ 8) (Q'.eqv_refl d))
  have h16 : 8*d+8*d ≈ 16*d := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv 8 8 d))
    (mc (by decide : (8:Q')+8 ≈ 16) (Q'.eqv_refl d))
  exact Q'.eqv_trans _ _ _ (ac h8 h8) h16

private theorem norm_difference_bound (a b : RationalQuaternion) (d : Q')
    (ha : ∀ j, Q'.abs (coordinate a j) ≤ (2:Q'))
    (hb : ∀ j, Q'.abs (coordinate b j) ≤ (2:Q'))
    (hd : ∀ j, Q'.abs (coordinate a j + -coordinate b j) ≤ d) :
    Q'.abs (normSq a + -normSq b) ≤ 16*d := by
  have hi : normSq a + -normSq b ≈
      ((a.r*a.r + -(b.r*b.r))+(a.i*a.i + -(b.i*b.i)))+
        ((a.j*a.j + -(b.j*b.j))+(a.k*a.k + -(b.k*b.k))) :=
    four_difference_identity (a.r*a.r) (a.i*a.i) (a.j*a.j) (a.k*a.k)
      (b.r*b.r) (b.i*b.i) (b.j*b.j) (b.k*b.k)
  have hsum := Q'.add_le_add
    (Q'.add_le_add (square_difference_bound (ha 0) (hb 0) (hd 0))
      (square_difference_bound (ha 1) (hb 1) (hd 1)))
    (Q'.add_le_add (square_difference_bound (ha 2) (hb 2) (hd 2))
      (square_difference_bound (ha 3) (hb 3) (hd 3)))
  have habs : Q'.abs
      (((a.r*a.r + -(b.r*b.r))+(a.i*a.i + -(b.i*b.i)))+
        ((a.j*a.j + -(b.j*b.j))+(a.k*a.k + -(b.k*b.k)))) ≤
      (Q'.abs (a.r*a.r + -(b.r*b.r))+Q'.abs (a.i*a.i + -(b.i*b.i)))+
        (Q'.abs (a.j*a.j + -(b.j*b.j))+Q'.abs (a.k*a.k + -(b.k*b.k))) :=
    abs_four_add_le _ _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hi))
    (Q'.le_trans' _ _ _ habs (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (four_scaled_sum d))))

private def sixteenth : Q' := Q'.mkPos 1 16 (by decide)
private theorem sixteen_sixteenth (e : Q') : 16*(sixteenth*e) ≈ e :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 16 sixteenth e))
    (Q'.eqv_trans _ _ _ (mc (by decide : (16:Q')*sixteenth ≈ 1) (Q'.eqv_refl _))
      (Q'.one_mul_eqv _))

def normRate {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j)) (e : Q') : Nat :=
  max (bootstrap R) (commonRate R (sixteenth*e))

/-- Norm regularity is constructed from the supplied coordinate rates.
The norm-one hypothesis supplies only a proved tail bound, not a new rate. -/
def normRegularity {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) : InnerRegularity (coordinateNorm x) where
  rate := normRate R
  regular := by
    intro e he p q hp hq
    have hd : (0:Q') < sixteenth*e := Q'.mul_pos (by decide) he
    apply bounds_of_abs_sub
    have hpBound : ∀ j, Q'.abs (coordinate (rawRow x p) j) ≤ (2:Q') := by
      intro j
      rw [coordinate_rawRow]
      exact coordinate_tail_bound R hx p (Nat.le_trans (Nat.le_max_left _ _) hp) j
    have hqBound : ∀ j, Q'.abs (coordinate (rawRow x q) j) ≤ (2:Q') := by
      intro j
      rw [coordinate_rawRow]
      exact coordinate_tail_bound R hx q (Nat.le_trans (Nat.le_max_left _ _) hq) j
    have hdiff : ∀ j,
        Q'.abs (coordinate (rawRow x p) j + -coordinate (rawRow x q) j) ≤ sixteenth*e := by
      intro j
      rw [coordinate_rawRow,coordinate_rawRow]
      exact common_regular R hd (Nat.le_trans (Nat.le_max_right _ _) hp)
        (Nat.le_trans (Nat.le_max_right _ _) hq) j
    have h := norm_difference_bound (rawRow x p) (rawRow x q) (sixteenth*e)
      hpBound hqBound hdiff
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (sixteen_sixteenth e))

def residualRate {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j)) (e : Q') : Nat :=
  normRate R (HalfPow.half*e)

theorem norm_residual_bound {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (e : Q') (he : (0:Q') < e)
    (n : Nat) (hn : residualRate R e ≤ n) :
    Q'.abs (normSq (rawRow x n) + -(1:Q')) ≤ e := by
  have hh := ExpNeg.half_mul_pos e he
  obtain ⟨M,hM⟩ := hx (HalfPow.half*e) hh
  let q := max M (normRate R (HalfPow.half*e))
  have hq := CReal.abs_sub_le_of_bounds (hM q (Nat.le_max_left _ _)).1
    (hM q (Nat.le_max_left _ _)).2
  have hr := (normRegularity R hx).regular (HalfPow.half*e) hh n q hn (Nat.le_max_right _ _)
  have hd := CReal.abs_sub_le_of_bounds hr.1 hr.2
  have hi : normSq (rawRow x n) + -(1:Q') ≈
      (normSq (rawRow x n) + -normSq (rawRow x q))+
        (normSq (rawRow x q) + -(1:Q')) :=
    poly_identity_of_normal_eq (.var 0 + -1) ((.var 0 + -(.var 1))+(.var 1 + -1))
      (by decide) (fun | 0 => normSq (rawRow x n) | _ => normSq (rawRow x q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hi))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hd hq) (Q'.le_of_eqv (ExpNeg.two_halves e))))

private def eighth : Q' := Q'.mkPos 1 8 (by decide)
/-- A positive computable coordinate tolerance for squared chord error. -/
def repairTolerance (e : Q') : Q' := eighth*Q'.min' 1 e

theorem repairTolerance_positive {e : Q'} (he : (0:Q') < e) : (0:Q') < repairTolerance e := by
  apply Q'.mul_pos (by decide)
  unfold Q'.min'
  split
  · decide
  · exact he

private theorem repairTolerance_budget {e : Q'} (he : (0:Q') < e) :
    22*(repairTolerance e*repairTolerance e) ≤ e := by
  let u := Q'.min' 1 e
  have hu0 : (0:Q') ≤ u := by
    unfold u Q'.min'
    split
    · decide
    · exact Q'.le_of_lt he
  have hu1 : u ≤ (1:Q') := by
    unfold u Q'.min'
    split
    · exact Q'.le_refl' _
    · exact Int.le_of_lt (Int.not_le.mp ‹¬ (1:Q') ≤ e›)
  have hue : u ≤ e := by
    unfold u Q'.min'
    split
    · assumption
    · exact Q'.le_refl' _
  have hsq : u*u ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ u hu1 hu0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv u)) hue)
  have hi : 22*(repairTolerance e*repairTolerance e) ≈ (22*(eighth*eighth))*(u*u) :=
    poly_identity_of_normal_eq (22*((.var 0*.var 1)*(.var 0*.var 1)))
      ((22*(.var 0*.var 0))*(.var 1*.var 1)) (by decide) (fun | 0 => eighth | _ => u)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hi)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (u*u)
      (by decide : (22:Q')*(eighth*eighth) ≤ 1) (sq_nonnegative u))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hsq))

private theorem raw_distance_bound (a b : RationalQuaternion) {e : Q'}
    (he : (0:Q') ≤ e) (h : ∀ j, Q'.abs (coordinate a j + -coordinate b j) ≤ e) :
    distSq a b ≤ 4*(e*e) := by
  have hs := Q'.add_le_add
    (Q'.add_le_add (square_le_of_abs_le he (h 0)) (square_le_of_abs_le he (h 1)))
    (Q'.add_le_add (square_le_of_abs_le he (h 2)) (square_le_of_abs_le he (h 3)))
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (poly_identity_of_normal_eq
    ((.var 0+.var 0)+(.var 0+.var 0)) (4*.var 0) (by decide) (fun _ => e*e)))

def realizationRate {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j)) (e : Q') : Nat :=
  max (residualRate R (repairTolerance e)) (commonRate R (repairTolerance e))

theorem repaired_row_bound {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (e : Q') (he : (0:Q') < e)
    (p q : Nat) (hp : realizationRate R e ≤ p) (hq : realizationRate R e ≤ q) :
    chord (repair (rawRow x p)) (repair (rawRow x q)) ≤ e := by
  let eta := repairTolerance e
  have heta := repairTolerance_positive he
  have hp0 := norm_residual_bound R hx eta heta p (Nat.le_trans (Nat.le_max_left _ _) hp)
  have hq0 := norm_residual_bound R hx eta heta q (Nat.le_trans (Nat.le_max_left _ _) hq)
  have hep : distSq (repair (rawRow x p)).val (rawRow x p) ≤ eta*eta :=
    Q'.le_trans' _ _ _ (repair_error_le _) (square_le_of_abs_le (Q'.le_of_lt heta) hp0)
  have heq : distSq (rawRow x q) (repair (rawRow x q)).val ≤ eta*eta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (distance_symm _ _))
      (Q'.le_trans' _ _ _ (repair_error_le _) (square_le_of_abs_le (Q'.le_of_lt heta) hq0))
  have hpq : distSq (rawRow x p) (rawRow x q) ≤ 4*(eta*eta) :=
    raw_distance_bound _ _ (Q'.le_of_lt heta) (fun j => by
      rw [coordinate_rawRow,coordinate_rawRow]
      exact common_regular R heta (Nat.le_trans (Nat.le_max_right _ _) hp)
        (Nat.le_trans (Nat.le_max_right _ _) hq) j)
  have h2 := distance_triangle (rawRow x p) (rawRow x q) (repair (rawRow x q)).val
  have h1 := distance_triangle (repair (rawRow x p)).val (rawRow x p) (repair (rawRow x q)).val
  have hb := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hep (by decide))
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (Q'.le_trans' _ _ _ h2 (Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left _ _ 2 hpq (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ 2 heq (by decide)))) (by decide))
  have hi : 2*(eta*eta)+2*(2*(4*(eta*eta))+2*(eta*eta)) ≈ 22*(eta*eta) :=
    poly_identity_of_normal_eq (2*.var 0+2*(2*(4*.var 0)+2*.var 0)) (22*.var 0)
      (by decide) (fun _ => eta*eta)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ hb
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hi) (repairTolerance_budget he)))

/-- The actual rational-unit Cauchy row, with a Type-valued modulus. -/
def realizationRow (x : Fin 4 → CReal) (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) : CauchyPoint where
  seq n := repair (rawRow x n)
  modulus := realizationRate R
  isCauchy := fun e he p q hp hq =>
    leEv_of_le (ofQ'_le_ofQ' (repaired_row_bound R hx e he p q hp hq))

def realization (x : Fin 4 → CReal) (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) : Point :=
  Quotient.mk chordSeminorm.completionSetoid (realizationRow x R hx)

/-! ## Coordinates of supplied original point rows -/

private theorem coordinate_motion (a b : UnitNorm) (e : Q') (he : (0:Q') < e)
    (h : chord a b ≤ e*e) (j : Fin 4) :
    coordinate a.val j ≤ coordinate b.val j+e ∧
      coordinate b.val j ≤ coordinate a.val j+e :=
  bounds_of_abs_sub (abs_le_of_square_le he
    (Q'.le_trans' _ _ _ (coordinate_difference_square_le a.val b.val j) h))

def coordinateRate (X : CauchyPoint) (e : Q') : Nat := X.modulus (e*e)

theorem rowCoordinate_regular (X : CauchyPoint) (j : Fin 4) (e : Q')
    (he : (0:Q') < e) (p q : Nat) (hp : coordinateRate X e ≤ p)
    (hq : coordinateRate X e ≤ q) :
    coordinate (X.seq p).val j ≤ coordinate (X.seq q).val j+e ∧
      coordinate (X.seq q).val j ≤ coordinate (X.seq p).val j+e :=
  coordinate_motion _ _ e he (constant_le_reflect
    (X.isCauchy (e*e) (Q'.mul_pos he he) p q hp hq)) j

def rowCoordinate (X : CauchyPoint) (j : Fin 4) : CReal where
  approx n := coordinate (X.seq n).val j
  cauchy := fun e he => ⟨coordinateRate X e,rowCoordinate_regular X j e he⟩

def rowCoordinateRegularity (X : CauchyPoint) (j : Fin 4) :
    InnerRegularity (rowCoordinate X j) where
  rate := coordinateRate X
  regular := rowCoordinate_regular X j

theorem rowCoordinate_norm (X : CauchyPoint) :
    Equiv (coordinateNorm (rowCoordinate X)) cone :=
  pointwise_equiv (fun n => (X.seq n).unitNorm)

theorem rowCoordinate_congr {X Y : CauchyPoint} (h : chordSeminorm.CompletionRel X Y)
    (j : Fin 4) : Equiv (rowCoordinate X j) (rowCoordinate Y j) := by
  rcases h with ⟨h⟩
  intro e he
  refine ⟨h.modulus (e*e),fun n hn => ?_⟩
  exact coordinate_motion _ _ e he
    (constant_le_reflect (h.close (e*e) (Q'.mul_pos he he) n hn)) j

/-- Quotient coordinates are RC values, not chosen CReal representatives. -/
def pointCoordinate (j : Fin 4) : Point → RC :=
  Quotient.lift (fun X => Quotient.mk crealSetoid (rowCoordinate X j))
    (fun _ _ h => Quotient.sound (rowCoordinate_congr h j))

theorem pointCoordinate_mk (X : CauchyPoint) (j : Fin 4) :
    pointCoordinate j (Quotient.mk chordSeminorm.completionSetoid X) =
      Quotient.mk crealSetoid (rowCoordinate X j) := rfl

/-! ## Full recovery of the four supplied coordinates -/

theorem repaired_coordinate_bound {x : Fin 4 → CReal} (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (e : Q') (he : (0:Q') < e)
    (n : Nat) (hn : residualRate R e ≤ n) (j : Fin 4) :
    Q'.abs (coordinate (repair (rawRow x n)).val j + -(x j).approx n) ≤ e := by
  have h := coordinate_difference_square_le (repair (rawRow x n)).val (rawRow x n) j
  rw [coordinate_rawRow] at h
  exact abs_le_of_square_le he (Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (repair_error_le _)
      (square_le_of_abs_le (Q'.le_of_lt he) (norm_residual_bound R hx e he n hn))))

/-- The constructed unit row recovers EVERY supplied coordinate. -/
theorem coordinate_realization (x : Fin 4 → CReal) (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (j : Fin 4) :
    Equiv (rowCoordinate (realizationRow x R hx) j) (x j) := by
  intro e he
  refine ⟨residualRate R e,fun n hn => ?_⟩
  exact bounds_of_abs_sub (repaired_coordinate_bound R hx e he n hn j)

theorem pointCoordinate_realization (x : Fin 4 → CReal) (R : ∀ j, InnerRegularity (x j))
    (hx : Equiv (coordinateNorm x) cone) (j : Fin 4) :
    pointCoordinate j (realization x R hx) = Quotient.mk crealSetoid (x j) :=
  Quotient.sound (coordinate_realization x R hx j)

/-- Reconstructing coordinates of an existing supplied row returns its SAME Point. -/
theorem realization_rowCoordinate (X : CauchyPoint) :
    realization (rowCoordinate X) (rowCoordinateRegularity X) (rowCoordinate_norm X) =
      Quotient.mk chordSeminorm.completionSetoid X := by
  apply Quotient.sound
  refine ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull ?_⟩
  intro n
  have hr : rawRow (rowCoordinate X) n = (X.seq n).val := rfl
  change chordSeminorm.Null (repair (rawRow (rowCoordinate X) n)) (X.seq n)
  rw [hr]
  exact (null_iff_semantic _ _).mpr (repair_unit (X.seq n))

/-- The rational constant-coordinate producer, on both central signs and the equator. -/
def rationalCoordinates (a : UnitNorm) (j : Fin 4) : CReal := ofQ' (coordinate a.val j)

theorem rationalCoordinates_norm (a : UnitNorm) :
    Equiv (coordinateNorm (rationalCoordinates a)) cone :=
  pointwise_equiv (fun _ => a.unitNorm)

theorem realization_rational (a : UnitNorm)
    (R : ∀ j, InnerRegularity (rationalCoordinates a j)) :
    realization (rationalCoordinates a) R (rationalCoordinates_norm a) = embed a := by
  apply Quotient.sound
  refine ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull ?_⟩
  intro n
  have hr : rawRow (rationalCoordinates a) n = a.val := rfl
  change chordSeminorm.Null (repair (rawRow (rationalCoordinates a) n)) a
  rw [hr]
  exact (null_iff_semantic _ _).mpr (repair_unit a)

theorem realization_change_rates (x : Fin 4 → CReal)
    (R S : ∀ j, InnerRegularity (x j))
    (hx hy : Equiv (coordinateNorm x) cone) : realization x R hx = realization x S hy := by
  apply Quotient.sound
  refine ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull ?_⟩
  intro n
  exact (null_iff_semantic _ _).mpr (UnitNorm.semanticSetoid.iseqv.refl _)

private theorem distance_zero_of_coordinates (X Y : CauchyPoint)
    (h : ∀ j, Equiv (rowCoordinate X j) (rowCoordinate Y j)) :
    Equiv (RationalQuaternionCompletedDistance.representativeDist X Y) czero := by
  intro e he
  let eta := repairTolerance e
  have heta := repairTolerance_positive he
  obtain ⟨M0,h0⟩ := h 0 eta heta
  obtain ⟨M1,h1⟩ := h 1 eta heta
  obtain ⟨M2,h2⟩ := h 2 eta heta
  obtain ⟨M3,h3⟩ := h 3 eta heta
  refine ⟨max (max M0 M1) (max M2 M3),fun n hn => ⟨?_,?_⟩⟩
  · have hm0 := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
    have hm1 := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
    have hm2 := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
    have hm3 := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
    have hd : ∀ j, Q'.abs (coordinate (X.seq n).val j + -coordinate (Y.seq n).val j) ≤ eta := by
      intro j
      rcases j with ⟨j,hj⟩
      cases j with
      | zero => exact CReal.abs_sub_le_of_bounds (h0 n hm0).1 (h0 n hm0).2
      | succ j => cases j with
        | zero => exact CReal.abs_sub_le_of_bounds (h1 n hm1).1 (h1 n hm1).2
        | succ j => cases j with
          | zero => exact CReal.abs_sub_le_of_bounds (h2 n hm2).1 (h2 n hm2).2
          | succ j => cases j with
            | zero => exact CReal.abs_sub_le_of_bounds (h3 n hm3).1 (h3 n hm3).2
            | succ j => omega
    have hb : chord (X.seq n) (Y.seq n) ≤ e := Q'.le_trans' _ _ _
      (raw_distance_bound _ _ (Q'.le_of_lt heta) hd)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (eta*eta)
        (by decide : (4:Q') ≤ 22) (sq_nonnegative eta)) (repairTolerance_budget he))
    exact Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv (QPoly.q_zero_add_eqv e))
  · exact Q'.le_trans' _ _ _ (chord_nonnegative (X.seq n) (Y.seq n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-- The four semantic coordinates separate the existing point quotient. -/
theorem pointCoordinate_injective {x y : Point}
    (h : ∀ j, pointCoordinate j x = pointCoordinate j y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  apply Quotient.sound
  exact ⟨RationalQuaternionCompletedDistance.closeOfZero X Y
    (distance_zero_of_coordinates X Y (fun j => Quotient.exact (h j)))⟩

/-- Semantic coordinate changes, including changes of rates, give the same Point. -/
theorem realization_congr (x y : Fin 4 → CReal)
    (R : ∀ j, InnerRegularity (x j)) (S : ∀ j, InnerRegularity (y j))
    (hx : Equiv (coordinateNorm x) cone) (hy : Equiv (coordinateNorm y) cone)
    (h : ∀ j, Equiv (x j) (y j)) : realization x R hx = realization y S hy := by
  apply pointCoordinate_injective
  intro j
  rw [pointCoordinate_realization,pointCoordinate_realization]
  exact Quotient.sound (h j)

/-! ## Regression: any finite initial string of zero approximations -/

/-- The initial raw approximations really are zero, not assumed to lie on S³. -/
def delayedCoordinates (a : UnitNorm) (start : Nat) (j : Fin 4) : CReal where
  approx n := if n < start then 0 else coordinate a.val j
  cauchy := by
    intro e he
    refine ⟨start,fun p q hp hq => ?_⟩
    simp only [Nat.not_lt.mpr hp,Nat.not_lt.mpr hq,if_false]
    exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩

def delayedRegularity (a : UnitNorm) (start : Nat) (j : Fin 4) :
    InnerRegularity (delayedCoordinates a start j) where
  rate _ := start
  regular := by
    intro e he p q hp hq
    change (if p < start then 0 else coordinate a.val j) ≤
        (if q < start then 0 else coordinate a.val j)+e ∧
      (if q < start then 0 else coordinate a.val j) ≤
        (if p < start then 0 else coordinate a.val j)+e
    simp only [Nat.not_lt.mpr hp,Nat.not_lt.mpr hq,if_false]
    exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩

theorem delayedCoordinates_norm (a : UnitNorm) (start : Nat) :
    Equiv (coordinateNorm (delayedCoordinates a start)) cone := by
  intro e he
  refine ⟨start,fun n hn => ?_⟩
  have hr : rawRow (delayedCoordinates a start) n = a.val := by
    unfold rawRow delayedCoordinates
    simp only [Nat.not_lt.mpr hn,if_false]
    rfl
  have hnorm : (coordinateNorm (delayedCoordinates a start)).approx n ≈ (1:Q') := by
    rw [coordinateNorm_approx,hr]
    exact a.unitNorm
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hnorm) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnorm) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem realization_delayed (a : UnitNorm) (start : Nat) :
    realization (delayedCoordinates a start) (delayedRegularity a start)
      (delayedCoordinates_norm a start) = embed a := by
  have hc : ∀ j, Equiv (delayedCoordinates a start j) (rationalCoordinates a j) := by
    intro j e he
    refine ⟨start,fun n hn => ?_⟩
    change (if n < start then 0 else coordinate a.val j) ≤ coordinate a.val j+e ∧
      coordinate a.val j ≤ (if n < start then 0 else coordinate a.val j)+e
    simp only [Nat.not_lt.mpr hn,if_false]
    exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩
  exact Eq.trans (realization_congr _ _ (delayedRegularity a start)
    (fun j => InnerRegularity.ofQ' (coordinate a.val j))
    (delayedCoordinates_norm a start) (rationalCoordinates_norm a) hc)
    (realization_rational a (fun j => InnerRegularity.ofQ' (coordinate a.val j)))

theorem realization_central_signs_distinct :
    realization (rationalCoordinates unitOne)
        (fun j => InnerRegularity.ofQ' (coordinate unitOne.val j)) (rationalCoordinates_norm unitOne) ≠
      realization (rationalCoordinates unitNegativeOne)
        (fun j => InnerRegularity.ofQ' (coordinate unitNegativeOne.val j))
        (rationalCoordinates_norm unitNegativeOne) := by
  rw [realization_rational,realization_rational]
  intro h
  have hc := (embed_eq_iff unitOne unitNegativeOne).mp h
  have hh : ¬ unitOne.Equivalent unitNegativeOne := by
    unfold UnitNorm.Equivalent RationalQuaternion.Equivalent
    decide
  exact hh hc

end YMGap.RepTheory.RationalQuaternionCoordinateCompletion

#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.coordinate_rawRow
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.coordinateNorm_approx
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.coordinate_rate_le
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.coordinate_tail_bound
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.normRegularity
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.norm_residual_bound
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.repairTolerance_positive
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.repaired_row_bound
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realizationRow
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rowCoordinate_regular
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rowCoordinate
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rowCoordinateRegularity
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rowCoordinate_norm
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rowCoordinate_congr
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.pointCoordinate
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.pointCoordinate_mk
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.repaired_coordinate_bound
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.coordinate_realization
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.pointCoordinate_realization
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_rowCoordinate
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.rationalCoordinates_norm
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_rational
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_change_rates
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.pointCoordinate_injective
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_congr
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.delayedCoordinates
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.delayedRegularity
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.delayedCoordinates_norm
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_delayed
#print axioms YMGap.RepTheory.RationalQuaternionCoordinateCompletion.realization_central_signs_distinct
