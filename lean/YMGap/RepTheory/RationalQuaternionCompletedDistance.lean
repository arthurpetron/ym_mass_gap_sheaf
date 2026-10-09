/-
# The actual squared chord on the quaternion point-Cauchy quotient

The scalar representative is literally n ↦ chord(X_n,Y_n). Its regularity
uses the two given point moduli at epsilon^2/16; no monotonicity or selection
of quotient representatives is required. All completed-distance fields,
separation and group isometries are proved for the existing Point carrier.

This supplies the existing quantitative approximation/represented-Cauchy-row
interfaces. It does not prove arbitrary quotient-family completeness,
compactness, a matrix SU(2) identification, or a Haar extension.
-/

import YMGap.RepTheory.RationalQuaternionCauchyGroup
import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.RepTheory.RationalQuaternionCompletedDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv
local instance : Trans Q'.eqv Q'.eqv Q'.eqv :=
  ⟨fun h k => Q'.eqv_trans _ _ _ h k⟩

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a+c ≈ b+d := Q'.eqv_trans _ _ _
  (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _
  (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b := Q'.neg_eqv_congr _ _ h

private theorem sq_nonnegative (a : Q') : (0 : Q') ≤ a*a :=
  SumOfSquares.q_mul_self_nonneg a

private def sub (x y : RationalQuaternion) : RationalQuaternion :=
  ⟨x.r + -y.r, x.i + -y.i, x.j + -y.j, x.k + -y.k⟩

private structure QuaternionExpr where
  r : PE
  i : PE
  j : PE
  k : PE

private def qvar (n : Nat) : QuaternionExpr :=
  ⟨.var n, .var (n+1), .var (n+2), .var (n+3)⟩

private def qsub (x y : QuaternionExpr) : QuaternionExpr :=
  ⟨x.r + -y.r, x.i + -y.i, x.j + -y.j, x.k + -y.k⟩

private def qconj (x : QuaternionExpr) : QuaternionExpr :=
  ⟨x.r, -x.i, -x.j, -x.k⟩

private def qnorm (x : QuaternionExpr) : PE :=
  (x.r*x.r+x.i*x.i)+(x.j*x.j+x.k*x.k)

private def realProduct (x y : QuaternionExpr) : PE :=
  (x.r*y.r + -(x.i*y.i))+(-(x.j*y.j) + -(x.k*y.k))

private def environment (x x' y y' : RationalQuaternion) : Nat → Q'
  | 0 => x.r | 1 => x.i | 2 => x.j | 3 => x.k
  | 4 => x'.r | 5 => x'.i | 6 => x'.j | 7 => x'.k
  | 8 => y.r | 9 => y.i | 10 => y.j | 11 => y.k
  | 12 => y'.r | 13 => y'.i | 14 => y'.j | _ => y'.k

private theorem raw_difference (x x' y y' : RationalQuaternion) :
    RationalQuaternionSphereNets.distSq x y +
      -RationalQuaternionSphereNets.distSq x' y' ≈
    ((normSq x + -normSq x')+(normSq y + -normSq y')) +
      -(2*((RationalQuaternion.mul (sub x x') (RationalQuaternion.conj y)).r+
        (RationalQuaternion.mul x' (RationalQuaternion.conj (sub y y'))).r)) :=
  poly_identity_of_normal_eq
    (qnorm (qsub (qvar 0) (qvar 8)) + -qnorm (qsub (qvar 4) (qvar 12)))
    (((qnorm (qvar 0) + -qnorm (qvar 4))+
      (qnorm (qvar 8) + -qnorm (qvar 12)))+
      -(2*(realProduct (qsub (qvar 0) (qvar 4)) (qconj (qvar 8))+
        realProduct (qvar 4) (qconj (qsub (qvar 8) (qvar 12))))))
    (by decide) (environment x x' y y')

private def firstMovement (x x' y : UnitNorm) : RationalQuaternion :=
  RationalQuaternion.mul (sub x.val x'.val) (RationalQuaternion.conj y.val)

private def secondMovement (x' y y' : UnitNorm) : RationalQuaternion :=
  RationalQuaternion.mul x'.val (RationalQuaternion.conj (sub y.val y'.val))

private theorem movement_difference (x x' y y' : UnitNorm) :
    chord x y + -chord x' y' ≈
      -(2*((firstMovement x x' y).r+(secondMovement x' y y').r)) := by
  have hnorm : (normSq x.val + -normSq x'.val)+
      (normSq y.val + -normSq y'.val) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (ac (ac x.unitNorm (nc x'.unitNorm)) (ac y.unitNorm (nc y'.unitNorm)))
      (by decide : (((1 : Q') + -1)+(1 + -1)) ≈ 0)
  have hp := raw_difference x.val x'.val y.val y'.val
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
    (ac hnorm (Q'.eqv_refl _)) (QPoly.q_zero_add_eqv _))

private theorem firstMovement_norm (x x' y : UnitNorm) :
    normSq (firstMovement x x' y) ≈ chord x x' := by
  calc
    _ ≈ normSq (sub x.val x'.val)*normSq (RationalQuaternion.conj y.val) :=
      normSq_mul (sub x.val x'.val) (RationalQuaternion.conj y.val)
    _ ≈ normSq (sub x.val x'.val)*1 :=
      mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (normSq_conj y.val) y.unitNorm)
    _ ≈ chord x x' := Q'.mul_one_eqv _

private theorem secondMovement_norm (x' y y' : UnitNorm) :
    normSq (secondMovement x' y y') ≈ chord y y' := by
  calc
    _ ≈ normSq x'.val*normSq (RationalQuaternion.conj (sub y.val y'.val)) :=
      normSq_mul x'.val (RationalQuaternion.conj (sub y.val y'.val))
    _ ≈ 1*normSq (sub y.val y'.val) :=
      mc x'.unitNorm (normSq_conj (sub y.val y'.val))
    _ ≈ chord y y' := Q'.one_mul_eqv _

private theorem real_square_le (x : RationalQuaternion) : x.r*x.r ≤ normSq x :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (sq_nonnegative x.i))
    (Q'.add_le_self_of_nonneg _ _
      (Q'.zero_le_add _ _ (sq_nonnegative x.j) (sq_nonnegative x.k)))

private theorem twice_sum_square (a b : Q') :
    (-(2*(a+b)))*(-(2*(a+b))) ≤ 8*(a*a+b*b) := by
  have h := Q'.add_le_self_of_nonneg ((-(2*(a+b)))*(-(2*(a+b))))
    ((2*(a + -b))*(2*(a + -b))) (sq_nonnegative _)
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    ((-(2*(PolyExpr.var 0+PolyExpr.var 1)))*(-(2*(PolyExpr.var 0+PolyExpr.var 1)))+
      (2*(PolyExpr.var 0 + -(PolyExpr.var 1)))*(2*(PolyExpr.var 0 + -(PolyExpr.var 1))))
    (8*(PolyExpr.var 0*PolyExpr.var 0+PolyExpr.var 1*PolyExpr.var 1))
    (by decide) (fun | 0 => a | _ => b)

/-- A uniform scalar continuity estimate from the actual Hamilton norm law. -/
theorem chord_difference_square (x x' y y' : UnitNorm) :
    (chord x y + -chord x' y')*(chord x y + -chord x' y') ≤
      8*(chord x x'+chord y y') := by
  have hdiff := movement_difference x x' y y'
  have ha : (firstMovement x x' y).r*(firstMovement x x' y).r ≤ chord x x' :=
    Q'.le_trans' _ _ _ (real_square_le _) (Q'.le_of_eqv (firstMovement_norm x x' y))
  have hb : (secondMovement x' y y').r*(secondMovement x' y y').r ≤ chord y y' :=
    Q'.le_trans' _ _ _ (real_square_le _) (Q'.le_of_eqv (secondMovement_norm x' y y'))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mc hdiff hdiff))
    (Q'.le_trans' _ _ _ (twice_sum_square _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ (8 : Q') (Q'.add_le_add ha hb) (by decide)))

def movementTolerance (epsilon : Q') : Q' :=
  Q'.mkPos 1 16 (by decide)*(epsilon*epsilon)

theorem movementTolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < movementTolerance epsilon :=
  Q'.mul_pos (by decide) (Q'.mul_pos he he)

private theorem movement_budget (epsilon : Q') :
    8*(movementTolerance epsilon+movementTolerance epsilon) ≈ epsilon*epsilon := by
  have h : 8*(movementTolerance epsilon+movementTolerance epsilon) ≈
      (16*Q'.mkPos 1 16 (by decide))*(epsilon*epsilon) :=
    poly_identity_of_normal_eq
      (8*((PolyExpr.var 0*PolyExpr.var 1)+(PolyExpr.var 0*PolyExpr.var 1)))
      ((16*PolyExpr.var 0)*PolyExpr.var 1) (by decide)
      (fun | 0 => Q'.mkPos 1 16 (by decide) | _ => epsilon*epsilon)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (mc (by decide : (16*Q'.mkPos 1 16 (by decide)) ≈ (1 : Q')) (Q'.eqv_refl _))
    (Q'.one_mul_eqv _))

private theorem neg_square (a : Q') : (-a)*(-a) ≈ a*a :=
  poly_identity_of_normal_eq ((-(PolyExpr.var 0))*(-(PolyExpr.var 0)))
    (PolyExpr.var 0*PolyExpr.var 0) (by decide) (fun _ => a)

private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact neg_square a

private theorem le_add_of_difference {a b epsilon : Q'} (h : a + -b ≤ epsilon) :
    a ≤ b+epsilon := by
  have hs := Q'.add_le_add_right _ _ b h
  have he : (a + -b)+b ≈ a := Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv a (-b) b) (Q'.eqv_trans _ _ _
      (ac (Q'.eqv_refl a) (Q'.neg_add_self_eqv b)) (QPoly.q_add_zero_eqv a))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.add_comm_eqv epsilon b)))

private theorem two_sided_of_square {a b epsilon : Q'} (he : (0 : Q') < epsilon)
    (h : (a + -b)*(a + -b) ≤ epsilon*epsilon) :
    a ≤ b+epsilon ∧ b ≤ a+epsilon := by
  have habs : Q'.abs (a + -b) ≤ epsilon := CReal.le_of_sq_le_sq he
    (Q'.abs_nonneg _) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square _)) h)
  have hneg : b + -a ≈ -(a + -b) :=
    poly_identity_of_normal_eq (PolyExpr.var 1 + -(PolyExpr.var 0))
      (-(PolyExpr.var 0 + -(PolyExpr.var 1))) (by decide) (fun | 0 => a | _ => b)
  exact ⟨le_add_of_difference (Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs),
    le_add_of_difference (Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg)
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) habs))⟩

theorem chord_continuity (x x' y y' : UnitNorm) (epsilon : Q')
    (he : (0 : Q') < epsilon)
    (hx : chord x x' ≤ movementTolerance epsilon)
    (hy : chord y y' ≤ movementTolerance epsilon) :
    chord x y ≤ chord x' y'+epsilon ∧ chord x' y' ≤ chord x y+epsilon := by
  apply two_sided_of_square he
  exact Q'.le_trans' _ _ _ (chord_difference_square x x' y y')
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (8 : Q') (Q'.add_le_add hx hy) (by decide))
      (Q'.le_of_eqv (movement_budget epsilon)))

/-! ## Literal scalar rows, with computed regularity data -/

private theorem constant_le_reflect {a b : Q'}
    (h : leEv (ofQ' a) (ofQ' b)) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
  have ht : a ≤ b+Q'.invSucc N := hM M (Nat.le_refl M)
  have he : b+Q'.ofNat 1*Q'.invSucc N ≈ b+Q'.invSucc N :=
    ac (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (show Q'.ofNat 1 ≈ (1 : Q') by decide) (Q'.eqv_refl _)) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv he)

def distanceRate (X Y : CauchyPoint) (epsilon : Q') : Nat :=
  max (X.modulus (movementTolerance epsilon)) (Y.modulus (movementTolerance epsilon))

theorem distanceRow_regular (X Y : CauchyPoint) (epsilon : Q')
    (he : (0 : Q') < epsilon) (p q : Nat)
    (hp : distanceRate X Y epsilon ≤ p) (hq : distanceRate X Y epsilon ≤ q) :
    chord (X.seq p) (Y.seq p) ≤ chord (X.seq q) (Y.seq q)+epsilon ∧
      chord (X.seq q) (Y.seq q) ≤ chord (X.seq p) (Y.seq p)+epsilon := by
  have ht := movementTolerance_positive he
  have hxp := Nat.le_trans (Nat.le_max_left _ _) hp
  have hxq := Nat.le_trans (Nat.le_max_left _ _) hq
  have hyp := Nat.le_trans (Nat.le_max_right _ _) hp
  have hyq := Nat.le_trans (Nat.le_max_right _ _) hq
  exact chord_continuity _ _ _ _ epsilon he
    (constant_le_reflect (X.isCauchy _ ht p q hxp hxq))
    (constant_le_reflect (Y.isCauchy _ ht p q hyp hyq))

/-- The approximations are the ORIGINAL row distances, without reindexing. -/
def representativeDist (X Y : CauchyPoint) : CReal where
  approx n := chord (X.seq n) (Y.seq n)
  cauchy := fun epsilon he =>
    ⟨distanceRate X Y epsilon, distanceRow_regular X Y epsilon he⟩

def representativeDistRegularity (X Y : CauchyPoint) :
    InnerRegularity (representativeDist X Y) where
  rate := distanceRate X Y
  regular := distanceRow_regular X Y

theorem representativeDist_approx (X Y : CauchyPoint) (n : Nat) :
    (representativeDist X Y).approx n = chord (X.seq n) (Y.seq n) := rfl

theorem representativeDist_converges (X Y : CauchyPoint) :
    ConvergesTo (fun n => chordSeminorm.distSq (X.seq n) (Y.seq n))
      (representativeDist X Y) := by
  intro epsilon he
  refine ⟨distanceRate X Y epsilon, fun p hp =>
    ⟨distanceRate X Y epsilon, fun q hq => ?_⟩⟩
  exact distanceRow_regular X Y epsilon he p q hp hq

theorem representativeDist_congr {X X' Y Y' : CauchyPoint}
    (hx : chordSeminorm.CompletionRel X X') (hy : chordSeminorm.CompletionRel Y Y') :
    Equiv (representativeDist X Y) (representativeDist X' Y') := by
  rcases hx with ⟨hX⟩
  rcases hy with ⟨hY⟩
  intro epsilon he
  let delta := movementTolerance epsilon
  refine ⟨max (hX.modulus delta) (hY.modulus delta), fun n hn => ?_⟩
  exact chord_continuity _ _ _ _ epsilon he
    (constant_le_reflect (hX.close delta (movementTolerance_positive he) n
      (Nat.le_trans (Nat.le_max_left _ _) hn)))
    (constant_le_reflect (hY.close delta (movementTolerance_positive he) n
      (Nat.le_trans (Nat.le_max_right _ _) hn)))

def completedDist : Point → Point → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeDist X Y))
    (fun _ _ _ _ hx hy => Quotient.sound (representativeDist_congr hx hy))

theorem completedDist_mk (X Y : CauchyPoint) :
    completedDist (Quotient.mk chordSeminorm.completionSetoid X)
      (Quotient.mk chordSeminorm.completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist X Y) := rfl

private theorem pointwise_equiv {a b : CReal} (h : ∀ n, a.approx n ≈ b.approx n) :
    Equiv a b := by
  intro epsilon he
  refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (h n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

theorem completedDist_nonnegative (x y : Point) : RCnonneg (completedDist x y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact leEv_ofQ'_of_approx_ge (fun n => chord_nonnegative (X.seq n) (Y.seq n))

theorem completedDist_symm (x y : Point) : completedDist x y = completedDist y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (pointwise_equiv (fun n => chord_symm (X.seq n) (Y.seq n)))

theorem completedDist_triangle (x y z : Point) :
    RCle (completedDist x z)
      (RCadd (RCadd (completedDist x y) (completedDist x y))
        (RCadd (completedDist y z) (completedDist y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z epsilon he
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _ (chord_triangle (X.seq n) (Y.seq n) (Z.seq n))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-! ## Separation, with no semantic-zero cutoff extracted into data -/

def closeOfZero (X Y : CauchyPoint) (h : Equiv (representativeDist X Y) czero) :
    chordSeminorm.Close X Y where
  modulus epsilon := distanceRate X Y (HalfPow.half*epsilon)
  close := by
    intro epsilon he n hn
    have hh := ExpNeg.half_mul_pos epsilon he
    obtain ⟨M, hM⟩ := h (HalfPow.half*epsilon) hh
    let q := max M (distanceRate X Y (HalfPow.half*epsilon))
    have hq : chord (X.seq q) (Y.seq q) ≤ HalfPow.half*epsilon :=
      Q'.le_trans' _ _ _ (hM q (Nat.le_max_left _ _)).1
        (Q'.le_of_eqv (QPoly.q_zero_add_eqv _))
    have hr := (distanceRow_regular X Y (HalfPow.half*epsilon) hh n q hn
      (Nat.le_max_right _ _)).1
    have hb : chord (X.seq n) (Y.seq n) ≤ epsilon :=
      Q'.le_trans' _ _ _ hr (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (HalfPow.half*epsilon) hq)
        (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))
    exact leEv_of_le (ofQ'_le_ofQ' hb)

theorem representativeDist_zero_of_close {X Y : CauchyPoint}
    (h : chordSeminorm.Close X Y) : Equiv (representativeDist X Y) czero := by
  intro epsilon he
  refine ⟨h.modulus epsilon, fun n hn => ⟨?_, ?_⟩⟩
  · have hb := constant_le_reflect (h.close epsilon he n hn)
    exact Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv (QPoly.q_zero_add_eqv epsilon))
  · exact Q'.le_trans' _ _ _ (chord_nonnegative (X.seq n) (Y.seq n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

theorem completedDist_zero_iff (x y : Point) : completedDist x y = RCzero ↔ x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  constructor
  · intro h
    have hzero : Equiv (representativeDist X Y) czero := Quotient.exact h
    exact Quotient.sound ⟨closeOfZero X Y hzero⟩
  · intro h
    have hclose : chordSeminorm.CompletionRel X Y := Quotient.exact h
    rcases hclose with ⟨hc⟩
    exact Quotient.sound (representativeDist_zero_of_close hc)

theorem completedDist_refl (x : Point) : completedDist x x = RCzero :=
  (completedDist_zero_iff x x).mpr rfl

/-- Every field is constructed on the already existing point quotient. -/
def distanceData : Continuum.CRealSeminormCompletedApproximation.DistanceData chordSeminorm where
  representativeDist := representativeDist
  representativeDist_converges := representativeDist_converges
  completedDist := completedDist
  completedDist_mk := completedDist_mk
  completedDist_nonnegative := completedDist_nonnegative
  completedDist_symm := completedDist_symm
  completedDist_triangle := completedDist_triangle
  completedDist_zero_iff := completedDist_zero_iff

theorem completedDist_embed (x y : UnitNorm) :
    completedDist (embed x) (embed y) = Quotient.mk crealSetoid (ofQ' (chord x y)) :=
  Continuum.CRealSeminormCompletedApproximation.completedDist_embedRep distanceData x y

theorem completedDist_signs : completedDist (embed unitOne) (embed unitNegativeOne) =
    Quotient.mk crealSetoid (ofQ' (4 : Q')) := by
  rw [completedDist_embed]
  exact Quotient.sound (ofQ'_equiv_of_eqv (by decide : chord unitOne unitNegativeOne ≈ 4))

/-! ## The original group operations are isometries of this same distance -/

theorem completedDist_mul_left (z x y : Point) :
    completedDist (completedMul z x) (completedMul z y) = completedDist x y := by
  refine Quotient.inductionOn₃ z x y ?_
  intro Z X Y
  exact Quotient.sound (pointwise_equiv
    (fun n => chord_mul_left (Z.seq n) (X.seq n) (Y.seq n)))

theorem completedDist_mul_right (x y z : Point) :
    completedDist (completedMul x z) (completedMul y z) = completedDist x y := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact Quotient.sound (pointwise_equiv
    (fun n => chord_mul_right (X.seq n) (Y.seq n) (Z.seq n)))

theorem completedDist_inverse (x y : Point) :
    completedDist (completedInv x) (completedInv y) = completedDist x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (pointwise_equiv (fun n => chord_inverse (X.seq n) (Y.seq n)))

/-- Different Cauchy moduli with the same row do not change its distances. -/
theorem representativeDist_of_same_rows (X X' Y Y' : CauchyPoint)
    (hx : ∀ n, (X.seq n).Equivalent (X'.seq n))
    (hy : ∀ n, (Y.seq n).Equivalent (Y'.seq n)) :
    Equiv (representativeDist X Y) (representativeDist X' Y') :=
  pointwise_equiv (fun n => chord_congr (hx n) (hy n))

/-! ## Actual consumers: supplied-row approximation and finite-net tail cover -/

def approximationData (X : CauchyPoint) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' x : UnitNorm,
      RCle (completedDist (embed x) (Quotient.mk chordSeminorm.completionSetoid X))
        (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  Continuum.CRealSeminormCompletedApproximation.approximationData distanceData X epsilon he

theorem completed_net_cover (X : CauchyPoint) (N : Nat) (hN : 0 < N) :
    RCle (completedDist (embed (rowNetPoint X N hN))
      (Quotient.mk chordSeminorm.completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (Q'.mkPos 48 (N*N) (Nat.mul_pos hN hN)))) := by
  apply Continuum.CRealSeminormCompletedApproximation.representativeDist_le_of_eventually
    distanceData (chordSeminorm.constant (rowNetPoint X N hN)) X
    (Q'.mkPos 48 (N*N) (Nat.mul_pos hN hN)) (rowNetStage X N hN)
  intro k hk
  exact leEv_of_le (ofQ'_le_ofQ' (rowNet_tail_bound X N hN k hk))

#print axioms chord_difference_square
#print axioms movementTolerance
#print axioms movementTolerance_positive
#print axioms chord_continuity
#print axioms distanceRate
#print axioms distanceRow_regular
#print axioms representativeDist
#print axioms representativeDistRegularity
#print axioms representativeDist_approx
#print axioms representativeDist_converges
#print axioms representativeDist_congr
#print axioms completedDist
#print axioms completedDist_mk
#print axioms completedDist_nonnegative
#print axioms completedDist_symm
#print axioms completedDist_triangle
#print axioms closeOfZero
#print axioms representativeDist_zero_of_close
#print axioms completedDist_zero_iff
#print axioms completedDist_refl
#print axioms distanceData
#print axioms completedDist_embed
#print axioms completedDist_signs
#print axioms completedDist_mul_left
#print axioms completedDist_mul_right
#print axioms completedDist_inverse
#print axioms representativeDist_of_same_rows
#print axioms approximationData
#print axioms completed_net_cover

end YMGap.RepTheory.RationalQuaternionCompletedDistance
