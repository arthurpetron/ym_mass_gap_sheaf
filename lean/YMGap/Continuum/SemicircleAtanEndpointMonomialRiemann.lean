/-
# Exact monomial-cell factorization for the endpoint atan series

The endpoint-series route is reduced to uniform Riemann convergence of finite
monomial polynomials.  This file supplies the binomial-free algebraic core.
For nonnegative `x <= y`, the mixed power sum

    S_p(x,y) = y^p + x*y^(p-1) + ... + x^p

simultaneously factors `y^(p+1)-x^(p+1)` and lies between
`(p+1)x^p` and `(p+1)y^p`.  Multiplication by `1/(p+1)` therefore sandwiches
the exact antiderivative increment between the left and right rectangles.
-/

import YMGap.Continuum.SemicircleAtanEndpointSeriesSum

namespace YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanEndpointCellFactor
open YMGap.Continuum.SemicircleAtanEndpointSeriesSum

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private def factorDistribL : RingNormaliser.PolyExpr :=
  .mul (.add (.var 1) (.neg (.var 0)))
    (.add (.mul (.var 1) (.var 2)) (.var 3))

private def factorDistribR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.var 1) (.mul (.add (.var 1) (.neg (.var 0))) (.var 2)))
    (.mul (.add (.var 1) (.neg (.var 0))) (.var 3))

private theorem factorDistrib_normal :
    RingNormaliser.normalize factorDistribL =
      RingNormaliser.normalize factorDistribR := by decide

private theorem factor_distrib (x y s t : Q') :
    (y + -x) * (y * s + t) ≈
      y * ((y + -x) * s) + (y + -x) * t := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    factorDistribL factorDistribR factorDistrib_normal
    (fun | 0 => x | 1 => y | 2 => s | _ => t)
  simpa [factorDistribL, factorDistribR, RingNormaliser.eval] using h

private def factorCancelL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.var 1) (.add (.var 3) (.neg (.var 2))))
    (.mul (.add (.var 1) (.neg (.var 0))) (.var 2))

private def factorCancelR : RingNormaliser.PolyExpr :=
  .add (.mul (.var 3) (.var 1)) (.neg (.mul (.var 2) (.var 0)))

private theorem factorCancel_normal :
    RingNormaliser.normalize factorCancelL =
      RingNormaliser.normalize factorCancelR := by decide

private theorem factor_cancel (x y X Y : Q') :
    y * (Y + -X) + (y + -x) * X ≈ Y * y + -(X * x) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    factorCancelL factorCancelR factorCancel_normal
    (fun | 0 => x | 1 => y | 2 => X | _ => Y)
  simpa [factorCancelL, factorCancelR, RingNormaliser.eval] using h

/-- Horner form of `y^p + x*y^(p-1) + ... + x^p`. -/
def mixedPowSum (x y : Q') : Nat → Q'
  | 0 => 1
  | p + 1 => y * mixedPowSum x y p + qpow x (p + 1)

theorem mixedPowSum_nonnegative {x y : Q'}
    (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y) :
    ∀ p, (0 : Q') ≤ mixedPowSum x y p
  | 0 => Q'.zero_le_one
  | p + 1 =>
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hy (mixedPowSum_nonnegative hx hy p))
        (qpow_nonneg x hx (p + 1))

/-- Difference-of-powers factorization, proved without a binomial theorem. -/
theorem mixedPowSum_factor (x y : Q') : ∀ p,
    ((y + -x) * mixedPowSum x y p) ≈
      (qpow y (p + 1) + -qpow x (p + 1))
  | 0 => by
      unfold mixedPowSum qpow
      have hz : y * ((1 : Q') + -1) ≈ 0 := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left y _ _ (Q'.add_neg_self_eqv 1)) ?_
        exact Q'.mul_zero_eqv _
      refine Q'.eqv_trans _
        (y * ((1 : Q') + -1) + (y + -x) * 1) _ ?_ ?_
      · refine Q'.eqv_trans _
          ((0 : Q') + (y + -x) * 1) _ ?_ ?_
        · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
        · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hz)
      · exact factor_cancel x y 1 1
  | p + 1 => by
      have ih := mixedPowSum_factor x y p
      refine Q'.eqv_trans _
        (y * ((y + -x) * mixedPowSum x y p) +
          (y + -x) * qpow x (p + 1)) _ ?_ ?_
      · exact factor_distrib x y (mixedPowSum x y p) (qpow x (p + 1))
      · refine Q'.eqv_trans _
          (y * (qpow y (p + 1) + -qpow x (p + 1)) +
            (y + -x) * qpow x (p + 1)) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left y _ _ ih)
        · have hySucc : qpow y (p + 1 + 1) = qpow y (p + 1) * y := rfl
          have hxSucc : qpow x (p + 1 + 1) = qpow x (p + 1) * x := rfl
          rw [hySucc, hxSucc]
          exact factor_cancel x y (qpow x (p + 1)) (qpow y (p + 1))

private theorem cast_succ (p : Nat) :
    Q'.ofNat (p + 1) ≈ Q'.ofNat p + 1 :=
  Q'.ofNat_add_eqv p 1

private theorem cast_succ_succ (p : Nat) :
    Q'.ofNat (p + 2) ≈ Q'.ofNat (p + 1) + 1 := by
  have h := Q'.ofNat_add_eqv (p + 1) 1
  simpa only [Nat.add_assoc] using h

/-- Lower rectangle bound for the mixed cofactor. -/
theorem mixedPowSum_lower {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) : ∀ p,
    Q'.ofNat (p + 1) * qpow x p ≤ mixedPowSum x y p
  | 0 => by
      unfold mixedPowSum qpow
      exact Q'.le_of_eqv (by ring_qeqv)
  | p + 1 => by
      have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      have ih := mixedPowSum_lower hx hxy p
      have hS0 := mixedPowSum_nonnegative hx hy p
      have hxyS : x * mixedPowSum x y p ≤
          y * mixedPowSum x y p :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hxy hS0
      have hxih : x * (Q'.ofNat (p + 1) * qpow x p) ≤
          x * mixedPowSum x y p :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih hx
      have hmain :
          x * (Q'.ofNat (p + 1) * qpow x p) + qpow x (p + 1) ≤
            y * mixedPowSum x y p + qpow x (p + 1) :=
        Q'.add_le_add_right _ _ _ (Q'.le_trans' _ _ _ hxih hxyS)
      refine Q'.le_trans' _ _ _ ?_ hmain
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat (p + 1) + 1) * qpow x (p + 1)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (cast_succ_succ p)
      · have hxSucc : qpow x (p + 1) = qpow x p * x := rfl
        rw [hxSucc]
        ring_qeqv

/-- Upper rectangle bound for the mixed cofactor. -/
theorem mixedPowSum_upper {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) : ∀ p,
    mixedPowSum x y p ≤ Q'.ofNat (p + 1) * qpow y p
  | 0 => by
      unfold mixedPowSum qpow
      exact Q'.le_of_eqv (by ring_qeqv)
  | p + 1 => by
      have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      have ih := mixedPowSum_upper hx hxy p
      have hyih : y * mixedPowSum x y p ≤
          y * (Q'.ofNat (p + 1) * qpow y p) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih hy
      have hp : qpow x (p + 1) ≤ qpow y (p + 1) :=
        qpow_mono hx hxy (p + 1)
      have hmain :
          y * mixedPowSum x y p + qpow x (p + 1) ≤
            y * (Q'.ofNat (p + 1) * qpow y p) + qpow y (p + 1) :=
        Q'.add_le_add hyih hp
      refine Q'.le_trans' _ _ _ hmain ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat (p + 1) + 1) * qpow y (p + 1)) _ ?_ ?_
      · have hySucc : qpow y (p + 1) = qpow y p * y := rfl
        rw [hySucc]
        ring_qeqv
      · exact Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_symm (cast_succ_succ p))

/-- The exact antiderivative increment of the monomial `t^p`. -/
def monomialIncrement (x y : Q') (p : Nat) : Q' :=
  Q'.invSucc p * (qpow y (p + 1) + -qpow x (p + 1))

theorem invSucc_nonnegative (p : Nat) :
    (0 : Q') ≤ Q'.invSucc p := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold Q'.invSucc
  rw [Q'.mkPos_num]
  decide

private theorem invSucc_mul_count (p : Nat) :
    Q'.invSucc p * Q'.ofNat (p + 1) ≈ 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  exact Q'.ofNat_succ_mul_invSucc p

/-- Exact antiderivative increment as mesh times the averaged mixed cofactor. -/
theorem monomialIncrement_factor (x y : Q') (p : Nat) :
    monomialIncrement x y p ≈
      (y + -x) * (Q'.invSucc p * mixedPowSum x y p) := by
  unfold monomialIncrement
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.invSucc p) _ _
      (Q'.eqv_symm (mixedPowSum_factor x y p))) ?_
  ring_qeqv

/-- The exact monomial integral over one nonnegative cell lies above its left
rectangle. -/
theorem leftRectangle_le_increment {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (p : Nat) :
    (y + -x) * qpow x p ≤ monomialIncrement x y p := by
  have hmesh : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have havg : qpow x p ≤ Q'.invSucc p * mixedPowSum x y p := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc p)
      (mixedPowSum_lower hx hxy p) (invSucc_nonnegative p)
    refine Q'.le_trans' _ _ _ ?_ hscaled
    have hnorm :
        Q'.invSucc p * (Q'.ofNat (p + 1) * qpow x p) ≈ qpow x p := by
      refine Q'.eqv_trans _
        ((Q'.invSucc p * Q'.ofNat (p + 1)) * qpow x p) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.invSucc p) (Q'.ofNat (p + 1)) (qpow x p))
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (invSucc_mul_count p)) ?_
        exact Q'.one_mul_eqv _
    exact Q'.ge_of_eqv hnorm
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ havg hmesh
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.eqv_symm (monomialIncrement_factor x y p)))

/-- The exact monomial integral over one nonnegative cell lies below its right
rectangle. -/
theorem increment_le_rightRectangle {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (p : Nat) :
    monomialIncrement x y p ≤ (y + -x) * qpow y p := by
  have hmesh : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have havg : Q'.invSucc p * mixedPowSum x y p ≤ qpow y p := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc p)
      (mixedPowSum_upper hx hxy p) (invSucc_nonnegative p)
    refine Q'.le_trans' _ _ _ hscaled ?_
    have hnorm :
        Q'.invSucc p * (Q'.ofNat (p + 1) * qpow y p) ≈ qpow y p := by
      refine Q'.eqv_trans _
        ((Q'.invSucc p * Q'.ofNat (p + 1)) * qpow y p) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.invSucc p) (Q'.ofNat (p + 1)) (qpow y p))
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (invSucc_mul_count p)) ?_
        exact Q'.one_mul_eqv _
    exact Q'.le_of_eqv hnorm
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ havg hmesh
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (monomialIncrement_factor x y p)) hmul

/-! ## Finite telescoping and endpoint-grid assembly -/

private def incrementAddL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))
    (.mul (.var 0) (.add (.var 3) (.neg (.var 2))))

private def incrementAddR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.add (.var 3) (.neg (.var 1)))

private theorem incrementAdd_normal :
    RingNormaliser.normalize incrementAddL =
      RingNormaliser.normalize incrementAddR := by decide

theorem monomialIncrement_add (x y z : Q') (p : Nat) :
    monomialIncrement x y p + monomialIncrement y z p ≈
      monomialIncrement x z p := by
  unfold monomialIncrement
  have h := RingNormaliser.poly_identity_of_normal_eq
    incrementAddL incrementAddR incrementAdd_normal
    (fun | 0 => Q'.invSucc p
         | 1 => qpow x (p + 1)
         | 2 => qpow y (p + 1)
         | _ => qpow z (p + 1))
  simpa [incrementAddL, incrementAddR, RingNormaliser.eval] using h

theorem monomialIncrement_self (x : Q') (p : Nat) :
    monomialIncrement x x p ≈ 0 := by
  unfold monomialIncrement
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.invSucc p) _ 0
      (Q'.add_neg_self_eqv (qpow x (p + 1)))) ?_
  exact Q'.mul_zero_eqv _

/-- Adjacent exact monomial antiderivative increments telescope. -/
theorem finSum_monomialIncrement_telescope (x : Nat → Q') (p : Nat) : ∀ n,
    finSum (fun j => monomialIncrement (x j) (x (j + 1)) p) n ≈
      monomialIncrement (x 0) (x n) p
  | 0 => Q'.eqv_symm (monomialIncrement_self (x 0) p)
  | n + 1 => by
      refine Q'.eqv_trans _
        (monomialIncrement (x 0) (x n) p +
          monomialIncrement (x n) (x (n + 1)) p) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_monomialIncrement_telescope x p n)
      · exact monomialIncrement_add (x 0) (x n) (x (n + 1)) p

def endpointMonomialLeftSum
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  finSum (fun j =>
    scaledMesh 1 k n hk hn * qpow (endpointNode k n j hk hn) p) n

def endpointMonomialRightSum
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  finSum (fun j =>
    scaledMesh 1 k n hk hn * qpow (endpointNode k n (j + 1) hk hn) p) n

def endpointMonomialIncrementSum
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  finSum (fun j => (2 : Q') * monomialIncrement
    (endpointNode k n j hk hn) (endpointNode k n (j + 1) hk hn) p) n

/-- The formal endpoint value `2 * (1/k)^(p+1)/(p+1)`. -/
def endpointMonomialValue (k p : Nat) (hk : 0 < k) : Q' :=
  (2 : Q') * (Q'.invSucc p * qpow (rat 1 k hk) (p + 1))

theorem scaledMesh_eqv_two_gridMesh
    (k n : Nat) (hk : 0 < k) (hn : 0 < n) :
    scaledMesh 1 k n hk hn ≈ (2 : Q') * gridMesh 1 k n hk hn := by
  show (scaledMesh 1 k n hk hn).num *
      (((2 : Q') * gridMesh 1 k n hk hn).den : Int) =
    ((2 : Q') * gridMesh 1 k n hk hn).num *
      ((scaledMesh 1 k n hk hn).den : Int)
  unfold scaledMesh gridMesh rat
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, two_num_cast, two_den_cast]
  push_cast
  ac_rfl

private theorem scaledMesh_eqv_two_step
    (k n j : Nat) (hk : 0 < k) (hn : 0 < n) :
    scaledMesh 1 k n hk hn ≈
      (2 : Q') *
        (endpointNode k n (j + 1) hk hn +
          -endpointNode k n j hk hn) := by
  refine Q'.eqv_trans _ _ _ (scaledMesh_eqv_two_gridMesh k n hk hn) ?_
  exact Q'.mul_eqv_congr_left 2 _ _
    (Q'.eqv_symm (gridNode_step_eqv 1 k n j hk hn))

theorem endpointMonomial_left_cell_le_increment
    (k n j p : Nat) (hk : 0 < k) (hn : 0 < n) :
    scaledMesh 1 k n hk hn * qpow (endpointNode k n j hk hn) p ≤
      (2 : Q') * monomialIncrement
        (endpointNode k n j hk hn) (endpointNode k n (j + 1) hk hn) p := by
  let x := endpointNode k n j hk hn
  let y := endpointNode k n (j + 1) hk hn
  have hx : (0 : Q') ≤ x := gridNode_nonneg 1 k n j hk hn
  have hxy : x ≤ y := gridNode_mono 1 k n j (j + 1) hk hn (Nat.le_succ j)
  have hrect := leftRectangle_le_increment hx hxy p
  have htwo : (0 : Q') ≤ (2 : Q') := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hrect htwo
  have hmesh : scaledMesh 1 k n hk hn ≈ (2 : Q') * (y + -x) := by
    simpa [x, y] using scaledMesh_eqv_two_step k n j hk hn
  have heq :
      scaledMesh 1 k n hk hn * qpow x p ≈
        (2 : Q') * ((y + -x) * qpow x p) := by
    refine Q'.eqv_trans _
      (((2 : Q') * (y + -x)) * qpow x p) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hmesh
    · ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hscaled

theorem endpointMonomial_increment_le_right_cell
    (k n j p : Nat) (hk : 0 < k) (hn : 0 < n) :
    (2 : Q') * monomialIncrement
        (endpointNode k n j hk hn) (endpointNode k n (j + 1) hk hn) p ≤
      scaledMesh 1 k n hk hn *
        qpow (endpointNode k n (j + 1) hk hn) p := by
  let x := endpointNode k n j hk hn
  let y := endpointNode k n (j + 1) hk hn
  have hx : (0 : Q') ≤ x := gridNode_nonneg 1 k n j hk hn
  have hxy : x ≤ y := gridNode_mono 1 k n j (j + 1) hk hn (Nat.le_succ j)
  have hrect := increment_le_rightRectangle hx hxy p
  have htwo : (0 : Q') ≤ (2 : Q') := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hrect htwo
  have hmesh : scaledMesh 1 k n hk hn ≈ (2 : Q') * (y + -x) := by
    simpa [x, y] using scaledMesh_eqv_two_step k n j hk hn
  have heq :
      scaledMesh 1 k n hk hn * qpow y p ≈
        (2 : Q') * ((y + -x) * qpow y p) := by
    refine Q'.eqv_trans _
      (((2 : Q') * (y + -x)) * qpow y p) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hmesh
    · ring_qeqv
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv heq)

/-- Every finite endpoint monomial left sum lies below the exact telescoping
antiderivative sum. -/
theorem endpointMonomialLeftSum_le_incrementSum
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialLeftSum k n p hk hn ≤
      endpointMonomialIncrementSum k n p hk hn := by
  unfold endpointMonomialLeftSum endpointMonomialIncrementSum
  exact ExpNeg.finSum_le_finSum_of_termwise _ _
    (fun j => endpointMonomial_left_cell_le_increment k n j p hk hn) n

/-- The exact telescoping antiderivative sum lies below every finite endpoint
monomial right sum. -/
theorem endpointMonomialIncrementSum_le_rightSum
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialIncrementSum k n p hk hn ≤
      endpointMonomialRightSum k n p hk hn := by
  unfold endpointMonomialIncrementSum endpointMonomialRightSum
  exact ExpNeg.finSum_le_finSum_of_termwise _ _
    (fun j => endpointMonomial_increment_le_right_cell k n j p hk hn) n

theorem endpointMonomialIncrementSum_telescope
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialIncrementSum k n p hk hn ≈
      (2 : Q') * monomialIncrement
        (endpointNode k n 0 hk hn) (endpointNode k n n hk hn) p := by
  unfold endpointMonomialIncrementSum
  refine Q'.eqv_trans _
    ((2 : Q') * finSum (fun j => monomialIncrement
      (endpointNode k n j hk hn)
      (endpointNode k n (j + 1) hk hn) p) n) _ ?_ ?_
  · exact Q'.eqv_symm (const_mul_finSum _ 2 n)
  · exact Q'.mul_eqv_congr_left 2 _ _
      (finSum_monomialIncrement_telescope
        (fun j => endpointNode k n j hk hn) p n)

private theorem endpointNode_zero_eqv
    (k n : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointNode k n 0 hk hn ≈ 0 := by
  show (endpointNode k n 0 hk hn).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((endpointNode k n 0 hk hn).den : Int)
  unfold endpointNode gridNode
  simp only [Q'.mkPos_num, zero_num_cast, zero_den_cast,
    Nat.mul_zero, Int.ofNat_zero, Int.zero_mul]

private theorem rgQpow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ p,
    qpow a p ≈ qpow b p
  | 0 => Q'.eqv_refl 1
  | p + 1 => by
      refine Q'.eqv_trans _
        (qpow b p * a) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (rgQpow_eqv_congr h p)
      · exact Q'.mul_eqv_congr_left _ _ _ h

private theorem qpow_zero_positive (p : Nat) :
    qpow (0 : Q') (p + 1) ≈ 0 := by
  change (qpow (0 : Q') p * 0) ≈ 0
  exact Q'.mul_zero_eqv _

private theorem endpointNode_zero_power_eqv
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    qpow (endpointNode k n 0 hk hn) (p + 1) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (rgQpow_eqv_congr
      (endpointNode_zero_eqv k n hk hn) (p + 1)) ?_
  exact qpow_zero_positive p

private theorem endpointNode_terminal_power_eqv
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    qpow (endpointNode k n n hk hn) (p + 1) ≈
      qpow (rat 1 k hk) (p + 1) :=
  rgQpow_eqv_congr
    (gridNode_endpoint_eqv 1 k n hk hn) (p + 1)

/-- The telescoping increment sum is exactly the formal monomial integral at
the rational endpoint, independently of the mesh resolution. -/
theorem endpointMonomialIncrementSum_eq_value
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialIncrementSum k n p hk hn ≈
      endpointMonomialValue k p hk := by
  refine Q'.eqv_trans _ _ _
    (endpointMonomialIncrementSum_telescope k n p hk hn) ?_
  unfold monomialIncrement endpointMonomialValue
  have htop := endpointNode_terminal_power_eqv k n p hk hn
  have hzero := endpointNode_zero_power_eqv k n p hk hn
  have hinner :
      qpow (endpointNode k n n hk hn) (p + 1) +
          -qpow (endpointNode k n 0 hk hn) (p + 1) ≈
        qpow (rat 1 k hk) (p + 1) := by
    refine Q'.eqv_trans _
      (qpow (rat 1 k hk) (p + 1) + -(0 : Q')) _ ?_ ?_
    · exact QPoly.q_add_congr htop (Q'.neg_eqv_congr _ _ hzero)
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact Q'.mul_eqv_congr_left 2 _ _
    (Q'.mul_eqv_congr_left (Q'.invSucc p) _ _ hinner)

/-- Resolution-uniform finite monomial sandwich around the exact formal
endpoint integral. -/
theorem endpointMonomial_finite_sandwich
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialLeftSum k n p hk hn ≤ endpointMonomialValue k p hk ∧
      endpointMonomialValue k p hk ≤ endpointMonomialRightSum k n p hk hn := by
  constructor
  · exact Q'.le_trans' _ _ _
      (endpointMonomialLeftSum_le_incrementSum k n p hk hn)
      (Q'.le_of_eqv (endpointMonomialIncrementSum_eq_value k n p hk hn))
  · exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (endpointMonomialIncrementSum_eq_value k n p hk hn))
      (endpointMonomialIncrementSum_le_rightSum k n p hk hn)

private theorem endpoint_rat_le_one (k : Nat) (hk : 0 < k) :
    rat 1 k hk ≤ (1 : Q') := by
  show (rat 1 k hk).num * ((1 : Q').den : Int) ≤
    (1 : Q').num * ((rat 1 k hk).den : Int)
  unfold rat
  rw [Q'.mkPos_num, Q'.mkPos_den, one_num_cast, one_den_cast,
    Int.mul_one, Int.one_mul]
  exact_mod_cast hk

/-- The shifted right monomial sum is at most one mesh above the left sum,
uniformly in the degree. -/
theorem endpointMonomialRightSum_le_left_add_mesh
    (k n p : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointMonomialRightSum k n p hk hn ≤
      endpointMonomialLeftSum k n p hk hn + scaledMesh 1 k n hk hn := by
  let f : Nat → Q' := fun j =>
    scaledMesh 1 k n hk hn * qpow (endpointNode k n j hk hn) p
  have hpeel := finSum_peel_left f n
  have hbase :
      endpointMonomialLeftSum k n p hk hn + f n ≈
        f 0 + endpointMonomialRightSum k n p hk hn := by
    unfold endpointMonomialLeftSum endpointMonomialRightSum
    change (finSum f n + f n) ≈
      (f 0 + finSum (fun j => f (j + 1)) n)
    rw [← finSum_succ]
    exact hpeel
  have hnode0 : (0 : Q') ≤ endpointNode k n 0 hk hn :=
    gridNode_nonneg 1 k n 0 hk hn
  have hf0 : (0 : Q') ≤ f 0 :=
    Q'.mul_nonneg _ _ (scaledMesh_nonnegative k n hk hn)
      (qpow_nonneg _ hnode0 p)
  have hrightFront : endpointMonomialRightSum k n p hk hn ≤
      f 0 + endpointMonomialRightSum k n p hk hn := by
    refine Q'.le_trans' _
      (endpointMonomialRightSum k n p hk hn + f 0) _ ?_ ?_
    · exact Q'.add_le_self_of_nonneg _ _ hf0
    · exact Q'.le_of_eqv (Q'.add_comm_eqv _ _)
  have htoLeft :
      f 0 + endpointMonomialRightSum k n p hk hn ≤
        endpointMonomialLeftSum k n p hk hn + f n :=
    Q'.ge_of_eqv hbase
  have hnodeN0 : (0 : Q') ≤ endpointNode k n n hk hn :=
    gridNode_nonneg 1 k n n hk hn
  have hnodeNEnd : endpointNode k n n hk hn ≤ rat 1 k hk :=
    Q'.le_of_eqv (gridNode_endpoint_eqv 1 k n hk hn)
  have hnodeN1 : endpointNode k n n hk hn ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hnodeNEnd (endpoint_rat_le_one k hk)
  have hpow : qpow (endpointNode k n n hk hn) p ≤ (1 : Q') :=
    qpow_le_one hnodeN0 hnodeN1 p
  have hfn : f n ≤ scaledMesh 1 k n hk hn := by
    unfold f
    refine Q'.le_trans' _
      (scaledMesh 1 k n hk hn * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
        (scaledMesh_nonnegative k n hk hn)
    · exact Q'.le_of_eqv (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ hrightFront
    (Q'.le_trans' _ _ _ htoLeft
      (Q'.add_le_add_left _ _ _ hfn))

/-! ## Constructive-real monomial convergence -/

def endpointMonomialSeq (k p : Nat) (hk : 0 < k) : Nat → CReal :=
  fun N => CReal.ofQ'
    (endpointMonomialLeftSum k (N + 1) p hk (Nat.succ_pos N))

/-- Uniform left endpoint monomial sums converge constructively to the exact
formal integral.  The explicit stage `2 * epsilon.den` works for every degree. -/
theorem endpointMonomialSeq_converges
    (k p : Nat) (hk : 0 < k) :
    CReal.ConvergesTo (endpointMonomialSeq k p hk)
      (CReal.ofQ' (endpointMonomialValue k p hk)) := by
  intro epsilon hepsilon
  refine ⟨2 * epsilon.den, fun N hN => ⟨0, fun _ _ => ?_⟩⟩
  let hn : 0 < N + 1 := Nat.succ_pos N
  let left := endpointMonomialLeftSum k (N + 1) p hk hn
  let right := endpointMonomialRightSum k (N + 1) p hk hn
  let value := endpointMonomialValue k p hk
  have hsandwich := endpointMonomial_finite_sandwich
    k (N + 1) p hk hn
  have hgap := endpointMonomialRightSum_le_left_add_mesh
    k (N + 1) p hk hn
  have hmeshNat : 2 * 1 * epsilon.den ≤ k * (N + 1) := by
    have hk1 : 1 ≤ k := hk
    have hstage : 2 * epsilon.den ≤ N := hN
    have hNk : N + 1 ≤ k * (N + 1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N + 1) hk1
    omega
  have hmesh : scaledMesh 1 k (N + 1) hk hn ≤ epsilon :=
    scaledMesh_succ_le hepsilon 1 k N hk hmeshNat
  have hright : right ≤ left + epsilon :=
    Q'.le_trans' _ _ _ hgap (Q'.add_le_add_left _ _ _ hmesh)
  have hvalueUpper : value ≤ left + epsilon :=
    Q'.le_trans' _ _ _ hsandwich.2 hright
  have hleftUpper : left ≤ value + epsilon :=
    Q'.le_trans' _ _ _ hsandwich.1
      (Q'.add_le_self_of_nonneg value epsilon (Q'.le_of_lt hepsilon))
  exact ⟨hleftUpper, hvalueUpper⟩

/-- At even degree `2m`, the formal monomial value is exactly twice the
project's arctangent magnitude term. -/
theorem endpointMonomialValue_even_eq_two_bMag
    (k m : Nat) (hk : 0 < k) :
    endpointMonomialValue k (2 * m) hk ≈
      (2 : Q') * Pi.bMag k hk m := by
  have hpow :
      qpow (rat 1 k hk) (2 * m + 1) ≈
        Q'.mkPos 1 (k ^ (2 * m + 1)) (Pi.nat_pow_pos hk (2 * m + 1)) := by
    refine Q'.eqv_trans _ _ _
      (rgQpow_eqv_pow (rat 1 k hk) (2 * m + 1)) ?_
    simpa [rat] using Pi.mkPosOne_pow_eqv k hk (2 * m + 1)
  have hinner :
      Q'.invSucc (2 * m) * qpow (rat 1 k hk) (2 * m + 1) ≈
        Pi.bMag k hk m := by
    refine Q'.eqv_trans _
      (Q'.invSucc (2 * m) *
        Q'.mkPos 1 (k ^ (2 * m + 1))
          (Pi.nat_pow_pos hk (2 * m + 1))) _
      (Q'.mul_eqv_congr_left _ _ _ hpow) ?_
    show (Q'.invSucc (2 * m) *
        Q'.mkPos 1 (k ^ (2 * m + 1))
          (Pi.nat_pow_pos hk (2 * m + 1))).num *
        ((Pi.bMag k hk m).den : Int) =
      (Pi.bMag k hk m).num *
        ((Q'.invSucc (2 * m) *
          Q'.mkPos 1 (k ^ (2 * m + 1))
            (Pi.nat_pow_pos hk (2 * m + 1))).den : Int)
    unfold Q'.invSucc Pi.bMag Pi.magDen
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
    push_cast
    ac_rfl
  unfold endpointMonomialValue
  exact Q'.mul_eqv_congr_left 2 _ _ hinner

#print axioms mixedPowSum_factor
#print axioms mixedPowSum_lower
#print axioms mixedPowSum_upper
#print axioms leftRectangle_le_increment
#print axioms increment_le_rightRectangle
#print axioms finSum_monomialIncrement_telescope
#print axioms endpointMonomialLeftSum_le_incrementSum
#print axioms endpointMonomialIncrementSum_le_rightSum
#print axioms endpointMonomialIncrementSum_telescope
#print axioms endpointMonomialIncrementSum_eq_value
#print axioms endpointMonomial_finite_sandwich
#print axioms endpointMonomialRightSum_le_left_add_mesh
#print axioms endpointMonomialSeq_converges
#print axioms endpointMonomialValue_even_eq_two_bMag

end YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann
