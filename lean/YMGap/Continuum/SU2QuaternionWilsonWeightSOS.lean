/-
# Exact sum-of-squares form of the retained quaternion Wilson kernel

On two unit rational quaternions, the retained Wilson kernel has the exact
identity

  1 + (1/2) dot(g,h)
    = 1/2 + (1/4) sum_i (g_i + h_i)^2.

This file proves that identity both as a rational value statement and as an
evaluation identity between the concrete finite-support polynomials built in
`SU2QuaternionPolynomialHaarCarrier`.  Hence the retained kernel is genuinely
pointwise nonnegative on `S^3 x S^3`; it is not merely a signed character
truncation.

The result sharpens the next analytic residual.  To obtain the all-degree
`ReferenceWeight.weighted_pos`, it now suffices to prove that the explicit
moment functional is positive on polynomial squares and respects the two
sphere relations.  No positivity assumption is used below.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

namespace YMGap.Continuum.SU2QuaternionWilsonWeightSOS

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

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
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## Polynomial SOS representative -/

def pairCoordinate (i : Nat) : RatPoly :=
  polyAdd (gCoordinate i) (hCoordinate i)

def pairCoordinateSquare (i : Nat) : RatPoly :=
  polyMul (pairCoordinate i) (pairCoordinate i)

def pairSquareSumPolynomial : RatPoly :=
  polyAdd (pairCoordinateSquare 0)
    (polyAdd (pairCoordinateSquare 1)
      (polyAdd (pairCoordinateSquare 2) (pairCoordinateSquare 3)))

/-- `1/2 + (1/4) sum_i (g_i+h_i)^2` as an actual finite-support polynomial. -/
def retainedWeightSOSPolynomial : RatPoly :=
  polyAdd (polySmul coupling polyOne)
    (polySmul quarter pairSquareSumPolynomial)

/-! ## Rational quaternion evaluation -/

def pairCoordinateList (g h : RationalSU2Point) : List Q' :=
  [g.1, g.2.1, g.2.2.1, g.2.2.2,
    h.1, h.2.1, h.2.2.1, h.2.2.2]

def pairEnvironment (g h : RationalSU2Point) (i : Nat) : Q' :=
  (pairCoordinateList g h).getD i 0

def pairSquareSumValue (g h : RationalSU2Point) : Q' :=
  (g.1 + h.1) * (g.1 + h.1) +
    ((g.2.1 + h.2.1) * (g.2.1 + h.2.1) +
      ((g.2.2.1 + h.2.2.1) * (g.2.2.1 + h.2.2.1) +
        (g.2.2.2 + h.2.2.2) * (g.2.2.2 + h.2.2.2)))

def retainedWeightSOSValue (g h : RationalSU2Point) : Q' :=
  coupling + quarter * pairSquareSumValue g h

/-! ### Evaluation homomorphism helpers -/

theorem evalRatPoly_one (rho : Nat → Q') :
    evalRatPoly rho polyOne ≈ 1 := by
  change ((1 : Q') * 1 + 0) ≈ 1
  decide

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

theorem evalRatPoly_var (rho : Nat → Q') (i : Nat) :
    evalRatPoly rho (polyVar i) ≈ rho i := by
  refine Q'.eqv_trans _ (evalMono rho (varMono i)) _ ?_ ?_
  · change (1 * evalMono rho (varMono i) + 0) ≈
      evalMono rho (varMono i)
    ring_qeqv
  · simpa [evalMono] using evalMonoFrom_varMono rho i 0

theorem evalRatPoly_smul (rho : Nat → Q') (c : Q') :
    forall p : RatPoly,
      evalRatPoly rho (polySmul c p) ≈ c * evalRatPoly rho p
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | t :: p => by
      change
        (c * t.2) * evalMono rho t.1 +
            evalRatPoly rho (polySmul c p) ≈
          c * (t.2 * evalMono rho t.1 + evalRatPoly rho p)
      refine Q'.eqv_trans _
        (c * (t.2 * evalMono rho t.1) + c * evalRatPoly rho p) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_assoc_eqv c t.2 (evalMono rho t.1))
          (evalRatPoly_smul rho c p)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv c (t.2 * evalMono rho t.1) (evalRatPoly rho p))

private theorem eval_g0 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (gCoordinate 0) ≈ g.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 0) (Q'.eqv_refl _)

private theorem eval_g1 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (gCoordinate 1) ≈ g.2.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 1) (Q'.eqv_refl _)

private theorem eval_g2 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (gCoordinate 2) ≈ g.2.2.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 2) (Q'.eqv_refl _)

private theorem eval_g3 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (gCoordinate 3) ≈ g.2.2.2 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 3) (Q'.eqv_refl _)

private theorem eval_h0 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (hCoordinate 0) ≈ h.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 4) (Q'.eqv_refl _)

private theorem eval_h1 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (hCoordinate 1) ≈ h.2.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 5) (Q'.eqv_refl _)

private theorem eval_h2 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (hCoordinate 2) ≈ h.2.2.1 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 6) (Q'.eqv_refl _)

private theorem eval_h3 (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) (hCoordinate 3) ≈ h.2.2.2 :=
  Q'.eqv_trans _ _ _ (evalRatPoly_var _ 7) (Q'.eqv_refl _)

private theorem eval_coordinate_mul (g h : RationalSU2Point)
    (i : Nat) (x y : Q')
    (hx : evalRatPoly (pairEnvironment g h) (gCoordinate i) ≈ x)
    (hy : evalRatPoly (pairEnvironment g h) (hCoordinate i) ≈ y) :
    evalRatPoly (pairEnvironment g h)
        (polyMul (gCoordinate i) (hCoordinate i)) ≈ x * y :=
  Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
    (q_mul_congr hx hy)

private theorem eval_relativeDot (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) relativeDot ≈
      relativeClassCoordinate g h := by
  have h0 := eval_coordinate_mul g h 0 g.1 h.1 (eval_g0 g h) (eval_h0 g h)
  have h1 := eval_coordinate_mul g h 1 g.2.1 h.2.1 (eval_g1 g h) (eval_h1 g h)
  have h2 := eval_coordinate_mul g h 2 g.2.2.1 h.2.2.1 (eval_g2 g h) (eval_h2 g h)
  have h3 := eval_coordinate_mul g h 3 g.2.2.2 h.2.2.2 (eval_g3 g h) (eval_h3 g h)
  unfold relativeDot relativeClassCoordinate
  refine Q'.eqv_trans _
    (evalRatPoly (pairEnvironment g h)
        (polyMul (gCoordinate 0) (hCoordinate 0)) +
      evalRatPoly (pairEnvironment g h)
        (polyAdd (polyMul (gCoordinate 1) (hCoordinate 1))
          (polyAdd (polyMul (gCoordinate 2) (hCoordinate 2))
            (polyMul (gCoordinate 3) (hCoordinate 3))))) _
    (evalRatPoly_add _ _ _) ?_
  refine Q'.add_eqv_congr' h0 ?_
  refine Q'.eqv_trans _
    (evalRatPoly (pairEnvironment g h)
        (polyMul (gCoordinate 1) (hCoordinate 1)) +
      evalRatPoly (pairEnvironment g h)
        (polyAdd (polyMul (gCoordinate 2) (hCoordinate 2))
          (polyMul (gCoordinate 3) (hCoordinate 3)))) _
    (evalRatPoly_add _ _ _) ?_
  refine Q'.add_eqv_congr' h1 ?_
  refine Q'.eqv_trans _
    (evalRatPoly (pairEnvironment g h)
        (polyMul (gCoordinate 2) (hCoordinate 2)) +
      evalRatPoly (pairEnvironment g h)
        (polyMul (gCoordinate 3) (hCoordinate 3))) _
    (evalRatPoly_add _ _ _) (Q'.add_eqv_congr' h2 h3)

theorem eval_retainedRelativeWeight (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) retainedRelativeWeight ≈
      1 + coupling * relativeClassCoordinate g h := by
  unfold retainedRelativeWeight relativeFundamentalCharacter
  refine Q'.eqv_trans _
    (evalRatPoly (pairEnvironment g h) polyOne +
      evalRatPoly (pairEnvironment g h)
        (polySmul quarter (polySmul 2 relativeDot))) _
    (evalRatPoly_add _ _ _) ?_
  refine Q'.add_eqv_congr' (evalRatPoly_one _) ?_
  refine Q'.eqv_trans _
    (quarter * evalRatPoly (pairEnvironment g h)
      (polySmul 2 relativeDot)) _
    (evalRatPoly_smul _ quarter _) ?_
  refine Q'.eqv_trans _
    (quarter * (2 * evalRatPoly (pairEnvironment g h) relativeDot)) _
    (Q'.mul_eqv_congr_left quarter _ _
      (evalRatPoly_smul _ 2 _)) ?_
  refine Q'.eqv_trans _
    (quarter * (2 * relativeClassCoordinate g h)) _
    (Q'.mul_eqv_congr_left quarter _ _
      (Q'.mul_eqv_congr_left 2 _ _ (eval_relativeDot g h))) ?_
  unfold quarter coupling
  ring_qeqv

theorem eval_retainedWeightSOSPolynomial (g h : RationalSU2Point) :
    evalRatPoly (pairEnvironment g h) retainedWeightSOSPolynomial ≈
      retainedWeightSOSValue g h := by
  have pairEval (i : Nat) (x y : Q')
      (hx : evalRatPoly (pairEnvironment g h) (gCoordinate i) ≈ x)
      (hy : evalRatPoly (pairEnvironment g h) (hCoordinate i) ≈ y) :
      evalRatPoly (pairEnvironment g h) (pairCoordinateSquare i) ≈
        (x + y) * (x + y) := by
    unfold pairCoordinateSquare pairCoordinate
    refine Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _) ?_
    have hp : evalRatPoly (pairEnvironment g h)
        (polyAdd (gCoordinate i) (hCoordinate i)) ≈ x + y :=
      Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
        (Q'.add_eqv_congr' hx hy)
    exact q_mul_congr hp hp
  have h0 := pairEval 0 g.1 h.1 (eval_g0 g h) (eval_h0 g h)
  have h1 := pairEval 1 g.2.1 h.2.1 (eval_g1 g h) (eval_h1 g h)
  have h2 := pairEval 2 g.2.2.1 h.2.2.1 (eval_g2 g h) (eval_h2 g h)
  have h3 := pairEval 3 g.2.2.2 h.2.2.2 (eval_g3 g h) (eval_h3 g h)
  have hsum : evalRatPoly (pairEnvironment g h) pairSquareSumPolynomial ≈
      pairSquareSumValue g h := by
    unfold pairSquareSumPolynomial pairSquareSumValue
    refine Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _) ?_
    refine Q'.add_eqv_congr' h0 ?_
    refine Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _) ?_
    refine Q'.add_eqv_congr' h1 ?_
    refine Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
      (Q'.add_eqv_congr' h2 h3)
  unfold retainedWeightSOSPolynomial retainedWeightSOSValue
  refine Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_smul _ coupling _)
      (Q'.mul_eqv_congr_left coupling _ _ (evalRatPoly_one _))
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_smul _ quarter _)
      (Q'.mul_eqv_congr_left quarter _ _ hsum)

/-! ## The sphere-quotient identity -/

private def pairSquareExpansionL : RingNormaliser.PolyExpr :=
  let sq (i j : Nat) :=
    RingNormaliser.PolyExpr.mul
      (.add (.var i) (.var j)) (.add (.var i) (.var j))
  .add (sq 0 4) (.add (sq 1 5) (.add (sq 2 6) (sq 3 7)))

private def pairSquareExpansionR : RingNormaliser.PolyExpr :=
  let sq (i : Nat) := RingNormaliser.PolyExpr.mul (.var i) (.var i)
  let dot :=
    RingNormaliser.PolyExpr.add (.mul (.var 0) (.var 4))
      (.add (.mul (.var 1) (.var 5))
        (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))
  .add
    (.add
      (.add (sq 0) (.add (sq 1) (.add (sq 2) (sq 3))))
      (.add (sq 4) (.add (sq 5) (.add (sq 6) (sq 7)))))
    (.mul (.const 2) dot)

private theorem pairSquareExpansion_normal :
    RingNormaliser.normalize pairSquareExpansionL =
      RingNormaliser.normalize pairSquareExpansionR := by decide

theorem pairSquareSum_expansion (g h : RationalSU2Point) :
    pairSquareSumValue g h ≈
      quatNormSq g + quatNormSq h +
        (2 : Q') * relativeClassCoordinate g h := by
  have hp := RingNormaliser.poly_identity_of_normal_eq
    pairSquareExpansionL pairSquareExpansionR pairSquareExpansion_normal
    (fun
      | 0 => g.1
      | 1 => g.2.1
      | 2 => g.2.2.1
      | 3 => g.2.2.2
      | 4 => h.1
      | 5 => h.2.1
      | 6 => h.2.2.1
      | _ => h.2.2.2)
  simpa [pairSquareExpansionL, pairSquareExpansionR, RingNormaliser.eval,
    pairSquareSumValue, quatNormSq, relativeClassCoordinate] using hp

theorem retained_weight_value_eq_sos
    (g h : RationalSU2Point)
    (hg : quatNormSq g ≈ 1) (hh : quatNormSq h ≈ 1) :
    1 + coupling * relativeClassCoordinate g h ≈
      retainedWeightSOSValue g h := by
  have hexpand := pairSquareSum_expansion g h
  have hsphere :
      quatNormSq g + quatNormSq h +
          (2 : Q') * relativeClassCoordinate g h ≈
        1 + 1 + (2 : Q') * relativeClassCoordinate g h :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hg hh) (Q'.eqv_refl _)
  let d := relativeClassCoordinate g h
  have hquarterTwo : quarter * (2 : Q') ≈ coupling := by decide
  have hcouplingTwo : coupling + coupling ≈ (1 : Q') := by decide
  have hsplit :
      quarter * (1 + 1 + (2 : Q') * d) ≈
        coupling + coupling * d := by
    refine Q'.eqv_trans _
      (quarter * (1 + 1) + quarter * ((2 : Q') * d)) _ ?_ ?_
    · exact Q'.mul_add_eqv quarter (1 + 1) ((2 : Q') * d)
    · exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ (quarter * 2) _
          (Q'.mul_eqv_congr_left quarter _ _ (by decide)) hquarterTwo)
        (Q'.eqv_trans _ ((quarter * 2) * d) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv quarter 2 d))
          (Q'.mul_eqv_congr_right _ _ d hquarterTwo))
  refine Q'.eqv_trans _
    (coupling + quarter *
      (1 + 1 + (2 : Q') * relativeClassCoordinate g h)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((coupling + coupling) + coupling * d) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_symm hcouplingTwo) (Q'.eqv_refl _)
    · refine Q'.eqv_trans _
        (coupling + (coupling + coupling * d)) _
        (Q'.add_assoc_eqv coupling coupling (coupling * d)) ?_
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm hsplit)
  · unfold retainedWeightSOSValue
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left quarter _ _
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsphere)
          (Q'.eqv_symm hexpand)))

/-- The actual retained polynomial and its SOS polynomial agree at every pair
of rational unit quaternions. -/
theorem retained_polynomial_eq_sos_on_unit
    (g h : RationalSU2Point)
    (hg : quatNormSq g ≈ 1) (hh : quatNormSq h ≈ 1) :
    evalRatPoly (pairEnvironment g h) retainedRelativeWeight ≈
      evalRatPoly (pairEnvironment g h) retainedWeightSOSPolynomial :=
  Q'.eqv_trans _ _ _ (eval_retainedRelativeWeight g h)
    (Q'.eqv_trans _ _ _ (retained_weight_value_eq_sos g h hg hh)
      (Q'.eqv_symm (eval_retainedWeightSOSPolynomial g h)))

/-! ## Pointwise nonnegativity -/

theorem pairSquareSumValue_nonneg (g h : RationalSU2Point) :
    (0 : Q') ≤ pairSquareSumValue g h := by
  unfold pairSquareSumValue
  exact Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg (g.1 + h.1))
    (Q'.zero_le_add _ _
      (SumOfSquares.q_mul_self_nonneg (g.2.1 + h.2.1))
      (Q'.zero_le_add _ _
        (SumOfSquares.q_mul_self_nonneg (g.2.2.1 + h.2.2.1))
        (SumOfSquares.q_mul_self_nonneg (g.2.2.2 + h.2.2.2))))

theorem retainedWeightSOSValue_nonneg (g h : RationalSU2Point) :
    (0 : Q') ≤ retainedWeightSOSValue g h := by
  unfold retainedWeightSOSValue
  exact Q'.zero_le_add _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (pairSquareSumValue_nonneg g h))

/-- Exact pointwise positivity of the retained Wilson polynomial on
`S^3 x S^3`, obtained from the SOS representative. -/
theorem retainedRelativeWeight_pointwise_nonneg
    (g h : RationalSU2Point)
    (hg : quatNormSq g ≈ 1) (hh : quatNormSq h ≈ 1) :
    (0 : Q') ≤ evalRatPoly (pairEnvironment g h) retainedRelativeWeight := by
  have heq := retained_polynomial_eq_sos_on_unit g h hg hh
  exact Q'.le_trans' _ _ _ (retainedWeightSOSValue_nonneg g h)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_retainedWeightSOSPolynomial g h))
        (Q'.eqv_symm heq)))

end YMGap.Continuum.SU2QuaternionWilsonWeightSOS

#print axioms YMGap.Continuum.SU2QuaternionWilsonWeightSOS.eval_retainedRelativeWeight
#print axioms YMGap.Continuum.SU2QuaternionWilsonWeightSOS.eval_retainedWeightSOSPolynomial
#print axioms YMGap.Continuum.SU2QuaternionWilsonWeightSOS.pairSquareSum_expansion
#print axioms YMGap.Continuum.SU2QuaternionWilsonWeightSOS.retained_polynomial_eq_sos_on_unit
#print axioms YMGap.Continuum.SU2QuaternionWilsonWeightSOS.retainedRelativeWeight_pointwise_nonneg
