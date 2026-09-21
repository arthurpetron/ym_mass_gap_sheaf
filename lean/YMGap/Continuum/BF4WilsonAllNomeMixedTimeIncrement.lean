/-
# Mixed time increments in the SAME original Wilson state

Ordinary positivity, not a reflected-pairing substitution, bounds the square
of a mixed increment by the product of the two actual diagonal increments.
The existing linear-in-lag nome bounds therefore control every off-diagonal
entry for two fixed source loops. An exact signed two-loop expansion retains
the cross term before any inequality is used.

The explicit budget depends on nome, lag and both loop lengths, but not on
width. Each width still has its own original state. There is no spatial
separation decay, coefficient-l2 family estimate, changing-spacing observable
identification, relative variance bound or continuum survival conclusion.
-/

import YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz
import YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (includedLoop_edges_active)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

attribute [local irreducible] originalJointLimit baseLinks

/-- The signed cross term is integrated against the same original action
and partition as both diagonal time increments. -/
def mixedTimeIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (.mul (timeDifference a n) (timeDifference b n))
    ⟨(timeSquare_within a n).1, (timeSquare_within b n).1⟩

theorem mixedTimeIncrement_diagonal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a : SourceLoop width) (n : Nat) :
    mixedTimeIncrement hw0 hw1 a a n = timeIncrement hw0 hw1 a n := rfl

/-- Positive semidefiniteness of the ordinary two-increment Gram matrix. -/
theorem mixedTimeIncrement_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (n : Nat) :
    leEv (mul (mixedTimeIncrement hw0 hw1 a b n) (mixedTimeIncrement hw0 hw1 a b n))
      (mul (timeIncrement hw0 hw1 a n) (timeIncrement hw0 hw1 b n)) :=
  joint_cauchySchwarz hw0 hw1 n (timeDifference a n) (timeDifference b n)
    (timeSquare_within a n).1 (timeSquare_within b n).1

/-- The already proved diagonal budget, made explicit as rational data. -/
def incrementBudget (w : Q') (n length : Nat) : Q' :=
  Q'.ofNat n * (24 * (Q'.ofNat length * Q'.ofNat length) * (1 + -w))

theorem incrementBudget_nonnegative {w : Q'} (hw1 : w < (1 : Q')) (n length : Nat) :
    (0 : Q') ≤ incrementBudget w n length :=
  Q'.mul_nonneg _ _ (Q'.ofNat_nonneg n)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _)))
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))

/-- No sign is assigned to the mixed term. Its SQUARE is bounded by the
product of explicit budgets, hence quadratically in the nome defect. -/
theorem mixedTimeIncrement_squared_nome_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width)
    (ha : ∀ e, e ∈ a.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (hb : ∀ e, e ∈ b.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (n : Nat) :
    leEv (mul (mixedTimeIncrement hw0 hw1 a b n) (mixedTimeIncrement hw0 hw1 a b n))
      (ofQ' (incrementBudget w n a.edges.length * incrementBudget w n b.edges.length)) := by
  have h1 := leEv_mul_nonneg_left (timeIncrement_nonnegative hw0 hw1 a n)
    (timeIncrement_nome_bound hw0 hw1 b hb n)
  have h2 := leEv_smul_nonneg (incrementBudget_nonnegative hw1 n b.edges.length)
    (timeIncrement_nome_bound hw0 hw1 a ha n)
  have hcomm : Equiv
      (mul (timeIncrement hw0 hw1 a n) (ofQ' (incrementBudget w n b.edges.length)))
      (mul (ofQ' (incrementBudget w n b.edges.length)) (timeIncrement hw0 hw1 a n)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv _ _)
  exact leEv_trans (mixedTimeIncrement_cauchySchwarz hw0 hw1 a b n)
    (leEv_trans h1 (leEv_trans (leEv_of_equiv hcomm)
      (leEv_trans h2 (leEv_of_equiv
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv _ _))))))

/-- Strict padding proves both active-link premises. No equality between
the original states at distinct widths is asserted. -/
theorem padded_mixedTimeIncrement_squared_nome_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (a b : SourceLoop base) (n : Nat) :
    leEv
      (mul (mixedTimeIncrement hw0 hw1
          (recenterLoop (space := 0) (by omega : base+0 ≤ width) a)
          (recenterLoop (space := 0) (by omega : base+0 ≤ width) b) n)
        (mixedTimeIncrement hw0 hw1
          (recenterLoop (space := 0) (by omega : base+0 ≤ width) a)
          (recenterLoop (space := 0) (by omega : base+0 ≤ width) b) n))
      (ofQ' (incrementBudget w n a.edges.length * incrementBudget w n b.edges.length)) := by
  have h := mixedTimeIncrement_squared_nome_bound hw0 hw1
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) a)
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) b)
    (includedLoop_edges_active hwidth a) (includedLoop_edges_active hwidth b) n
  rw [includeLoop_edges (Nat.le_of_lt hwidth) a, includeLoop_edges (Nat.le_of_lt hwidth) b] at h
  exact h

private theorem joint_scaled_product {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (p q : WindowExpression width)
    (hp : Within L p) (hq : Within L q) (c d : Q') :
    Equiv (originalJointLimit hw0 hw1 L (.mul (.smul c p) (.smul d q)) ⟨hp,hq⟩)
      (mul (ofQ' (c*d)) (originalJointLimit hw0 hw1 L (.mul p q) ⟨hp,hq⟩)) :=
  (joint_congr hw0 hw1 L (.mul (.smul c p) (.smul d q))
    (.smul (c*d) (.mul p q)) ⟨hp,hq⟩ ⟨hp,hq⟩
    ((RatPolyCoeffEqv.polyMul_smul_left c _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right d _ _).smul c).trans
        (RatPolyCoeffEqv.smul_assoc c d _)))).trans
    (joint_smul hw0 hw1 L (.mul p q) ⟨hp,hq⟩ (c*d))

/-- Literal signed sum of two time differences, in the existing Wilson syntax. -/
def combinedDifference {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    WindowExpression width :=
  .add (.smul c (timeDifference a n)) (.smul d (timeDifference b n))

theorem combinedDifference_within {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    Within n (combinedDifference a b c d n) :=
  ⟨(timeSquare_within a n).1, (timeSquare_within b n).1⟩

/-- The squared increment of a signed combination, not a sum of separate
absolute-value budgets. All cross terms remain in the original functional. -/
def combinedTimeIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n
    (.mul (combinedDifference a b c d n) (combinedDifference a b c d n))
    ⟨combinedDifference_within a b c d n, combinedDifference_within a b c d n⟩

theorem combinedTimeIncrement_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    leEv (ofQ' 0) (combinedTimeIncrement hw0 hw1 a b c d n) :=
  joint_square_nonnegative hw0 hw1 n _ (combinedDifference_within a b c d n)

/-- Exact Gram expansion with arbitrary signed rational coefficients.
The mixed term is neither dropped nor assigned a favorable sign. -/
theorem combinedTimeIncrement_expand {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    Equiv (combinedTimeIncrement hw0 hw1 a b c d n)
      (add (add (mul (ofQ' (c*c)) (timeIncrement hw0 hw1 a n))
        (mul (ofQ' (2*c*d)) (mixedTimeIncrement hw0 hw1 a b n)))
        (mul (ofQ' (d*d)) (timeIncrement hw0 hw1 b n))) := by
  let p := timeDifference a n
  let q := timeDifference b n
  have hp : Within n p := (timeSquare_within a n).1
  have hq : Within n q := (timeSquare_within b n).1
  let sp : WindowExpression width := .smul c p
  let tq : WindowExpression width := .smul d q
  let e : WindowExpression width :=
    .add (.add (.mul sp sp) (.mul sp tq)) (.add (.mul tq sp) (.mul tq tq))
  have he : Within n e := ⟨⟨⟨hp,hp⟩,⟨hp,hq⟩⟩,⟨⟨hq,hp⟩,⟨hq,hq⟩⟩⟩
  have hpoly : RatPolyCoeffEqv
      (sourcePolynomial (.mul (combinedDifference a b c d n) (combinedDifference a b c d n)))
      (sourcePolynomial e) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 1)))
        (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => sourcePolynomial sp | _ => sourcePolynomial tq)
  have hswap : Equiv (originalJointLimit hw0 hw1 n (.mul q p) ⟨hq,hp⟩)
      (originalJointLimit hw0 hw1 n (.mul p q) ⟨hp,hq⟩) :=
    joint_congr hw0 hw1 n (.mul q p) (.mul p q) ⟨hq,hp⟩ ⟨hp,hq⟩ (RatPolyCoeffEqv.mul_comm _ _)
  have hqp := (joint_scaled_product hw0 hw1 n q p hq hp d c).trans
    (Pivot2.mul_congr_right hswap)
  have hexp := (joint_congr hw0 hw1 n
    (.mul (combinedDifference a b c d n) (combinedDifference a b c d n)) e
    ⟨combinedDifference_within a b c d n, combinedDifference_within a b c d n⟩ he hpoly).trans
    ((joint_add hw0 hw1 n _ _ he.1 he.2).trans
      (equiv_add (joint_add hw0 hw1 n _ _ he.1.1 he.1.2)
        (joint_add hw0 hw1 n _ _ he.2.1 he.2.2)))
  have hterms := equiv_add
    (equiv_add (joint_scaled_product hw0 hw1 n p p hp hp c c)
      (joint_scaled_product hw0 hw1 n p q hp hq c d))
    (equiv_add hqp (joint_scaled_product hw0 hw1 n q q hq hq d d))
  exact hexp.trans (hterms.trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.var 3)))
        (.add (.mul (.mul (.var 1) (.var 0)) (.var 3))
          (.mul (.mul (.var 1) (.var 1)) (.var 4))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
      (fun | 0 => c | 1 => d | 2 => (timeIncrement hw0 hw1 a n).approx k
           | 3 => (mixedTimeIncrement hw0 hw1 a b n).approx k
           | _ => (timeIncrement hw0 hw1 b n).approx k))))

/-- Exact cancellation regression: opposite coefficients of the SAME loop
produce zero, not a positive sum of separate diagonal costs. -/
theorem combinedTimeIncrement_cancel {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a : SourceLoop width) (c : Q') (n : Nat) :
    Equiv (combinedTimeIncrement hw0 hw1 a a c (-c) n) (ofQ' 0) :=
  (combinedTimeIncrement_expand hw0 hw1 a a c (-c) n).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
          (.mul (.mul (.mul (.const 2) (.var 0)) (.neg (.var 0))) (.var 1)))
          (.mul (.mul (.neg (.var 0)) (.neg (.var 0))) (.var 1)))
        (.const 0) (by decide)
        (fun | 0 => c | _ => (timeIncrement hw0 hw1 a n).approx k)))

end YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement

#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.mixedTimeIncrement_diagonal
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.mixedTimeIncrement_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.incrementBudget_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.mixedTimeIncrement_squared_nome_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.padded_mixedTimeIncrement_squared_nome_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.combinedDifference_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.combinedTimeIncrement_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.combinedTimeIncrement_expand
#print axioms YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement.combinedTimeIncrement_cancel
