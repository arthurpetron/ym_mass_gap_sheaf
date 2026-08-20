/-
Type-level approximation-index moduli for the legacy constructive real `CReal`.

`CReal.cauchy` predates the repository's Rule-8 requirement that recoverable
moduli live in `Type`, so its cutoff is stored under a propositional
existential.  This file does not try to extract that cutoff.  Instead it gives
an explicit data record and constructive combinators for the pointwise
operations used by exact physical logarithmic rates: constants, negation,
addition, and multiplication on the right by a nonnegative rational constant.

The rational-scaling cutoff is completely computable.  At tolerance `epsilon`
it asks the input for tolerance

  epsilon * 1 / (q.num.toNat + 1),

and `ExpNeg.mul_le_of_mul_invSucc_toNat` proves that multiplication by
`q >= 0` returns an error at most `epsilon`.

No modulus is extracted from `Prop`; no classical principle is used.
-/

import YMGap.Constructive.CRealAdd
import YMGap.Constructive.ExpNeg

namespace YMGap.Constructive

namespace CReal

/-- A Type-level approximation-index modulus for one legacy `CReal`.

The two inequalities are stated in the same order as `CReal.cauchy`, but the
stage is data and can therefore be composed into later limit constructions. -/
structure InnerRegularity (x : CReal) : Type where
  rate : Q' -> Nat
  regular : forall epsilon : Q', (0 : Q') < epsilon -> forall p q : Nat,
    rate epsilon <= p -> rate epsilon <= q ->
      x.approx p <= x.approx q + epsilon /\
      x.approx q <= x.approx p + epsilon

namespace InnerRegularity

/-- Constant constructive reals have the zero inner cutoff. -/
def ofQ' (q : Q') : InnerRegularity (CReal.ofQ' q) where
  rate _ := 0
  regular := by
    intro epsilon hepsilon p r _ _
    have hnonnegative : (0 : Q') <= epsilon := Q'.le_of_lt hepsilon
    exact
      ⟨Q'.add_le_self_of_nonneg q epsilon hnonnegative,
       Q'.add_le_self_of_nonneg q epsilon hnonnegative⟩

/-- Pointwise negation preserves an explicit inner modulus. -/
def neg {x : CReal} (X : InnerRegularity x) :
    InnerRegularity (CReal.neg x) where
  rate := X.rate
  regular := by
    intro epsilon hepsilon p q hp hq
    obtain ⟨hforward, hbackward⟩ := X.regular epsilon hepsilon p q hp hq
    exact
      ⟨Q'.neg_le_neg_add hbackward,
       Q'.neg_le_neg_add hforward⟩

/-- Pointwise addition composes explicit inner moduli by splitting the target
tolerance in half and taking the maximum of the two input stages. -/
def add {x y : CReal} (X : InnerRegularity x) (Y : InnerRegularity y) :
    InnerRegularity (CReal.add x y) where
  rate epsilon := max (X.rate (HalfPow.half * epsilon))
    (Y.rate (HalfPow.half * epsilon))
  regular := by
    intro epsilon hepsilon p q hp hq
    have hhalf : (0 : Q') < HalfPow.half * epsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hXp : X.rate (HalfPow.half * epsilon) <= p :=
      Nat.le_trans (Nat.le_max_left _ _) hp
    have hXq : X.rate (HalfPow.half * epsilon) <= q :=
      Nat.le_trans (Nat.le_max_left _ _) hq
    have hYp : Y.rate (HalfPow.half * epsilon) <= p :=
      Nat.le_trans (Nat.le_max_right _ _) hp
    have hYq : Y.rate (HalfPow.half * epsilon) <= q :=
      Nat.le_trans (Nat.le_max_right _ _) hq
    obtain ⟨hxForward, hxBackward⟩ :=
      X.regular (HalfPow.half * epsilon) hhalf p q hXp hXq
    obtain ⟨hyForward, hyBackward⟩ :=
      Y.regular (HalfPow.half * epsilon) hhalf p q hYp hYq
    have combine : forall xp xq yp yq : Q',
        xp <= xq + HalfPow.half * epsilon ->
        yp <= yq + HalfPow.half * epsilon ->
        xp + yp <= (xq + yq) + epsilon := by
      intro xp xq yp yq hx hy
      have hsum : xp + yp <=
          (xq + HalfPow.half * epsilon) +
            (yq + HalfPow.half * epsilon) :=
        Q'.add_le_add hx hy
      have hregroup :
          ((xq + HalfPow.half * epsilon) +
              (yq + HalfPow.half * epsilon)).eqv
            ((xq + yq) +
              (HalfPow.half * epsilon + HalfPow.half * epsilon)) :=
        Q'.regroup xq yq (HalfPow.half * epsilon)
      have hhalves :
          ((xq + yq) +
              (HalfPow.half * epsilon + HalfPow.half * epsilon)).eqv
            ((xq + yq) + epsilon) :=
        Q'.add_eqv_congr_left (xq + yq)
          (HalfPow.half * epsilon + HalfPow.half * epsilon) epsilon
          (ExpNeg.two_halves epsilon)
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
          (Q'.le_of_eqv hhalves))
    exact
      ⟨combine (x.approx p) (x.approx q) (y.approx p) (y.approx q)
          hxForward hyForward,
       combine (x.approx q) (x.approx p) (y.approx q) (y.approx p)
          hxBackward hyBackward⟩

/-- The computable input tolerance used when scaling by a nonnegative rational
constant. -/
def scaleTolerance (q epsilon : Q') : Q' :=
  epsilon * Q'.invSucc q.num.toNat

/-- The scaling tolerance is positive whenever the requested tolerance is. -/
theorem scaleTolerance_pos (q epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < scaleTolerance q epsilon := by
  show (0 : Int) * ((scaleTolerance q epsilon).den : Int) <
    (scaleTolerance q epsilon).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  show (0 : Int) < epsilon.num * (Q'.invSucc q.num.toNat).num * 1
  rw [Q'.invSucc_num, Int.mul_one, Int.mul_one]
  exact CReal.num_pos_of_pos hepsilon

/-- Multiplication by a nonnegative rational sends the computed scaling
tolerance below the requested tolerance. -/
theorem mul_scaleTolerance_le (q epsilon : Q') (hq : (0 : Q') <= q)
    (hepsilon : (0 : Q') < epsilon) :
    q * scaleTolerance q epsilon <= epsilon := by
  exact ExpNeg.mul_le_of_mul_invSucc_toNat q epsilon hq (Q'.le_of_lt hepsilon)

/-- Multiplication on the right by a nonnegative rational constant preserves
Type-level inner regularity with a computed rescaled tolerance. -/
def scaleRight {x : CReal} (X : InnerRegularity x) (q : Q')
    (hq : (0 : Q') <= q) :
    InnerRegularity (CReal.mul x (CReal.ofQ' q)) where
  rate epsilon := X.rate (scaleTolerance q epsilon)
  regular := by
    intro epsilon hepsilon p r hp hr
    have hscaledPositive : (0 : Q') < scaleTolerance q epsilon :=
      scaleTolerance_pos q epsilon hepsilon
    obtain ⟨hforward, hbackward⟩ :=
      X.regular (scaleTolerance q epsilon) hscaledPositive p r hp hr
    have hscaled : q * scaleTolerance q epsilon <= epsilon :=
      mul_scaleTolerance_le q epsilon hq hepsilon
    have hscaledComm : scaleTolerance q epsilon * q <= epsilon :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv
        (Q'.mul_comm_eqv (scaleTolerance q epsilon) q)) hscaled
    have scaleBound : forall a b : Q',
        a <= b + scaleTolerance q epsilon ->
        a * q <= b * q + epsilon := by
      intro a b hab
      have hmul : a * q <= (b + scaleTolerance q epsilon) * q :=
        Q'.mul_le_mul_of_nonneg_right a
          (b + scaleTolerance q epsilon) q hab hq
      have hdistribute : ((b + scaleTolerance q epsilon) * q).eqv
          (b * q + scaleTolerance q epsilon * q) :=
        ExpNeg.add_mul_eqv b (scaleTolerance q epsilon) q
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdistribute)
          (Q'.add_le_add_left (b * q)
            (scaleTolerance q epsilon * q) epsilon hscaledComm))
    exact
      ⟨scaleBound (x.approx p) (x.approx r) hforward,
       scaleBound (x.approx r) (x.approx p) hbackward⟩

/-- Multiplication on the left by a nonnegative rational constant preserves
Type-level inner regularity with the same computed rescaled tolerance. -/
def scaleLeft {x : CReal} (X : InnerRegularity x) (q : Q')
    (hq : (0 : Q') <= q) :
    InnerRegularity (CReal.mul (CReal.ofQ' q) x) where
  rate epsilon := X.rate (scaleTolerance q epsilon)
  regular := by
    intro epsilon hepsilon p r hp hr
    have hscaledPositive : (0 : Q') < scaleTolerance q epsilon :=
      scaleTolerance_pos q epsilon hepsilon
    obtain ⟨hforward, hbackward⟩ :=
      X.regular (scaleTolerance q epsilon) hscaledPositive p r hp hr
    have hscaled : q * scaleTolerance q epsilon <= epsilon :=
      mul_scaleTolerance_le q epsilon hq hepsilon
    have scaleBound : forall a b : Q',
        a <= b + scaleTolerance q epsilon ->
        q * a <= q * b + epsilon := by
      intro a b hab
      have hmul : q * a <= q * (b + scaleTolerance q epsilon) :=
        Q'.mul_le_mul_of_nonneg_left a
          (b + scaleTolerance q epsilon) q hab hq
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.mul_add_eqv q b (scaleTolerance q epsilon)))
          (Q'.add_le_add_left (q * b)
            (q * scaleTolerance q epsilon) epsilon hscaled))
    exact
      ⟨scaleBound (x.approx p) (x.approx r) hforward,
       scaleBound (x.approx r) (x.approx p) hbackward⟩

end InnerRegularity

end CReal

end YMGap.Constructive

#print axioms YMGap.Constructive.CReal.InnerRegularity.ofQ'
#print axioms YMGap.Constructive.CReal.InnerRegularity.neg
#print axioms YMGap.Constructive.CReal.InnerRegularity.add
#print axioms YMGap.Constructive.CReal.InnerRegularity.scaleTolerance_pos
#print axioms YMGap.Constructive.CReal.InnerRegularity.mul_scaleTolerance_le
#print axioms YMGap.Constructive.CReal.InnerRegularity.scaleRight
#print axioms YMGap.Constructive.CReal.InnerRegularity.scaleLeft
