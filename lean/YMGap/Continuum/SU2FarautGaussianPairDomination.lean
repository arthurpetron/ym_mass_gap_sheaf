/-
# Constructive Gaussian pair domination for the Faraut image sum

For `0 < a ≤ b`, `0 < t`, and `2t ≤ a²`, the elementary proof that

`b exp (-b²/(4t)) ≤ a exp (-a²/(4t))`

uses only

`(b²-a²)/(4t) ≥ (b-a)/a`

and the Padé/Bernoulli estimate `exp (-x) ≤ 1/(1+x)`.  This module
formalizes the division-free rational core of that argument and packages
the exponent-splitting datum needed by later constructive-real order code.

## Axiom gate

No `Classical.*`, `sorry`, `native_decide`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.CRealExp
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.SU2FarautGaussianPairDomination

open YMGap.Constructive
open YMGap.Constructive.ExpNeg

/-! ## 1. The exact rational gap and its division-free comparison -/

def gaussianPairDenominator (t : Q') : Q' :=
  (Q'.ofNat 2 * t) + (Q'.ofNat 2 * t)

def gaussianPairNumerator (a b : Q') : Q' :=
  (b + -a) * (b + a)

def gaussianPairGap (a b t : Q') (ht : (0 : Q') < t) : Q' :=
  Q'.divPos
    (gaussianPairNumerator a b)
    (gaussianPairDenominator t)
    (by
      unfold gaussianPairDenominator
      have htwo : (0 : Q') < Q'.ofNat 2 := by decide
      have hterm : (0 : Q') < Q'.ofNat 2 * t :=
        Q'.mul_pos htwo ht
      exact Q'.pos_add_nonneg hterm (Q'.le_of_lt hterm))

def gaussianExponent (x t : Q') (ht : (0 : Q') < t) : Q' :=
  Q'.divPos
    (x * x)
    (gaussianPairDenominator t)
    (by
      unfold gaussianPairDenominator
      have htwo : (0 : Q') < Q'.ofNat 2 := by decide
      have hterm : (0 : Q') < Q'.ofNat 2 * t :=
        Q'.mul_pos htwo ht
      exact Q'.pos_add_nonneg hterm (Q'.le_of_lt hterm))

theorem gaussianPairDenominator_pos
    (t : Q') (ht : (0 : Q') < t) :
    (0 : Q') < gaussianPairDenominator t := by
  unfold gaussianPairDenominator
  have htwo : (0 : Q') < Q'.ofNat 2 := by decide
  have hterm : (0 : Q') < Q'.ofNat 2 * t :=
    Q'.mul_pos htwo ht
  exact Q'.pos_add_nonneg hterm (Q'.le_of_lt hterm)

theorem gaussianPairNumerator_nonneg
    {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) :
    (0 : Q') ≤ gaussianPairNumerator a b := by
  unfold gaussianPairNumerator
  exact Q'.mul_nonneg _ _
    (Q'.sub_nonneg_of_le hab)
    (Q'.zero_le_add b a
      (Q'.le_trans' _ _ _ (Q'.le_of_lt ha) hab)
      (Q'.le_of_lt ha))

theorem gaussianPairGap_nonneg
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t) :
    (0 : Q') ≤ gaussianPairGap a b t ht := by
  unfold gaussianPairGap Q'.divPos
  exact Q'.mul_nonneg _ _
    (gaussianPairNumerator_nonneg ha hab)
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (gaussianPairDenominator t)
        (gaussianPairDenominator_pos t ht)))

theorem gaussianExponent_nonneg
    {x t : Q'} (hx : (0 : Q') ≤ x)
    (ht : (0 : Q') < t) :
    (0 : Q') ≤ gaussianExponent x t ht := by
  unfold gaussianExponent Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg x x hx hx)
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (gaussianPairDenominator t)
        (gaussianPairDenominator_pos t ht)))

private theorem square_add_gapNumerator_eqv
    (a b : Q') :
    (a * a + gaussianPairNumerator a b).eqv
      (b * b) := by
  have hn :
      (gaussianPairNumerator a b).eqv
        ((b * b + a * b) +
          (-(a * b) + -(a * a))) := by
    unfold gaussianPairNumerator
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv b (-a) (b + a)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_add_eqv b b a)
        (Q'.mul_add_eqv (-a) b a)) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.add_eqv_congr_left
        (b * b) (b * a) (a * b)
        (Q'.mul_comm_eqv b a)
    · exact Q'.add_eqv_congr'
        (Q'.neg_mul_eqv a b)
        (Q'.neg_mul_eqv a a)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a * a)
      (gaussianPairNumerator a b)
      ((b * b + a * b) +
        (-(a * b) + -(a * a))) hn) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (a * a)
        (b * b + a * b)
        (-(a * b) + -(a * a)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _
      (-(a * b) + -(a * a))
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (a * a) (b * b) (a * b)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      (a * a + b * b) (a * b)
      (-(a * b) + -(a * a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a * a + b * b)
      (a * b + (-(a * b) + -(a * a)))
      (-(a * a)) ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          (a * b) (-(a * b)) (-(a * a)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        (a * b + -(a * b)) 0 (-(a * a))
        (Q'.add_neg_self_eqv (a * b))) ?_
    exact QPoly.q_zero_add_eqv (-(a * a))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (a * a + b * b) (b * b + a * a)
      (-(a * a))
      (Q'.add_comm_eqv (a * a) (b * b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      (b * b) (a * a) (-(a * a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (b * b)
      (a * a + -(a * a)) 0
      (Q'.add_neg_self_eqv (a * a))) ?_
  exact QPoly.q_add_zero_eqv (b * b)

/-- Exact exponent normalization:

`a²/(4t) + (b²-a²)/(4t) ≃ b²/(4t)`,

with the difference written in the factored form
`(b-a)(b+a)`. -/
theorem gaussianExponent_add_gap_eqv
    (a b t : Q') (ht : (0 : Q') < t) :
    (gaussianExponent a t ht +
        gaussianPairGap a b t ht).eqv
      (gaussianExponent b t ht) := by
  unfold gaussianExponent gaussianPairGap Q'.divPos
  let reciprocal :=
    Q'.recipPos
      (gaussianPairDenominator t)
      (gaussianPairDenominator_pos t ht)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_mul_eqv
        (a * a) (gaussianPairNumerator a b)
        reciprocal)) ?_
  exact Q'.mul_eqv_congr_right
    (a * a + gaussianPairNumerator a b)
    (b * b) reciprocal
    (square_add_gapNumerator_eqv a b)

private theorem cancel_add_sub (a b : Q') :
    (a + (b + -a)).eqv b := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (b + -a) (-a + b)
      (Q'.add_comm_eqv b (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (a + -a) 0 b
      (Q'.add_neg_self_eqv a)) ?_
  exact QPoly.q_zero_add_eqv b

private theorem scale_gapNumerator_eqv
    (a b : Q') :
    ((a * gaussianPairNumerator a b)).eqv
      ((b + -a) * (a * (b + a))) := by
  unfold gaussianPairNumerator
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv a (b + -a) (b + a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (a * (b + -a)) ((b + -a) * a) (b + a)
      (Q'.mul_comm_eqv a (b + -a))) ?_
  exact Q'.mul_assoc_eqv (b + -a) a (b + a)

private theorem divPos_scale_eqv
    (a numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    (Q'.divPos (a * numerator) denominator hdenominator).eqv
      (a * Q'.divPos numerator denominator hdenominator) := by
  unfold Q'.divPos
  exact Q'.mul_assoc_eqv a numerator
    (Q'.recipPos denominator hdenominator)

/-- The division-free heart of Gaussian monotonicity:

`b - a ≤ a · ((b-a)(b+a)/(4t))`.

The proof first obtains `4t ≤ a(b+a)` from
`2t ≤ a² ≤ ab`, multiplies by the nonnegative `b-a`, and only then
introduces the positive-denominator quotient. -/
theorem sub_le_a_mul_gaussianPairGap
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a) :
    b + -a ≤ a * gaussianPairGap a b t ht := by
  have ha0 : (0 : Q') ≤ a := Q'.le_of_lt ha
  have hb0 : (0 : Q') ≤ b :=
    Q'.le_trans' _ _ _ ha0 hab
  have hdelta0 : (0 : Q') ≤ b + -a :=
    Q'.sub_nonneg_of_le hab
  have haa_le_hab : a * a ≤ a * b :=
    Q'.mul_le_mul_of_nonneg_left a b a hab ha0
  have hdouble :
      (Q'.ofNat 2 * t) + (Q'.ofNat 2 * t) ≤
        (a * a) + (a * a) :=
    Q'.add_le_add hscale hscale
  have hreplace :
      (a * a) + (a * a) ≤ (a * b) + (a * a) :=
    Q'.add_le_add_right (a * a) (a * b) (a * a)
      haa_le_hab
  have hdenScale :
      gaussianPairDenominator t ≤ a * (b + a) := by
    refine Q'.le_trans' _ _ _ hdouble ?_
    refine Q'.le_trans' _ _ _ hreplace ?_
    exact Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_add_eqv a b a))
  have hmul :
      (b + -a) * gaussianPairDenominator t ≤
        (b + -a) * (a * (b + a)) :=
    Q'.mul_le_mul_of_nonneg_left
      (gaussianPairDenominator t) (a * (b + a))
      (b + -a) hdenScale hdelta0
  have hmul' :
      (b + -a) * gaussianPairDenominator t ≤
        a * gaussianPairNumerator a b := by
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.eqv_symm (scale_gapNumerator_eqv a b)))
  have hquot :
      b + -a ≤
        Q'.divPos
          (a * gaussianPairNumerator a b)
          (gaussianPairDenominator t)
          (gaussianPairDenominator_pos t ht) :=
    Q'.le_divPos_of_mul_le
      (a * gaussianPairNumerator a b)
      (gaussianPairDenominator t)
      (gaussianPairDenominator_pos t ht)
      hmul'
  refine Q'.le_trans' _ _ _ hquot ?_
  exact Q'.le_of_eqv
    (divPos_scale_eqv
      a (gaussianPairNumerator a b)
      (gaussianPairDenominator t)
      (gaussianPairDenominator_pos t ht))

/-- Equivalent Padé-ready form:
`b ≤ a(1 + gap)`. -/
theorem b_le_a_mul_one_add_gaussianPairGap
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a) :
    b ≤ a * (1 + gaussianPairGap a b t ht) := by
  have hsub :=
    sub_le_a_mul_gaussianPairGap ha hab ht hscale
  have hfirst : b ≤ a + (b + -a) :=
    Q'.ge_of_eqv (cancel_add_sub a b)
  have hsecond :
      a + (b + -a) ≤
        a + a * gaussianPairGap a b t ht :=
    Q'.add_le_add_left a _ _ hsub
  refine Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond ?_)
  have hdistrib :
      (a * (1 + gaussianPairGap a b t ht)).eqv
        (a + a * gaussianPairGap a b t ht) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv a 1 (gaussianPairGap a b t ht)) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_one_eqv a)
  exact Q'.ge_of_eqv hdistrib

/-- The exact rational Padé comparison consumed by the exponential layer:

`b/(1+gap) ≤ a`.
-/
theorem b_mul_oneOver1p_gaussianPairGap_le_a
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a) :
    b * ExpUBInstance.oneOver1p
        (gaussianPairGap a b t ht) ≤ a := by
  let gap := gaussianPairGap a b t ht
  let pade := ExpUBInstance.oneOver1p gap
  have hgap0 : (0 : Q') ≤ gap :=
    gaussianPairGap_nonneg ha hab ht
  have hlinear : b ≤ a * (1 + gap) :=
    b_le_a_mul_one_add_gaussianPairGap ha hab ht hscale
  have hpade0 : (0 : Q') ≤ pade :=
    ExpUBInstance.oneOver1p_nonneg gap
  have hmul :
      b * pade ≤ (a * (1 + gap)) * pade :=
    Q'.mul_le_mul_of_nonneg_right
      b (a * (1 + gap)) pade hlinear hpade0
  refine Q'.le_trans' _ _ _ hmul ?_
  have hcollapse : ((a * (1 + gap)) * pade).eqv a := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv a (1 + gap) pade) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _
        (Q'.mul_comm_eqv (1 + gap) pade)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _
        (ExpUBInstance.oneOver1p_mul_oneAddX gap hgap0)) ?_
    exact Q'.mul_one_eqv a
  exact Q'.le_of_eqv hcollapse

/-! ## 2. A clean certificate interface for the exponent layer -/

/-- Data needed by later Faraut order code.  `baseExponent + gap ≃
pairedExponent` is deliberately explicit: it keeps the rational Gaussian
normalization separate from the Padé/order proof above. -/
structure GaussianPairCertificate
    (a b baseExponent pairedExponent gap : Q') : Prop where
  a_pos : (0 : Q') < a
  a_le_b : a ≤ b
  base_nonneg : (0 : Q') ≤ baseExponent
  gap_nonneg : (0 : Q') ≤ gap
  paired_nonneg : (0 : Q') ≤ pairedExponent
  exponent_split : (baseExponent + gap).eqv pairedExponent
  pade_prefactor : b * ExpUBInstance.oneOver1p gap ≤ a

/-- The hypotheses `0<a≤b`, `0<t`, `2t≤a²` canonically fill the Padé fields
of a Gaussian comparison certificate.  A later exact normalization lemma
only has to provide the three exponent fields and their split identity. -/
def GaussianPairCertificate.ofGaussianGap
    {a b t baseExponent pairedExponent : Q'}
    (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a)
    (hbase : (0 : Q') ≤ baseExponent)
    (hpaired : (0 : Q') ≤ pairedExponent)
    (hsplit :
      (baseExponent + gaussianPairGap a b t ht).eqv
        pairedExponent) :
    GaussianPairCertificate
      a b baseExponent pairedExponent
      (gaussianPairGap a b t ht) where
  a_pos := ha
  a_le_b := hab
  base_nonneg := hbase
  gap_nonneg := gaussianPairGap_nonneg ha hab ht
  paired_nonneg := hpaired
  exponent_split := hsplit
  pade_prefactor :=
    b_mul_oneOver1p_gaussianPairGap_le_a
      ha hab ht hscale

/-- The genuine rational Gaussian exponents `a²/(4t)` and `b²/(4t)`
instantiate the complete certificate, including the exact factored
difference-of-squares split. -/
def gaussianPairCertificate
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a) :
    GaussianPairCertificate
      a b (gaussianExponent a t ht)
      (gaussianExponent b t ht)
      (gaussianPairGap a b t ht) :=
  GaussianPairCertificate.ofGaussianGap
    ha hab ht hscale
    (gaussianExponent_nonneg (Q'.le_of_lt ha) ht)
    (gaussianExponent_nonneg
      (Q'.le_trans' _ _ _ (Q'.le_of_lt ha) hab) ht)
    (gaussianExponent_add_gap_eqv a b t ht)

/-! ## 3. Semantic constructive-real domination -/

def weightedExp
    (coefficient exponent : Q')
    (hexponent : (0 : Q') ≤ exponent) : CReal :=
  CReal.mul
    (CReal.ofQ' coefficient)
    (ExpNeg.expNeg exponent hexponent)

private theorem geRat_sub_of_leRat
    {X : CReal} {bound : Q'}
    (hX : CReal.leRat X bound) :
    ExpPos.geRat
      (CReal.sub (CReal.ofQ' bound) X) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := hX ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hsub :
      (0 : Q') ≤ (bound + ε) + -(X.approx n) :=
    Q'.sub_nonneg_of_le (hN n hn)
  have hrearrange :
      ((bound + ε) + -(X.approx n)).eqv
        ((bound + -(X.approx n)) + ε) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv bound ε (-(X.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left bound _ _
        (Q'.add_comm_eqv ε (-(X.approx n)))) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv bound (-(X.approx n)) ε)
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv hrearrange)

private theorem leEv_of_geRat_sub
    {X Y : CReal}
    (h : ExpPos.geRat (CReal.sub Y X) 0) :
    CReal.leEv X Y := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hnonneg :
      (0 : Q') ≤
        (Y.approx n + -(X.approx n)) + ε :=
    hN n hn
  have hrearrange :
      ((Y.approx n + -(X.approx n)) + ε).eqv
        ((Y.approx n + ε) + -(X.approx n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Y.approx n) (-(X.approx n)) ε) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Y.approx n) _ _
        (Q'.add_comm_eqv (-(X.approx n)) ε)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv (Y.approx n) ε (-(X.approx n)))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg
      (Q'.le_of_eqv hrearrange))

private theorem geRat_of_equiv
    {A B : CReal} {bound : Q'}
    (hAB : CReal.Equiv A B)
    (hB : ExpPos.geRat B bound) :
    ExpPos.geRat A bound := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε :=
    ExpNeg.half_mul_pos ε hε
  obtain ⟨N₁, hN₁⟩ := hAB (HalfPow.half * ε) hhε
  obtain ⟨N₂, hN₂⟩ := hB (HalfPow.half * ε) hhε
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hn₂ : N₂ ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  refine Q'.le_trans' _ _ _ (hN₂ n hn₂) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (HalfPow.half * ε)
      (hN₁ n hn₁).2) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        (A.approx n) (HalfPow.half * ε)
        (HalfPow.half * ε)) ?_)
  exact Q'.add_eqv_congr_left
    (A.approx n)
    (HalfPow.half * ε + HalfPow.half * ε) ε
    (ExpNeg.two_halves ε)

private theorem leEv_of_equiv
    {A B : CReal} (hAB : CReal.Equiv A B) :
    CReal.leEv A B := by
  intro ε hε
  obtain ⟨N, hN⟩ := hAB ε hε
  exact ⟨N, fun n hn => (hN n hn).1⟩

private theorem leEv_congr
    {A A' B B' : CReal}
    (hA : CReal.Equiv A A')
    (hB : CReal.Equiv B B')
    (h : CReal.leEv A' B') :
    CReal.leEv A B :=
  CReal.leEv_trans
    (leEv_of_equiv hA)
    (CReal.leEv_trans h
      (leEv_of_equiv hB.symm))

private theorem mul_congr_right
    {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  (CRealAlg.cmul_comm A B).trans
    ((CReal.mul_congr_left h).trans
      (CRealAlg.cmul_comm B' A))

theorem GaussianPairCertificate.gap_weight_leRat
    {a b baseExponent pairedExponent gap : Q'}
    (certificate :
      GaussianPairCertificate
        a b baseExponent pairedExponent gap) :
    CReal.leRat
      (weightedExp b gap certificate.gap_nonneg) a := by
  unfold weightedExp
  have hb0 : (0 : Q') ≤ b :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt certificate.a_pos)
      certificate.a_le_b
  have hscaled :=
    CReal.leRat_smul_nonneg hb0
      (expNeg_le_oneOver1p gap
        certificate.gap_nonneg)
  exact CReal.leRat_mono hscaled
    certificate.pade_prefactor

/-- The semantic Gaussian-pair comparison in the transitive constructive
order `CReal.leEv`.  This is the exact Faraut image-pair inequality once
`baseExponent + gap ≃ pairedExponent` is supplied:

`b exp(-pairedExponent) ≤ a exp(-baseExponent)`.
-/
theorem GaussianPairCertificate.weightedExp_leEv
    {a b baseExponent pairedExponent gap : Q'}
    (certificate :
      GaussianPairCertificate
        a b baseExponent pairedExponent gap) :
    CReal.leEv
      (weightedExp b pairedExponent
        certificate.paired_nonneg)
      (weightedExp a baseExponent
        certificate.base_nonneg) := by
  let baseWeight :=
    ExpNeg.expNeg baseExponent
      certificate.base_nonneg
  let gapWeight :=
    ExpNeg.expNeg gap certificate.gap_nonneg
  let gapPrefactor :=
    weightedExp b gap certificate.gap_nonneg
  have hgapBound :
      CReal.leRat gapPrefactor a :=
    certificate.gap_weight_leRat
  have hmargin :
      ExpPos.geRat
        (CReal.sub (CReal.ofQ' a) gapPrefactor) 0 :=
    geRat_sub_of_leRat hgapBound
  have hproduct :
      ExpPos.geRat
        (CReal.mul baseWeight
          (CReal.sub (CReal.ofQ' a) gapPrefactor)) 0 :=
    CReal.mul_nonneg
      (expNeg_geRat_zero
        baseExponent certificate.base_nonneg)
      hmargin
  have hproductDifference :
      ExpPos.geRat
        (CReal.sub
          (CReal.mul baseWeight (CReal.ofQ' a))
          (CReal.mul baseWeight gapPrefactor)) 0 :=
    geRat_of_equiv
      (CReal.mul_sub baseWeight
        (CReal.ofQ' a) gapPrefactor).symm
      hproduct
  have hregrouped :
      CReal.leEv
        (CReal.mul baseWeight gapPrefactor)
        (CReal.mul baseWeight (CReal.ofQ' a)) :=
    leEv_of_geRat_sub hproductDifference
  have hExpSplit :
      CReal.Equiv
        (ExpNeg.expNeg pairedExponent
          certificate.paired_nonneg)
        (CReal.mul baseWeight gapWeight) := by
    have htoSum :
        CReal.Equiv
          (ExpNeg.expNeg pairedExponent
            certificate.paired_nonneg)
          (ExpNeg.expNeg (baseExponent + gap)
            (Q'.zero_le_add _ _
              certificate.base_nonneg
              certificate.gap_nonneg)) :=
      expNeg_eqv_congr
        certificate.paired_nonneg
        (Q'.zero_le_add _ _
          certificate.base_nonneg
          certificate.gap_nonneg)
        certificate.exponent_split.symm
    exact htoSum.trans
      (expNeg_add_equiv
        baseExponent gap
        certificate.base_nonneg
        certificate.gap_nonneg).symm
  have hleft :
      CReal.Equiv
        (weightedExp b pairedExponent
          certificate.paired_nonneg)
        (CReal.mul baseWeight gapPrefactor) := by
    unfold weightedExp gapPrefactor
    have h₁ :=
      mul_congr_right
        (A := CReal.ofQ' b) hExpSplit
    refine h₁.trans ?_
    refine (CRealAlg.cmul_assoc
      (CReal.ofQ' b) baseWeight gapWeight).symm.trans ?_
    refine (CReal.mul_congr_left
      (CRealAlg.cmul_comm
        (CReal.ofQ' b) baseWeight)).trans ?_
    exact CRealAlg.cmul_assoc
      baseWeight (CReal.ofQ' b) gapWeight
  have hright :
      CReal.Equiv
        (weightedExp a baseExponent
          certificate.base_nonneg)
        (CReal.mul baseWeight (CReal.ofQ' a)) := by
    unfold weightedExp baseWeight
    exact CRealAlg.cmul_comm
      (CReal.ofQ' a)
      (ExpNeg.expNeg baseExponent
        certificate.base_nonneg)
  exact leEv_congr hleft hright hregrouped

/-- **Gaussian pair domination.**  For rational `0<a≤b`, `t>0`, and
`2t≤a²`,

`b exp(-b²/(4t)) ≤ a exp(-a²/(4t))`

in the repository's transitive semantic constructive-real order
`CReal.leEv`. -/
theorem gaussian_pair_weightedExp_leEv
    {a b t : Q'} (ha : (0 : Q') < a) (hab : a ≤ b)
    (ht : (0 : Q') < t)
    (hscale : Q'.ofNat 2 * t ≤ a * a) :
    CReal.leEv
      (weightedExp b (gaussianExponent b t ht)
        (gaussianExponent_nonneg
          (Q'.le_trans' _ _ _ (Q'.le_of_lt ha) hab) ht))
      (weightedExp a (gaussianExponent a t ht)
        (gaussianExponent_nonneg (Q'.le_of_lt ha) ht)) := by
  exact
    (gaussianPairCertificate ha hab ht hscale).weightedExp_leEv

/-! ## 4. Nontrivial exact instance -/

def halfQ : Q' := Q'.mkPos 1 2 (by decide)

theorem one_two_half_pade :
    (Q'.ofNat 2) *
        ExpUBInstance.oneOver1p
          (gaussianPairGap 1 2 halfQ (by decide)) ≤
      (1 : Q') := by
  exact b_mul_oneOver1p_gaussianPairGap_le_a
    (a := 1) (b := 2) (t := halfQ)
    (by decide) (by decide) (by decide) (by decide)

def oneTwoHalfCertificate :
    GaussianPairCertificate
      1 2 halfQ 2
      (gaussianPairGap 1 2 halfQ (by decide)) :=
  GaussianPairCertificate.ofGaussianGap
    (a := 1) (b := 2) (t := halfQ)
    (baseExponent := halfQ) (pairedExponent := 2)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem one_two_half_weightedExp_leEv :
    CReal.leEv
      (weightedExp 2 2 oneTwoHalfCertificate.paired_nonneg)
      (weightedExp 1 halfQ oneTwoHalfCertificate.base_nonneg) :=
  oneTwoHalfCertificate.weightedExp_leEv

#print axioms gaussianPairGap_nonneg
#print axioms sub_le_a_mul_gaussianPairGap
#print axioms b_le_a_mul_one_add_gaussianPairGap
#print axioms b_mul_oneOver1p_gaussianPairGap_le_a
#print axioms GaussianPairCertificate.ofGaussianGap
#print axioms gaussianExponent_add_gap_eqv
#print axioms gaussianPairCertificate
#print axioms GaussianPairCertificate.gap_weight_leRat
#print axioms GaussianPairCertificate.weightedExp_leEv
#print axioms gaussian_pair_weightedExp_leEv
#print axioms one_two_half_pade
#print axioms oneTwoHalfCertificate
#print axioms one_two_half_weightedExp_leEv

end YMGap.Continuum.SU2FarautGaussianPairDomination
