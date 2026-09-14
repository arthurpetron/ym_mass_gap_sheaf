/-
# A computed square root and inverse square root of a positive Cauchy stream

For a rational stream with QCauchy data and a uniform lower square L^2,
sample the existing Heron iteration at a computed index with square error
at most invSucc n. A difference-of-squares estimate supplies a QCauchy
modulus for these samples. Their reciprocal stream then has the existing
explicit reciprocal modulus. The inverse square cancels the ORIGINAL
stream value, not an independently supplied normalization scalar.

No modulus is selected from a Prop-level existence claim. Only rational
Heron samples are taken; no CReal square-root modulus is assumed.
-/

import YMGap.Continuum.PositiveRationalCauchyReciprocal
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveRationalCauchySquareRoot

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

theorem square_gap (L u v epsilon : Q') (hL : (0 : Q')<L)
    (hu : (0 : Q')≤u) (hv : L≤v) (he : (0 : Q')<epsilon)
    (hsq : u*u≤v*v+(L+L)*epsilon) : u≤v+epsilon := by
  apply CReal.le_of_sq_le_sq (Q'.add_pos (Q'.pos_of_lt_of_le hL hv) he) hu
  have hlinear := Q'.add_le_add_left (v*v) _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ epsilon (Q'.add_le_add hv hv) (Q'.le_of_lt he))
  have hsquare := Q'.add_le_self_of_nonneg (v*v+(v+v)*epsilon) (epsilon*epsilon)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt he) (Q'.le_of_lt he))
  exact Q'.le_trans' _ _ _ hsq (Q'.le_trans' _ _ _ hlinear (Q'.le_trans' _ _ _ hsquare
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.add (.var 0) (.var 0)) (.var 1)))
        (.mul (.var 1) (.var 1)))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (by decide)
      (fun | 0 => v | _ => epsilon)))))

variable {r : Nat → Q'} (c : QCauchy r) (L : Q') (hL : (0 : Q')<L)
  (hfloor : ∀ n, L*L≤r n)

include hL hfloor in
theorem source_positive (n : Nat) : (0 : Q')<r n :=
  Q'.pos_of_lt_of_le (Q'.mul_pos hL hL) (hfloor n)

def sampleIndex (n : Nat) : Nat :=
  (mulModulus (errAt (r n) 0) (Q'.invSucc n)
    (errAt_nonneg (r n) (source_positive L hL hfloor n) 0) (Q'.invSucc_pos n)).1.den

def sample (n : Nat) : Q' := heronSeq (r n) (sampleIndex L hL hfloor n)

theorem sample_floor (n : Nat) : L≤sample L hL hfloor n :=
  heronSeq_lb (r n) L (source_positive L hL hfloor n) hL (hfloor n) _

theorem sample_positive (n : Nat) : (0 : Q')<sample L hL hfloor n :=
  Q'.pos_of_lt_of_le hL (sample_floor L hL hfloor n)

theorem sample_square_lower (n : Nat) : r n≤sample L hL hfloor n*sample L hL hfloor n :=
  heronSeq_sq_ge (r n) (source_positive L hL hfloor n) _

theorem sample_square_upper (n : Nat) :
    sample L hL hfloor n*sample L hL hfloor n≤r n+Q'.invSucc n := by
  let d := mulModulus (errAt (r n) 0) (Q'.invSucc n)
    (errAt_nonneg (r n) (source_positive L hL hfloor n) 0) (Q'.invSucc_pos n)
  have herror : errAt (r n) d.1.den≤Q'.invSucc n :=
    Q'.le_trans' _ _ _ (errAt_le_geom (r n) (source_positive L hL hfloor n) d.1.den)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (errAt (r n) 0)
        (HalfPow.pow_half_le d.1 d.2.1) (errAt_nonneg (r n) (source_positive L hL hfloor n) 0)) d.2.2)
  exact Q'.le_add_of_sub_le herror

def tolerance (epsilon : Q') : Q' := HalfPow.half*((L+L)*epsilon)

include hL in
theorem tolerance_positive {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<tolerance L epsilon :=
  Q'.mul_pos (by decide) (Q'.mul_pos (Q'.add_pos hL hL) he)

theorem tolerance_budget (epsilon : Q') :
    Q'.eqv (tolerance L epsilon+tolerance L epsilon) ((L+L)*epsilon) :=
  ExpNeg.two_halves _

def sampleCauchy : QCauchy (sample L hL hfloor) where
  M epsilon := max (c.M (tolerance L epsilon)) (tolerance L epsilon).den
  bound := by
    intro epsilon he p q hp hq
    let delta := tolerance L epsilon
    have hd := tolerance_positive L hL he
    have hc := c.bound delta hd p q (Nat.le_trans (Nat.le_max_left _ _) hp)
      (Nat.le_trans (Nat.le_max_left _ _) hq)
    have step (i j : Nat) (hi : delta.den≤i) (hr : r i≤r j+delta) :
        sample L hL hfloor i≤sample L hL hfloor j+epsilon := by
      have herr := Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hi) (HalfPow.invSucc_den_le delta hd)
      have hfirst := Q'.le_trans' _ _ _ (sample_square_upper L hL hfloor i)
        (Q'.add_le_add_left (r i) _ _ herr)
      have hsecond := Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ delta hr)
        (Q'.add_le_add_right _ _ delta
          (Q'.add_le_add_right _ _ delta (sample_square_lower L hL hfloor j)))
      apply square_gap L _ _ epsilon hL (Q'.le_of_lt (sample_positive L hL hfloor i))
        (sample_floor L hL hfloor j) he
      exact Q'.le_trans' _ _ _ hfirst (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ delta delta)
          (Q'.add_eqv_congr_left _ _ _ (tolerance_budget L epsilon)))))
    exact ⟨step p q (Nat.le_trans (Nat.le_max_right _ _) hp) hc.1,
      step q p (Nat.le_trans (Nat.le_max_right _ _) hq) hc.2⟩

def source : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon,c.bound epsilon he⟩

def value : CReal where
  approx := sample L hL hfloor
  cauchy := fun epsilon he => ⟨(sampleCauchy c L hL hfloor).M epsilon,
    (sampleCauchy c L hL hfloor).bound epsilon he⟩

def valueCauchy : QCauchy (value c L hL hfloor).approx := sampleCauchy c L hL hfloor

theorem value_square : Equiv (CReal.mul (value c L hL hfloor) (value c L hL hfloor)) (source c) := by
  intro epsilon he
  refine ⟨epsilon.den,fun n hn => ⟨?_,?_⟩⟩
  · exact Q'.le_trans' _ _ _ (sample_square_upper L hL hfloor n)
      (Q'.add_le_add_left (r n) _ _ (Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le epsilon he)))
  · exact Q'.le_trans' _ _ _ (sample_square_lower L hL hfloor n)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

def inverseCauchy : QCauchy (PositiveRationalCauchyReciprocal.term L hL (sample_floor L hL hfloor)) :=
  PositiveRationalCauchyReciprocal.reciprocalCauchy (sampleCauchy c L hL hfloor)
    L hL (sample_floor L hL hfloor)

def inverse : CReal where
  approx := PositiveRationalCauchyReciprocal.term L hL (sample_floor L hL hfloor)
  cauchy := fun epsilon he => ⟨(inverseCauchy c L hL hfloor).M epsilon,
    (inverseCauchy c L hL hfloor).bound epsilon he⟩

theorem inverse_positive (n : Nat) : (0 : Q')<(inverse c L hL hfloor).approx n :=
  Q'.recipPos_pos _ (sample_positive L hL hfloor n)

theorem value_mul_inverse : Equiv (CReal.mul (value c L hL hfloor) (inverse c L hL hfloor)) cone :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_recipPos_eqv _ (sample_positive L hL hfloor n))

theorem inverse_square_source :
    Equiv (CReal.mul (inverse c L hL hfloor) (CReal.mul (inverse c L hL hfloor) (source c))) cone := by
  let a := value c L hL hfloor
  let i := inverse c L hL hfloor
  have he : Equiv (CReal.mul i (CReal.mul i (CReal.mul a a)))
      (CReal.mul (CReal.mul a i) (CReal.mul a i)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.var 1) (.mul (.var 0) (.var 0))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => a.approx n | _ => i.approx n))
  exact (Pivot2.mul_congr_right (Pivot2.mul_congr_right (value_square c L hL hfloor).symm)).trans
    (he.trans ((Pivot2.mul_congr_left (value_mul_inverse c L hL hfloor)).trans
      ((Pivot2.mul_congr_right (value_mul_inverse c L hL hfloor)).trans (CRealAlg.cone_mul cone))))

end YMGap.Continuum.PositiveRationalCauchySquareRoot

#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.square_gap
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.source_positive
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sampleIndex
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sample
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sample_floor
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sample_positive
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sample_square_lower
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sample_square_upper
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.tolerance
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.tolerance_positive
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.tolerance_budget
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.sampleCauchy
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.source
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.value
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.valueCauchy
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.value_square
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.inverseCauchy
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.inverse
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.inverse_positive
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.value_mul_inverse
#print axioms YMGap.Continuum.PositiveRationalCauchySquareRoot.inverse_square_source
