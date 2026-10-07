/-
# Actual finite theta weights on the two parity diamonds

The literal Gaussian/Chebyshev cell and its endpoint frequency-square
weight are transported through the checked signed-box parity bijection.
Every nome exponent is a natural number, including the shifted exponent
j*(j+1) for negative integers. The odd cell has exactly one factor w.

These are finite identities on the actual diamonds, including N=0. They
do not replace diamonds by rectangles, assert a derivative interchange,
or prove a completed theta addition identity or curvature estimate.
-/

import YMGap.Continuum.ThetaParityConvolution
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.KPLimit
import YMGap.Continuum.ChebyshevFormalJets

namespace YMGap.Continuum.ThetaParityWeights

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Actual signed theta cell, with both Gaussian exponents retained. -/
def thetaCell (w x y : Q') (z : SignedPair) : Q' :=
  w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs) *
    Cheb.T (z.1+z.2).natAbs x * Cheb.T (z.1-z.2).natAbs y

/-- Endpoint frequency weight; no derivative interpretation is assumed. -/
def frequencyCell (w x : Q') (z : SignedPair) : Q' :=
  Q'.ofNat ((z.1-z.2).natAbs*(z.1-z.2).natAbs) * thetaCell w x 1 z

def evenThetaTerm (w x : Q') (j : Int) : Q' :=
  w^(2*(j.natAbs*j.natAbs)) * Cheb.T (2*j).natAbs x

def oddThetaTerm (w x : Q') (j : Int) : Q' :=
  w^(2*(j*(j+1)).toNat) * Cheb.T (2*j+1).natAbs x

def evenCell (w x y : Q') (z : SignedPair) : Q' :=
  evenThetaTerm w x z.1 * evenThetaTerm w y z.2

def oddCell (w x y : Q') (z : SignedPair) : Q' :=
  w * oddThetaTerm w x z.1 * oddThetaTerm w y z.2

def evenFrequencyCell (w x : Q') (z : SignedPair) : Q' :=
  evenThetaTerm w x z.1 *
    (Q'.ofNat ((2*z.2).natAbs*(2*z.2).natAbs) *
      w^(2*(z.2.natAbs*z.2.natAbs)))

def oddFrequencyCell (w x : Q') (z : SignedPair) : Q' :=
  w * oddThetaTerm w x z.1 *
    (Q'.ofNat ((2*z.2+1).natAbs*(2*z.2+1).natAbs) *
      w^(2*(z.2*(z.2+1)).toNat))

/-- Signed shifted Gaussian exponents are nonnegative, not truncated data. -/
theorem shifted_exponent_nonneg (j : Int) : 0 ≤ j*(j+1) := by
  by_cases hj : 0 ≤ j
  · exact Int.mul_nonneg hj (by omega)
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem even_nat_exponent_pin (j k : Int) :
    (encodeEven (j,k)).1.natAbs*(encodeEven (j,k)).1.natAbs +
      (encodeEven (j,k)).2.natAbs*(encodeEven (j,k)).2.natAbs =
        2*(j.natAbs*j.natAbs) + 2*(k.natAbs*k.natAbs) := by
  have hp := even_exponent_pin j k
  have hc :
      (( (encodeEven (j,k)).1.natAbs*(encodeEven (j,k)).1.natAbs +
          (encodeEven (j,k)).2.natAbs*(encodeEven (j,k)).2.natAbs : Nat) : Int) =
        ((2*(j.natAbs*j.natAbs) + 2*(k.natAbs*k.natAbs) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natAbs_mul_self']
    omega
  exact Int.ofNat.inj hc

theorem odd_nat_exponent_pin (j k : Int) :
    (encodeOdd (j,k)).1.natAbs*(encodeOdd (j,k)).1.natAbs +
      (encodeOdd (j,k)).2.natAbs*(encodeOdd (j,k)).2.natAbs =
        2*(j*(j+1)).toNat + 2*(k*(k+1)).toNat + 1 := by
  have hp := odd_exponent_pin j k
  have hj := Int.toNat_of_nonneg (shifted_exponent_nonneg j)
  have hk := Int.toNat_of_nonneg (shifted_exponent_nonneg k)
  have hc :
      (( (encodeOdd (j,k)).1.natAbs*(encodeOdd (j,k)).1.natAbs +
          (encodeOdd (j,k)).2.natAbs*(encodeOdd (j,k)).2.natAbs : Nat) : Int) =
        ((2*(j*(j+1)).toNat + 2*(k*(k+1)).toNat + 1 : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natAbs_mul_self', hj, hk]
    omega
  exact Int.ofNat.inj hc

private theorem T_at_one : ∀ n, Cheb.T n 1 ≈ 1 ∧ Cheb.T (n+1) 1 ≈ 1
  | 0 => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  | n+1 => by
      have h := T_at_one n
      refine ⟨h.2, ?_⟩
      rw [Cheb.T_succ_succ]
      exact Q'.eqv_trans _ _ _
        (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ h.2)
          (Q'.neg_eqv_congr _ _ h.1))
        (by decide : ((2 : Q')*1)*1 + -1 ≈ (1 : Q'))

private theorem evenThetaTerm_at_one (w : Q') (k : Int) :
    evenThetaTerm w 1 k ≈ w^(2*(k.natAbs*k.natAbs)) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (T_at_one (2*k).natAbs).1)
    (Q'.mul_one_eqv _)

private theorem oddThetaTerm_at_one (w : Q') (k : Int) :
    oddThetaTerm w 1 k ≈ w^(2*(k*(k+1)).toNat) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (T_at_one (2*k+1).natAbs).1)
    (Q'.mul_one_eqv _)

/-- The actual even transformed theta cell factors, at every signed index. -/
theorem thetaCell_even_pin (w x y : Q') (j k : Int) :
    thetaCell w x y (encodeEven (j,k)) ≈ evenCell w x y (j,k) := by
  unfold thetaCell evenCell evenThetaTerm
  rw [even_nat_exponent_pin, (even_frequency_pin j k).1,
    (even_frequency_pin j k).2]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.pow_add_eqv w _ _)))
    (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun
        | 0 => w^(2*(j.natAbs*j.natAbs))
        | 1 => w^(2*(k.natAbs*k.natAbs))
        | 2 => Cheb.T (2*j).natAbs x
        | _ => Cheb.T (2*k).natAbs y))

/-- The actual odd transformed theta cell has exactly one factor w. -/
theorem thetaCell_odd_pin (w x y : Q') (j k : Int) :
    thetaCell w x y (encodeOdd (j,k)) ≈ oddCell w x y (j,k) := by
  unfold thetaCell oddCell oddThetaTerm
  rw [odd_nat_exponent_pin, (odd_frequency_pin j k).1,
    (odd_frequency_pin j k).2]
  have hp : w^(2*(j*(j+1)).toNat + 2*(k*(k+1)).toNat + 1) ≈
      (w^(2*(j*(j+1)).toNat) * w^(2*(k*(k+1)).toNat)) * w := by
    exact Q'.eqv_trans _ _ _ (Q'.pow_add_eqv w _ 1)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.pow_add_eqv w _ _))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv w)))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ hp))
    (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 4)))
      (by decide) (fun
        | 0 => w^(2*(j*(j+1)).toNat)
        | 1 => w^(2*(k*(k+1)).toNat)
        | 2 => w
        | 3 => Cheb.T (2*j+1).natAbs x
        | _ => Cheb.T (2*k+1).natAbs y))

theorem frequencyCell_even_pin (w x : Q') (j k : Int) :
    frequencyCell w x (encodeEven (j,k)) ≈ evenFrequencyCell w x (j,k) := by
  unfold frequencyCell
  rw [(even_frequency_pin j k).2]
  have ht := Q'.mul_eqv_congr_left
    (Q'.ofNat ((2*k).natAbs*(2*k).natAbs)) _ _ (thetaCell_even_pin w x 1 j k)
  unfold evenCell at ht
  have he := Q'.mul_eqv_congr_left
    (Q'.ofNat ((2*k).natAbs*(2*k).natAbs)) _ _
    (Q'.mul_eqv_congr_left (evenThetaTerm w x j) _ _
      (evenThetaTerm_at_one w k))
  exact Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun
        | 0 => Q'.ofNat ((2*k).natAbs*(2*k).natAbs)
        | 1 => evenThetaTerm w x j
        | _ => w^(2*(k.natAbs*k.natAbs)))))

theorem frequencyCell_odd_pin (w x : Q') (j k : Int) :
    frequencyCell w x (encodeOdd (j,k)) ≈ oddFrequencyCell w x (j,k) := by
  unfold frequencyCell
  rw [(odd_frequency_pin j k).2]
  have ht := Q'.mul_eqv_congr_left
    (Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)) _ _ (thetaCell_odd_pin w x 1 j k)
  unfold oddCell at ht
  have he := Q'.mul_eqv_congr_left
    (Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)) _ _
    (Q'.mul_eqv_congr_left (w*oddThetaTerm w x j) _ _
      (oddThetaTerm_at_one w k))
  exact Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)
        | 1 => w
        | 2 => oddThetaTerm w x j
        | _ => w^(2*(k*(k+1)).toNat))))

/-- Exact actual theta sum on the two diamonds, not rectangular sums. -/
theorem theta_box_eq_diamonds (w x y : Q') (N : Nat) :
    listQSum (thetaCell w x y) (boxIndices N) ≈
      listQSum (evenCell w x y) (evenDiamondIndices N) +
        listQSum (oddCell w x y) (oddDiamondIndices N) := by
  have he : listQSum (fun z : SignedPair => thetaCell w x y (encodeEven z))
      (evenDiamondIndices N) ≈ listQSum (evenCell w x y) (evenDiamondIndices N) :=
    listQSum_congr (f := fun z : SignedPair => thetaCell w x y (encodeEven z))
      (g := evenCell w x y) (fun z => thetaCell_even_pin w x y z.1 z.2) _
  have ho : listQSum (fun z : SignedPair => thetaCell w x y (encodeOdd z))
      (oddDiamondIndices N) ≈ listQSum (oddCell w x y) (oddDiamondIndices N) :=
    listQSum_congr (f := fun z : SignedPair => thetaCell w x y (encodeOdd z))
      (g := oddCell w x y) (fun z => thetaCell_odd_pin w x y z.1 z.2) _
  exact Q'.eqv_trans _ _ _ (signed_box_parity_convolution (thetaCell w x y) N)
    (Q'.add_eqv_congr' he ho)

/-- Exact endpoint frequency-square sum on the two actual diamonds. -/
theorem frequency_box_eq_diamonds (w x : Q') (N : Nat) :
    listQSum (frequencyCell w x) (boxIndices N) ≈
      listQSum (evenFrequencyCell w x) (evenDiamondIndices N) +
        listQSum (oddFrequencyCell w x) (oddDiamondIndices N) := by
  have he : listQSum (fun z : SignedPair => frequencyCell w x (encodeEven z))
      (evenDiamondIndices N) ≈ listQSum (evenFrequencyCell w x) (evenDiamondIndices N) :=
    listQSum_congr (f := fun z : SignedPair => frequencyCell w x (encodeEven z))
      (g := evenFrequencyCell w x) (fun z => frequencyCell_even_pin w x z.1 z.2) _
  have ho : listQSum (fun z : SignedPair => frequencyCell w x (encodeOdd z))
      (oddDiamondIndices N) ≈ listQSum (oddFrequencyCell w x) (oddDiamondIndices N) :=
    listQSum_congr (f := fun z : SignedPair => frequencyCell w x (encodeOdd z))
      (g := oddFrequencyCell w x) (fun z => frequencyCell_odd_pin w x z.1 z.2) _
  exact Q'.eqv_trans _ _ _ (signed_box_parity_convolution (frequencyCell w x) N)
    (Q'.add_eqv_congr' he ho)

/-- Actual coefficient polynomial in the second scalar coordinate. -/
def thetaCellPolynomial (w x : Q') (z : SignedPair) : QPoly.Poly :=
  QPoly.pscale
    (w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs)*Cheb.T (z.1+z.2).natAbs x)
    (ChebyshevFormalJets.Tpoly (z.1-z.2).natAbs)

theorem thetaCellPolynomial_eval (w x y : Q') (z : SignedPair) :
    QPoly.eval (thetaCellPolynomial w x z) y ≈ thetaCell w x y z :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ y)
    (Q'.mul_eqv_congr_left _ _ _ (ChebyshevFormalJets.eval_Tpoly _ y))

/-- The endpoint frequency weight is now pinned to the ACTUAL first formal
derivative, rather than supplied as a derivative interpretation. -/
theorem thetaCellPolynomial_endpoint_derivative (w x : Q') (z : SignedPair) :
    QPoly.eval (QPolyFormalDerivative.pderiv (thetaCellPolynomial w x z)) 1 ≈
      frequencyCell w x z := by
  let c := w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs)*Cheb.T (z.1+z.2).natAbs x
  let b := (z.1-z.2).natAbs
  have hd : QPoly.eval (QPolyFormalDerivative.pderiv (thetaCellPolynomial w x z)) 1 ≈
      c*(Q'.ofNat b*Q'.ofNat b) :=
    Q'.eqv_trans _ _ _
      (QPolyCoefficientEvaluation.coefficient_eval
        (QPolyFormalDerivative.pderiv_pscale c (ChebyshevFormalJets.Tpoly b)) 1)
      (Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ 1)
        (Q'.mul_eqv_congr_left _ _ _ (ChebyshevFormalJets.first_derivative_at_one b)))
  have hn : (Q'.ofNat b*Q'.ofNat b) ≈ Q'.ofNat (b*b) := by
    show ((b : Int)*(b : Int))*1 = ((b*b : Nat) : Int)*1
    simp only [Int.natCast_mul]
  have hf : frequencyCell w x z ≈ Q'.ofNat (b*b)*c :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left c _ _ (T_at_one b).1))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv c))
  exact Q'.eqv_trans _ _ _ hd
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ hn)
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.eqv_symm hf)))

/-- Finite coefficient sum of the literal cells, in their original order. -/
def thetaSumPolynomial (w x : Q') : List SignedPair → QPoly.Poly
  | [] => []
  | z::zs => QPoly.padd (thetaCellPolynomial w x z) (thetaSumPolynomial w x zs)

theorem thetaSumPolynomial_eval (w x y : Q') : ∀ zs,
    QPoly.eval (thetaSumPolynomial w x zs) y ≈ listQSum (thetaCell w x y) zs
  | [] => Q'.eqv_refl 0
  | z::zs => Q'.eqv_trans _ _ _ (QPoly.eval_padd _ _ y)
      (Q'.add_eqv_congr' (thetaCellPolynomial_eval w x y z) (thetaSumPolynomial_eval w x y zs))

/-- Formal endpoint jet of the ACTUAL finite sum; no infinite interchange. -/
theorem thetaSumPolynomial_endpoint_derivative (w x : Q') : ∀ zs,
    QPoly.eval (QPolyFormalDerivative.pderiv (thetaSumPolynomial w x zs)) 1 ≈
      listQSum (frequencyCell w x) zs
  | [] => Q'.eqv_refl 0
  | z::zs => Q'.eqv_trans _ _ _
      (QPolyCoefficientEvaluation.coefficient_eval
        (QPolyFormalDerivative.pderiv_padd (thetaCellPolynomial w x z) (thetaSumPolynomial w x zs)) 1)
      (Q'.eqv_trans _ _ _ (QPoly.eval_padd _ _ 1)
        (Q'.add_eqv_congr' (thetaCellPolynomial_endpoint_derivative w x z)
          (thetaSumPolynomial_endpoint_derivative w x zs)))

end YMGap.Continuum.ThetaParityWeights

#print axioms YMGap.Continuum.ThetaParityWeights.shifted_exponent_nonneg
#print axioms YMGap.Continuum.ThetaParityWeights.even_nat_exponent_pin
#print axioms YMGap.Continuum.ThetaParityWeights.odd_nat_exponent_pin
#print axioms YMGap.Continuum.ThetaParityWeights.thetaCell_even_pin
#print axioms YMGap.Continuum.ThetaParityWeights.thetaCell_odd_pin
#print axioms YMGap.Continuum.ThetaParityWeights.frequencyCell_even_pin
#print axioms YMGap.Continuum.ThetaParityWeights.frequencyCell_odd_pin
#print axioms YMGap.Continuum.ThetaParityWeights.theta_box_eq_diamonds
#print axioms YMGap.Continuum.ThetaParityWeights.frequency_box_eq_diamonds
#print axioms YMGap.Continuum.ThetaParityWeights.thetaCellPolynomial
#print axioms YMGap.Continuum.ThetaParityWeights.thetaCellPolynomial_eval
#print axioms YMGap.Continuum.ThetaParityWeights.thetaCellPolynomial_endpoint_derivative
#print axioms YMGap.Continuum.ThetaParityWeights.thetaSumPolynomial
#print axioms YMGap.Continuum.ThetaParityWeights.thetaSumPolynomial_eval
#print axioms YMGap.Continuum.ThetaParityWeights.thetaSumPolynomial_endpoint_derivative
