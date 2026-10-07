/-
# Actual theta parity cells bounded by their Gaussian shells

The literal two-Chebyshev theta cell is bounded by its actual nome power.
The checked parity exponent and frequency pins then give the even and odd
shell bounds, including the zero even shell and negative signed indices.
Frequency-square cells pay at most 4*radius^2 times the Gaussian shell.

Consumer: omitted weighted diamond shells and ThetaAngularShellTail. No
shell cardinality, diamond-to-rectangle equality, infinite addition formula,
or curvature ceiling is assumed or concluded here.
-/

import YMGap.Continuum.ThetaParityWeights
import YMGap.Continuum.ThetaParityShellGeometry

namespace YMGap.Continuum.ThetaParityShellWeights

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaParityWeights
open YMGap.Continuum.ThetaParityShellGeometry
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_nonneg ofNat_mul_eqv ofNat_le_ofNat)

local infix:50 " ≈ " => Q'.eqv

/-- The original first-kind Chebyshev bound includes the constant order. -/
theorem chebT_abs_le_one (n : Nat) {x : Q'}
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) :
    Q'.abs (Cheb.T n x) ≤ (1 : Q') := by
  cases n with
  | zero =>
      exact Q'.le_of_eqv
        (TsumDeriv.Q'.abs_of_nonneg (by decide : (0 : Q') ≤ 1))
  | succ n =>
      have h := ChebU.Tabs_le_one n x hx1 hx0
      exact Q'.abs_le h.1 h.2

/-- Literal signed theta cells pay only their actual Gaussian power. -/
theorem thetaCell_abs_le {w x y : Q'} (hw0 : (0 : Q') < w)
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (z : SignedPair) :
    Q'.abs (thetaCell w x y z) ≤
      w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs) := by
  let E := z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs
  have hpx : Q'.abs (Cheb.T (z.1+z.2).natAbs x) ≤ 1 :=
    chebT_abs_le_one _ hx0 hx1
  have hpy : Q'.abs (Cheb.T (z.1-z.2).natAbs y) ≤ 1 :=
    chebT_abs_le_one _ hy0 hy1
  have hp : (0 : Q') ≤ w^E := Q'.pow_nonneg w (Q'.le_of_lt hw0) E
  change Q'.abs ((w^E*Cheb.T (z.1+z.2).natAbs x)*Cheb.T (z.1-z.2).natAbs y) ≤ w^E
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpy (Q'.abs_nonneg _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) ?_
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpx (Q'.abs_nonneg _)) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hp))

/-- The actual exponent domination supplies the shell Gaussian, not a cap. -/
theorem thetaCell_shell_abs_le {w x y : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q'))
    (z : SignedPair) (R : Nat)
    (hE : R*R ≤ z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs) :
    Q'.abs (thetaCell w x y z) ≤ w^(R*R) :=
  Q'.le_trans' _ _ _ (thetaCell_abs_le hw0 hx0 hx1 hy0 hy1 z)
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hE)

private theorem frequency_square_le {f R : Nat} (hf : f ≤ 2*R) :
    Q'.ofNat (f*f) ≤ 4*(Q'.ofNat R*Q'.ofNat R) := by
  have hn : f*f ≤ 4*(R*R) := by
    have h := Nat.mul_le_mul hf hf
    have hp : (2*R)*(2*R) = 4*(R*R) := by
      calc
        (2*R)*(2*R) = (2*2)*(R*R) := by ac_rfl
        _ = 4*(R*R) := by rw [show 2*2 = 4 by decide]
    exact hp ▸ h
  have hpin : Q'.ofNat (4*(R*R)) ≈ 4*(Q'.ofNat R*Q'.ofNat R) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv 4 (R*R))
      (Q'.mul_eqv_congr_left 4 _ _ (ofNat_mul_eqv R R))
  exact Q'.le_trans' _ _ _ (ofNat_le_ofNat hn) (Q'.le_of_eqv hpin)

/-- Literal endpoint frequency-square cell, controlled by its true radius. -/
theorem frequencyCell_shell_abs_le {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (z : SignedPair) (R : Nat)
    (hE : R*R ≤ z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs)
    (hf : (z.1-z.2).natAbs ≤ 2*R) :
    Q'.abs (frequencyCell w x z) ≤ 4*(Q'.ofNat R*Q'.ofNat R)*w^(R*R) := by
  let f := (z.1-z.2).natAbs
  have hcoef : (0 : Q') ≤ Q'.ofNat (f*f) := ofNat_nonneg (f*f)
  have hcell : Q'.abs (thetaCell w x 1 z) ≤ w^(R*R) :=
    thetaCell_shell_abs_le hw0 hw1 hx0 hx1 (by decide) (by decide) z R hE
  change Q'.abs (Q'.ofNat (f*f)*thetaCell w x 1 z) ≤ _
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcell (Q'.abs_nonneg _)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
      (TsumDeriv.Q'.abs_of_nonneg hcoef))) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ (frequency_square_le hf)
    (Q'.pow_nonneg w (Q'.le_of_lt hw0) (R*R))

private theorem even_encoded_exponent_pin (j k : Int) :
    (encodeEven (j,k)).1.natAbs*(encodeEven (j,k)).1.natAbs +
      (encodeEven (j,k)).2.natAbs*(encodeEven (j,k)).2.natAbs = evenExponent j k := by
  rw [even_nat_exponent_pin]
  simp only [evenExponent, Nat.mul_add]

private theorem odd_encoded_exponent_pin (j k : Int) :
    (encodeOdd (j,k)).1.natAbs*(encodeOdd (j,k)).1.natAbs +
      (encodeOdd (j,k)).2.natAbs*(encodeOdd (j,k)).2.natAbs = oddExponent j k := by
  rw [odd_nat_exponent_pin]
  simp only [oddExponent, Nat.mul_add]

/-- Even transformed cells, including radius zero. -/
theorem evenCell_abs_le {w x y : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (j k : Int) :
    Q'.abs (evenCell w x y (j,k)) ≤ w^(evenRadius j k*evenRadius j k) := by
  have hE : evenRadius j k*evenRadius j k ≤
      (encodeEven (j,k)).1.natAbs*(encodeEven (j,k)).1.natAbs +
        (encodeEven (j,k)).2.natAbs*(encodeEven (j,k)).2.natAbs := by
    rw [even_encoded_exponent_pin]
    exact even_exponent_ge_radius_sq j k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr (Q'.eqv_symm (thetaCell_even_pin w x y j k))))
    (thetaCell_shell_abs_le hw0 hw1 hx0 hx1 hy0 hy1 (encodeEven (j,k)) (evenRadius j k) hE)

/-- Odd transformed cells retain the actual extra factor w. -/
theorem oddCell_abs_le {w x y : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (j k : Int) :
    Q'.abs (oddCell w x y (j,k)) ≤ w^(oddRadius j k*oddRadius j k) := by
  have hE : oddRadius j k*oddRadius j k ≤
      (encodeOdd (j,k)).1.natAbs*(encodeOdd (j,k)).1.natAbs +
        (encodeOdd (j,k)).2.natAbs*(encodeOdd (j,k)).2.natAbs := by
    rw [odd_encoded_exponent_pin]
    exact odd_exponent_ge_radius_sq j k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr (Q'.eqv_symm (thetaCell_odd_pin w x y j k))))
    (thetaCell_shell_abs_le hw0 hw1 hx0 hx1 hy0 hy1 (encodeOdd (j,k)) (oddRadius j k) hE)

/-- Even actual endpoint frequency cells pay at most four radius squares. -/
theorem evenFrequencyCell_abs_le {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (j k : Int) :
    Q'.abs (evenFrequencyCell w x (j,k)) ≤
      4*(Q'.ofNat (evenRadius j k)*Q'.ofNat (evenRadius j k))*
        w^(evenRadius j k*evenRadius j k) := by
  have hE : evenRadius j k*evenRadius j k ≤
      (encodeEven (j,k)).1.natAbs*(encodeEven (j,k)).1.natAbs +
        (encodeEven (j,k)).2.natAbs*(encodeEven (j,k)).2.natAbs := by
    rw [even_encoded_exponent_pin]
    exact even_exponent_ge_radius_sq j k
  have hf : ((encodeEven (j,k)).1-(encodeEven (j,k)).2).natAbs ≤ 2*evenRadius j k := by
    rw [(even_frequency_pin j k).2]
    exact (even_frequencies_le_radius j k).2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr (Q'.eqv_symm (frequencyCell_even_pin w x j k))))
    (frequencyCell_shell_abs_le hw0 hw1 hx0 hx1 (encodeEven (j,k)) (evenRadius j k) hE hf)

/-- Odd actual endpoint frequency cells, at all negative or positive indices. -/
theorem oddFrequencyCell_abs_le {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (j k : Int) :
    Q'.abs (oddFrequencyCell w x (j,k)) ≤
      4*(Q'.ofNat (oddRadius j k)*Q'.ofNat (oddRadius j k))*
        w^(oddRadius j k*oddRadius j k) := by
  have hE : oddRadius j k*oddRadius j k ≤
      (encodeOdd (j,k)).1.natAbs*(encodeOdd (j,k)).1.natAbs +
        (encodeOdd (j,k)).2.natAbs*(encodeOdd (j,k)).2.natAbs := by
    rw [odd_encoded_exponent_pin]
    exact odd_exponent_ge_radius_sq j k
  have hf : ((encodeOdd (j,k)).1-(encodeOdd (j,k)).2).natAbs ≤ 2*oddRadius j k := by
    rw [(odd_frequency_pin j k).2]
    exact (odd_frequencies_le_radius j k).2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr (Q'.eqv_symm (frequencyCell_odd_pin w x j k))))
    (frequencyCell_shell_abs_le hw0 hw1 hx0 hx1 (encodeOdd (j,k)) (oddRadius j k) hE hf)

end YMGap.Continuum.ThetaParityShellWeights

#print axioms YMGap.Continuum.ThetaParityShellWeights.chebT_abs_le_one
#print axioms YMGap.Continuum.ThetaParityShellWeights.thetaCell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.thetaCell_shell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.frequencyCell_shell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.evenCell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.oddCell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.evenFrequencyCell_abs_le
#print axioms YMGap.Continuum.ThetaParityShellWeights.oddFrequencyCell_abs_le
