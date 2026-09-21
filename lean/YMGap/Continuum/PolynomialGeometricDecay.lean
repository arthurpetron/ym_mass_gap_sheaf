/-
# An explicit modulus for a polynomial times any strict geometric rate

Choose a positive block length N with 2^p q^N <= 1/2. Writing m=floor(n/N),
the elementary bound n+1 <= N(m+1) and (m+1)^p <= (2^p)^(m+1) give

  q^n (n+1)^p <= (2N)^p (1/2)^m.

The existing geometric cutoff therefore computes an all-later-indices
tolerance modulus. Degree, amplitude and rate remain explicit data. The
same-Wilson scaling consumer uses this to test polynomial norm growth; no
uniformity as q approaches one is asserted.
-/

import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.PartitionUpperBound
import YMGap.Continuum.TotalMajorantClose
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.PolynomialGeometricDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.PartitionUpperBound (nat_pow_le_two_pow_pow ofNat_pow_mul)
open YMGap.Continuum.ClusterCount (ofNat_nonneg ofNat_le_ofNat ofNat_mul_eqv)

local infix:50 " ≈ " => Q'.eqv

/-- The maximum with one retains Euclidean division even when the cutoff is zero. -/
def blockLength (q : Q') (p : Nat) : Nat :=
  max 1 (geometricCutoff q (Q'.ofNat (2^p)) HalfPow.half)

theorem blockLength_pos (q : Q') (p : Nat) : 0 < blockLength q p := by
  have h := Nat.le_max_left 1 (geometricCutoff q (Q'.ofNat (2^p)) HalfPow.half)
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) h

theorem block_gain {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (p : Nat) :
    Q'.ofNat (2^p) * q^(blockLength q p) ≤ HalfPow.half :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (geometric_bound hq0 hq1 (ofNat_nonneg _) (by decide : (0 : Q') < HalfPow.half)
      _ (Nat.le_max_right _ _))

private theorem polynomial_block_bound (N p n : Nat) (hN : 0 < N) :
    (n+1)^p ≤ (N^p * 2^p) * (2^p)^(n/N) := by
  have hrem := Nat.mod_lt n hN
  have hdiv := Nat.div_add_mod n N
  have hstep : n+1 ≤ N*(n/N+1) := by
    rw [Nat.mul_succ]
    omega
  calc
    (n+1)^p ≤ (N*(n/N+1))^p := Nat.pow_le_pow_left hstep p
    _ = N^p * (n/N+1)^p := Nat.mul_pow N (n/N+1) p
    _ ≤ N^p * (2^p)^(n/N+1) :=
      Nat.mul_le_mul_left _ (nat_pow_le_two_pow_pow p (n/N+1))
    _ = (N^p * 2^p) * (2^p)^(n/N) := by rw [Nat.pow_succ]; ac_rfl

private theorem shuffle (a b c : Q') : a*(b*c) ≈ b*(c*a) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The envelope is valid at every n, including the initial block and q=0. -/
theorem blocked_bound {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (p n : Nat) :
    q^n * Q'.ofNat ((n+1)^p) ≤
      Q'.ofNat ((blockLength q p)^p * 2^p) * HalfPow.half^(n / blockLength q p) := by
  let N := blockLength q p
  let m := n/N
  let A := Q'.ofNat (N^p * 2^p)
  have hpower : q^n ≤ (q^N)^m :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone hq0 (Q'.le_of_lt hq1)
        (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self n N))
      (Q'.ge_of_eqv (TotalMajorantClose.pow_mul q N m))
  have hpoly : Q'.ofNat ((n+1)^p) ≤ A * Q'.ofNat ((2^p)^m) :=
    Q'.le_trans' _ _ _ (ofNat_le_ofNat (polynomial_block_bound N p n (blockLength_pos q p)))
      (Q'.le_of_eqv (ofNat_mul_eqv (N^p*2^p) ((2^p)^m)))
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _ hpower (ofNat_nonneg ((n+1)^p))
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ ((q^N)^m) hpoly
    (Q'.pow_nonneg _ (Q'.pow_nonneg q hq0 N) m)
  have h3 : (q^N)^m * (A * Q'.ofNat ((2^p)^m)) ≈
      A * (Q'.ofNat (2^p) * q^N)^m :=
    Q'.eqv_trans _ _ _ (shuffle _ _ _)
      (Q'.mul_eqv_congr_left A _ _ (ofNat_pow_mul (2^p) (q^N) m))
  have h4 := Q'.mul_le_mul_of_nonneg_left _ _ A
    (HKConv.pow_le_pow_base
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (Q'.pow_nonneg q hq0 N))
      (block_gain hq0 hq1 p) m) (ofNat_nonneg _)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv h3) h4))

/-- Computed cutoff, with no rate-of-convergence input beyond q<1. -/
def polynomialCutoff (q C : Q') (p : Nat) (epsilon : Q') : Nat :=
  blockLength q p * geometricCutoff HalfPow.half
    (C * Q'.ofNat ((blockLength q p)^p * 2^p)) epsilon

theorem polynomial_bound {q C epsilon : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (hC : (0 : Q') ≤ C) (he : (0 : Q') < epsilon) (p n : Nat)
    (hn : polynomialCutoff q C p epsilon ≤ n) :
    q^n * (C * Q'.ofNat ((n+1)^p)) ≤ epsilon := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ C (blocked_bound hq0 hq1 p n) hC
  have hleft : q^n * (C * Q'.ofNat ((n+1)^p)) ≈
      C * (q^n * Q'.ofNat ((n+1)^p)) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  have hright : C * (Q'.ofNat ((blockLength q p)^p * 2^p) *
      HalfPow.half^(n/blockLength q p)) ≈
      HalfPow.half^(n/blockLength q p) * (C * Q'.ofNat ((blockLength q p)^p * 2^p)) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  have hindex : geometricCutoff HalfPow.half
      (C * Q'.ofNat ((blockLength q p)^p * 2^p)) epsilon ≤ n / blockLength q p := by
    apply (Nat.le_div_iff_mul_le (blockLength_pos q p)).mpr
    simpa only [polynomialCutoff, Nat.mul_comm] using hn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
      (geometric_bound HalfPow.half_nonneg (by decide : HalfPow.half < (1 : Q'))
        (Q'.mul_nonneg _ _ hC (ofNat_nonneg _)) he _ hindex)))

end YMGap.Continuum.PolynomialGeometricDecay

#print axioms YMGap.Continuum.PolynomialGeometricDecay.blockLength
#print axioms YMGap.Continuum.PolynomialGeometricDecay.blockLength_pos
#print axioms YMGap.Continuum.PolynomialGeometricDecay.block_gain
#print axioms YMGap.Continuum.PolynomialGeometricDecay.blocked_bound
#print axioms YMGap.Continuum.PolynomialGeometricDecay.polynomialCutoff
#print axioms YMGap.Continuum.PolynomialGeometricDecay.polynomial_bound
