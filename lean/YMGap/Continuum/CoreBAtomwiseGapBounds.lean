/-
# Core-B atomwise parity gap bounds

On the canonical consumer diagonal

  `(s,r) = (t+1,n-1-t)`,

every midpoint window has the fixed antidiagonal total `n+2`.  This file
records the exact centered Casimir arithmetic used by a coefficient-mass
proof of `C(1,0,n)`.  In even length the midpoint antidiagonal is even and a
left displacement `d` costs `4d²` across the two midpoint factors.  In odd
length it is odd and costs `4d(d+1)`.

The results here are arithmetic infrastructure only.  They do not classify
an atom as adverse, sum coefficient mass, or inhabit a Core-B certificate.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBBoundedMonomialNormalForm
import YMGap.Continuum.CoreBResidualBaseUniform
import YMGap.Continuum.CoreBUniversalSquareGap
import YMGap.Continuum.MeanComplementCovariance

namespace YMGap.Continuum.CoreBAtomwiseGapBounds

open YMGap.Continuum
open YMGap.Constructive
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CoreBBoundedMonomialNormalForm
open YMGap.Continuum.CoreBResidualBaseUniform
open YMGap.Continuum.CoreBUniversalSquareGap
open YMGap.Continuum.MeanComplementCovariance

local infix:50 " ≈ " => Q'.eqv

local macro "atomwise_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.add_mul, Int.mul_add,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. Canonical contents and centered antidiagonals -/

/-- Common `(wh)` content observed on the canonical even family `n=2k`. -/
def evenContent (k : Nat) : Nat :=
  4 * (k + 1) * (k + 3)

/-- Common `(wh)` content observed on the canonical odd family `n=2k+1`. -/
def oddContent (k : Nat) : Nat :=
  4 * k * k + 20 * k + 22

/-- Heat-kernel exponent on an antidiagonal of total index `N`. -/
def antidiagonalExponent (N p : Nat) : Nat :=
  c4 p + c4 (N - p)

private theorem c4_even_center_shift (L d : Nat) :
    c4 L + c4 (L + 2 * d) =
      2 * c4 (L + d) + 2 * d * d := by
  unfold c4
  rw [show 2 * d = d + d by omega]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

private theorem c4_odd_center_shift (L d : Nat) :
    c4 L + c4 (L + 2 * d + 1) =
      c4 (L + d) + c4 (L + d + 1) + 2 * d * (d + 1) := by
  unfold c4
  rw [show 2 * d = d + d by omega]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- An even antidiagonal has the exact centered quadratic shift `2d²`. -/
theorem antidiagonalExponent_even_left (K d : Nat) (hd : d ≤ K) :
    antidiagonalExponent (2 * K) (K - d) =
      2 * c4 K + 2 * d * d := by
  have hK : K - d + d = K := Nat.sub_add_cancel hd
  have hright : 2 * K - (K - d) = (K - d) + 2 * d := by omega
  simpa only [antidiagonalExponent, hK, hright] using
    c4_even_center_shift (K - d) d

/-- An odd antidiagonal has the exact centered quadratic shift
`2d(d+1)`. -/
theorem antidiagonalExponent_odd_left (K d : Nat) (hd : d ≤ K) :
    antidiagonalExponent (2 * K + 1) (K - d) =
      c4 K + c4 (K + 1) + 2 * d * (d + 1) := by
  have hK : K - d + d = K := Nat.sub_add_cancel hd
  have hright : 2 * K + 1 - (K - d) = (K - d) + 2 * d + 1 := by omega
  simpa only [antidiagonalExponent, hK, hright] using
    c4_odd_center_shift (K - d) d

/-- The right side of an even antidiagonal has the same `2e²` cost. -/
theorem antidiagonalExponent_even_right (K e : Nat) (he : e ≤ K) :
    antidiagonalExponent (2 * K) (K + e) =
      2 * c4 K + 2 * e * e := by
  have hK : K - e + e = K := Nat.sub_add_cancel he
  have hleft : 2 * K - (K + e) = K - e := by omega
  have hpair := c4_even_center_shift (K - e) e
  rw [hK] at hpair
  rw [show K - e + 2 * e = K + e by omega] at hpair
  rw [antidiagonalExponent, hleft, Nat.add_comm]
  exact hpair

/-- The right side of an odd antidiagonal has the same `2e(e+1)` cost. -/
theorem antidiagonalExponent_odd_right (K e : Nat) (he : e ≤ K) :
    antidiagonalExponent (2 * K + 1) (K + 1 + e) =
      c4 K + c4 (K + 1) + 2 * e * (e + 1) := by
  have hK : K - e + e = K := Nat.sub_add_cancel he
  have hleft : 2 * K + 1 - (K + 1 + e) = K - e := by omega
  have hpair := c4_odd_center_shift (K - e) e
  rw [hK] at hpair
  rw [show K - e + 2 * e + 1 = K + 1 + e by omega] at hpair
  rw [antidiagonalExponent, hleft, Nat.add_comm]
  exact hpair

theorem antidiagonalExponent_even_center_minimum
    (K p : Nat) (hp : p ≤ 2 * K) :
    antidiagonalExponent (2 * K) K ≤
      antidiagonalExponent (2 * K) p := by
  have hcenter := antidiagonalExponent_even_left K 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero] at hcenter
  by_cases hleft : p ≤ K
  · have hshift := antidiagonalExponent_even_left K (K - p) (by omega)
    rw [show K - (K - p) = p by omega] at hshift
    rw [hcenter, hshift]
    omega
  · have hshift := antidiagonalExponent_even_right K (p - K) (by omega)
    rw [show K + (p - K) = p by omega] at hshift
    rw [hcenter, hshift]
    omega

theorem antidiagonalExponent_odd_center_minimum
    (K p : Nat) (hp : p ≤ 2 * K + 1) :
    antidiagonalExponent (2 * K + 1) K ≤
      antidiagonalExponent (2 * K + 1) p := by
  have hcenter := antidiagonalExponent_odd_left K 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hcenter
  by_cases hleft : p ≤ K
  · have hshift := antidiagonalExponent_odd_left K (K - p) (by omega)
    rw [show K - (K - p) = p by omega] at hshift
    rw [hcenter, hshift]
    omega
  · have hshift :=
      antidiagonalExponent_odd_right K (p - (K + 1)) (by omega)
    rw [show K + 1 + (p - (K + 1)) = p by omega] at hshift
    rw [hcenter, hshift]
    omega

/-! Coefficient products on one antidiagonal are controlled by the same
center geometry as the Casimir exponent. -/

/-- Product of the two SU(2) dimension coefficients on antidiagonal `N`. -/
def antidiagonalCoefficient (N p : Nat) : Nat :=
  (p + 1) * (N - p + 1)

private theorem antidiagonalCoefficient_even_left
    (K p : Nat) (hp : p ≤ K) :
    antidiagonalCoefficient (2 * K) p ≤ (K + 1) * (K + 1) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hp
  unfold antidiagonalCoefficient
  rw [show 2 * (p + d) - p + 1 = p + 2 * d + 1 by omega]
  have hid :
      (p + 1) * (p + 2 * d + 1) + d * d =
        (p + d + 1) * (p + d + 1) := by
    simp only [Nat.add_mul, Nat.mul_add]
    rw [show p * (2 * d) = 2 * (p * d) by
      rw [← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc]]
    rw [Nat.mul_comm d p]
    omega
  omega

/-- The coefficient product on an even antidiagonal is maximized at its
unique center. -/
theorem antidiagonalCoefficient_even_center_max
    (K p : Nat) (hp : p ≤ 2 * K) :
    antidiagonalCoefficient (2 * K) p ≤ (K + 1) * (K + 1) := by
  by_cases hleft : p ≤ K
  · exact antidiagonalCoefficient_even_left K p hleft
  · let q := 2 * K - p
    have hq : q ≤ K := by
      dsimp [q]
      omega
    have hqp : 2 * K - q = p := by
      dsimp [q]
      omega
    have h := antidiagonalCoefficient_even_left K q hq
    unfold antidiagonalCoefficient at h ⊢
    rw [show 2 * K - p = q by rfl]
    rw [hqp] at h
    simpa only [Nat.mul_comm] using h

private theorem antidiagonalCoefficient_odd_left
    (K p : Nat) (hp : p ≤ K) :
    antidiagonalCoefficient (2 * K + 1) p ≤
      (K + 1) * (K + 2) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hp
  unfold antidiagonalCoefficient
  rw [show 2 * (p + d) + 1 - p + 1 = p + 2 * d + 2 by omega]
  have hid :
      (p + 1) * (p + 2 * d + 2) + d * (d + 1) =
        (p + d + 1) * (p + d + 2) := by
    simp only [Nat.add_mul, Nat.mul_add]
    rw [show p * (2 * d) = 2 * (p * d) by
      rw [← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc]]
    rw [Nat.mul_comm d p]
    omega
  omega

/-- The coefficient product on an odd antidiagonal is maximized at either of
its two central indices. -/
theorem antidiagonalCoefficient_odd_center_max
    (K p : Nat) (hp : p ≤ 2 * K + 1) :
    antidiagonalCoefficient (2 * K + 1) p ≤
      (K + 1) * (K + 2) := by
  by_cases hleft : p ≤ K
  · exact antidiagonalCoefficient_odd_left K p hleft
  · let q := 2 * K + 1 - p
    have hq : q ≤ K := by
      dsimp [q]
      omega
    have hqp : 2 * K + 1 - q = p := by
      dsimp [q]
      omega
    have h := antidiagonalCoefficient_odd_left K q hq
    unfold antidiagonalCoefficient at h ⊢
    rw [show 2 * K + 1 - p = q by rfl]
    rw [hqp] at h
    simpa only [Nat.mul_comm] using h

/-- Nat-safe square of the centered antidiagonal coordinate `2p-N`. -/
def centeredIndexSquare (N p : Nat) : Nat :=
  (N - 2 * p) * (N - 2 * p) + (2 * p - N) * (2 * p - N)

private theorem twice_antidiagonalExponent_add_four_cross
    (N p : Nat) (hp : p ≤ N) :
    2 * antidiagonalExponent N p + 4 * (p * (N - p)) =
      2 * (N * N) + 4 * N := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hp
  unfold antidiagonalExponent c4
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_add]
  rw [Nat.mul_comm d p]
  omega

/-- Exact completion of the antidiagonal Casimir into the centered square. -/
theorem twice_antidiagonalExponent_eq_centeredSquare_add
    (N p : Nat) (hp : p ≤ N) :
    2 * antidiagonalExponent N p =
      centeredIndexSquare N p + N * (N + 4) := by
  have hcross := twice_antidiagonalExponent_add_four_cross N p hp
  have hsquare := four_x_add_dsq p N hp
  change 4 * (p * (N - p)) + centeredIndexSquare N p = N * N at hsquare
  rw [Nat.mul_add]
  omega

/-! ## 2. Canonical midpoint atoms -/

def canonicalALeftIndex (s i p : Nat) : Nat :=
  match i with
  | 0 => p
  | 1 => p
  | _ => s + 1

def canonicalARightIndex (s i q : Nat) : Nat :=
  match i with
  | 0 => q
  | 1 => s + 1
  | 2 => q
  | _ => s + 1

def canonicalMLeftIndex (s j p : Nat) : Nat :=
  match j with
  | 0 => p
  | 1 => p
  | _ => s + 1

def canonicalMRightIndex (s j q : Nat) : Nat :=
  match j with
  | 0 => q
  | _ => s + 1

theorem canonical_a_atom_exponent_all
    (n t i p q : Nat) (ht : t < n) :
    (aAtomicMonomial (t + 1) (n - 1 - t) i p q).exponent =
      antidiagonalExponent (n + 1) (canonicalALeftIndex (t + 1) i p) +
        antidiagonalExponent (n + 3) (canonicalARightIndex (t + 1) i q) := by
  cases i with
  | zero =>
      simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial,
        canonicalALeftIndex, canonicalARightIndex, antidiagonalExponent]
      rw [show t + 1 + (n - 1 - t + 1) = n + 1 by omega]
      rw [show t + 1 + (n - 1 - t + 3) = n + 3 by omega]
  | succ i =>
      cases i with
      | zero =>
          simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            coefficientMonomial, canonicalALeftIndex, canonicalARightIndex,
            antidiagonalExponent]
          rw [show t + 1 + (n - 1 - t + 1) = n + 1 by omega]
          rw [show n - 1 - t + 2 =
            n + 3 - (t + 1 + 1) by omega]
      | succ i =>
          cases i with
          | zero =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                windowMonomial, boundaryMonomial, WeightMonomial.mul,
                coefficientMonomial, canonicalALeftIndex, canonicalARightIndex,
                antidiagonalExponent]
              rw [show n - 1 - t =
                n + 1 - (t + 1 + 1) by omega]
              rw [show t + 1 +
                (n + 1 - (t + 1 + 1) + 3) = n + 3 by omega]
          | succ i =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                boundaryMonomial, WeightMonomial.mul, coefficientMonomial,
                canonicalALeftIndex, canonicalARightIndex,
                antidiagonalExponent]
              rw [show n - 1 - t =
                n + 1 - (t + 1 + 1) by omega]
              rw [show n + 1 - (t + 1 + 1) + 2 =
                n + 3 - (t + 1 + 1) by omega]

theorem canonical_m_atom_exponent_all
    (n t j p q : Nat) (ht : t < n) :
    (mAtomicMonomial (t + 1) (n - 1 - t) j p q).exponent =
      antidiagonalExponent (n + 2) (canonicalMLeftIndex (t + 1) j p) +
        antidiagonalExponent (n + 2) (canonicalMRightIndex (t + 1) j q) := by
  cases j with
  | zero =>
      simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial,
        canonicalMLeftIndex, canonicalMRightIndex, antidiagonalExponent]
      rw [show t + 1 + (n - 1 - t + 2) = n + 2 by omega]
  | succ j =>
      cases j with
      | zero =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            WeightMonomial.twice, coefficientMonomial,
            canonicalMLeftIndex, canonicalMRightIndex,
            antidiagonalExponent]
          rw [show t + 1 + (n - 1 - t + 2) = n + 2 by omega]
          rw [show n - 1 - t + 1 =
            n + 2 - (t + 1 + 1) by omega]
      | succ j =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            boundaryMonomial, WeightMonomial.mul, coefficientMonomial,
            canonicalMLeftIndex, canonicalMRightIndex,
            antidiagonalExponent]
          rw [show n - 1 - t + 1 =
            n + 2 - (t + 1 + 1) by omega]

private def midpointCoefficientMultiplicity (j : Nat) : Nat :=
  match j with
  | 1 => 2
  | _ => 1

private theorem midpointCoefficientMultiplicity_le_two (j : Nat) :
    midpointCoefficientMultiplicity j ≤ 2 := by
  cases j with
  | zero => simp [midpointCoefficientMultiplicity]
  | succ j =>
      cases j with
      | zero => simp [midpointCoefficientMultiplicity]
      | succ j => simp [midpointCoefficientMultiplicity]

private theorem canonical_a_atom_coefficient_all
    (n t i p q : Nat) (ht : t < n) :
    (aAtomicMonomial (t + 1) (n - 1 - t) i p q).coefficientNat =
      antidiagonalCoefficient (n + 1) (canonicalALeftIndex (t + 1) i p) *
        antidiagonalCoefficient (n + 3) (canonicalARightIndex (t + 1) i q) := by
  cases i with
  | zero =>
      simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial,
        canonicalALeftIndex, canonicalARightIndex, antidiagonalCoefficient]
      rw [show t + 1 + (n - 1 - t + 1) = n + 1 by omega]
      rw [show t + 1 + (n - 1 - t + 3) = n + 3 by omega]
  | succ i =>
      cases i with
      | zero =>
          simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            coefficientMonomial, canonicalALeftIndex, canonicalARightIndex,
            antidiagonalCoefficient]
          rw [show t + 1 + (n - 1 - t + 1) = n + 1 by omega]
          rw [show n - 1 - t + 2 =
            n + 3 - (t + 1 + 1) by omega]
      | succ i =>
          cases i with
          | zero =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                windowMonomial, boundaryMonomial, WeightMonomial.mul,
                coefficientMonomial, canonicalALeftIndex, canonicalARightIndex,
                antidiagonalCoefficient]
              rw [show n - 1 - t =
                n + 1 - (t + 1 + 1) by omega]
              rw [show t + 1 +
                (n + 1 - (t + 1 + 1) + 3) = n + 3 by omega]
          | succ i =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                boundaryMonomial, WeightMonomial.mul, coefficientMonomial,
                canonicalALeftIndex, canonicalARightIndex,
                antidiagonalCoefficient]
              rw [show n - 1 - t =
                n + 1 - (t + 1 + 1) by omega]
              rw [show n + 1 - (t + 1 + 1) + 2 =
                n + 3 - (t + 1 + 1) by omega]

private theorem canonical_m_atom_coefficient_all
    (n t j p q : Nat) (ht : t < n) :
    (mAtomicMonomial (t + 1) (n - 1 - t) j p q).coefficientNat =
      midpointCoefficientMultiplicity j *
        (antidiagonalCoefficient (n + 2) (canonicalMLeftIndex (t + 1) j p) *
          antidiagonalCoefficient (n + 2)
            (canonicalMRightIndex (t + 1) j q)) := by
  cases j with
  | zero =>
      simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial,
        midpointCoefficientMultiplicity, canonicalMLeftIndex,
        canonicalMRightIndex, antidiagonalCoefficient, Nat.one_mul]
      rw [show t + 1 + (n - 1 - t + 2) = n + 2 by omega]
  | succ j =>
      cases j with
      | zero =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            WeightMonomial.twice, coefficientMonomial,
            midpointCoefficientMultiplicity, canonicalMLeftIndex,
            canonicalMRightIndex, antidiagonalCoefficient]
          rw [show t + 1 + (n - 1 - t + 2) = n + 2 by omega]
          rw [show n - 1 - t + 1 =
            n + 2 - (t + 1 + 1) by omega]
          omega
      | succ j =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            boundaryMonomial, WeightMonomial.mul, coefficientMonomial,
            midpointCoefficientMultiplicity, canonicalMLeftIndex,
            canonicalMRightIndex, antidiagonalCoefficient, Nat.one_mul]
          rw [show n - 1 - t + 1 =
            n + 2 - (t + 1 + 1) by omega]

theorem canonicalALeftIndex_le
    (n t i p : Nat) (ht : t < n) (hp : p < aLeftCount (t + 1) i) :
    canonicalALeftIndex (t + 1) i p ≤ n + 1 := by
  cases i with
  | zero =>
      simp only [aLeftCount, canonicalALeftIndex] at hp ⊢
      omega
  | succ i =>
      cases i with
      | zero =>
          simp only [aLeftCount, canonicalALeftIndex] at hp ⊢
          omega
      | succ i =>
          simp only [canonicalALeftIndex]
          omega

theorem canonicalARightIndex_le
    (n t i q : Nat) (ht : t < n) (hq : q < aRightCount (t + 1) i) :
    canonicalARightIndex (t + 1) i q ≤ n + 3 := by
  cases i with
  | zero =>
      simp only [aRightCount, canonicalARightIndex] at hq ⊢
      omega
  | succ i =>
      cases i with
      | zero =>
          simp only [canonicalARightIndex]
          omega
      | succ i =>
          cases i with
          | zero =>
              simp only [aRightCount, canonicalARightIndex] at hq ⊢
              omega
          | succ i =>
              simp only [canonicalARightIndex]
              omega

theorem canonicalMLeftIndex_le
    (n t j p : Nat) (ht : t < n) (hp : p < mLeftCount (t + 1) j) :
    canonicalMLeftIndex (t + 1) j p ≤ n + 2 := by
  cases j with
  | zero =>
      simp only [mLeftCount, canonicalMLeftIndex] at hp ⊢
      omega
  | succ j =>
      cases j with
      | zero =>
          simp only [mLeftCount, canonicalMLeftIndex] at hp ⊢
          omega
      | succ j =>
          simp only [canonicalMLeftIndex]
          omega

theorem canonicalMRightIndex_le
    (n t j q : Nat) (ht : t < n) (hq : q < mRightCount (t + 1) j) :
    canonicalMRightIndex (t + 1) j q ≤ n + 2 := by
  cases j with
  | zero =>
      simp only [mRightCount, canonicalMRightIndex] at hq ⊢
      omega
  | succ j =>
      simp only [canonicalMRightIndex]
      omega

/-- A bounded midpoint atom on the canonical diagonal has two copies of the
fixed antidiagonal exponent `n+2`. -/
theorem canonical_midpoint_atom_exponent
    (n t p : Nat) (ht : t < n) :
    (mAtomicMonomial (t + 1) (n - 1 - t) 0 p p).exponent =
      2 * antidiagonalExponent (n + 2) p := by
  simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
    windowMonomial, WeightMonomial.mul, antidiagonalExponent,
    coefficientMonomial]
  rw [show t + 1 + (n - 1 - t + 2) = n + 2 by omega]
  omega

theorem evenContent_eq_center (k : Nat) :
    evenContent k = 4 * c4 (k + 1) := by
  unfold evenContent c4
  rw [Nat.mul_assoc]

theorem oddContent_eq_center (k : Nat) :
    oddContent k = 2 * (c4 (k + 1) + c4 (k + 2)) := by
  unfold oddContent c4
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

/-- Every bounded midpoint selector on an even canonical diagonal carries at
least the common centered content; this includes `j=1` and every boundary
selector, not only the window/window component `j=0`. -/
theorem canonical_midpoint_even_content_lower_all
    (k t j p q : Nat) (ht : t < 2 * k)
    (hp : p < mLeftCount (t + 1) j)
    (hq : q < mRightCount (t + 1) j) :
    evenContent k ≤
      (mAtomicMonomial (t + 1) (2 * k - 1 - t) j p q).exponent := by
  rw [canonical_m_atom_exponent_all (2 * k) t j p q ht]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega]
  have hl := antidiagonalExponent_even_center_minimum
    (k + 1) (canonicalMLeftIndex (t + 1) j p)
    (by
      rw [← show 2 * k + 2 = 2 * (k + 1) by omega]
      exact canonicalMLeftIndex_le (2 * k) t j p ht hp)
  have hr := antidiagonalExponent_even_center_minimum
    (k + 1) (canonicalMRightIndex (t + 1) j q)
    (by
      rw [← show 2 * k + 2 = 2 * (k + 1) by omega]
      exact canonicalMRightIndex_le (2 * k) t j q ht hq)
  have hadd := Nat.add_le_add hl hr
  have hcenter := antidiagonalExponent_even_left (k + 1) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero] at hcenter
  rw [hcenter] at hadd
  rw [evenContent_eq_center]
  omega

/-- Every bounded midpoint selector on an odd canonical diagonal carries at
least the common two-center content. -/
theorem canonical_midpoint_odd_content_lower_all
    (k t j p q : Nat) (ht : t < 2 * k + 1)
    (hp : p < mLeftCount (t + 1) j)
    (hq : q < mRightCount (t + 1) j) :
    oddContent k ≤
      (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j p q).exponent := by
  rw [canonical_m_atom_exponent_all (2 * k + 1) t j p q ht]
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
  have hl := antidiagonalExponent_odd_center_minimum
    (k + 1) (canonicalMLeftIndex (t + 1) j p)
    (by
      rw [← show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
      exact canonicalMLeftIndex_le (2 * k + 1) t j p ht hp)
  have hr := antidiagonalExponent_odd_center_minimum
    (k + 1) (canonicalMRightIndex (t + 1) j q)
    (by
      rw [← show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
      exact canonicalMRightIndex_le (2 * k + 1) t j q ht hq)
  have hadd := Nat.add_le_add hl hr
  have hcenter := antidiagonalExponent_odd_left (k + 1) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hcenter
  rw [hcenter] at hadd
  rw [oddContent_eq_center]
  rw [show k + 1 + 1 = k + 2 by omega] at hadd
  omega

/-- **Even left-shift formula.**  On `n=2k`, moving both midpoint
indices `d` places left of the center raises the atom exponent by exactly
`4d²` above the canonical content. -/
theorem canonical_midpoint_even_left_shift
    (k t d : Nat) (ht : t < 2 * k)
    (hd : d ≤ k + 1) :
    (mAtomicMonomial (t + 1) (2 * k - 1 - t) 0
        (k + 1 - d) (k + 1 - d)).exponent =
      evenContent k + 4 * d * d := by
  rw [canonical_midpoint_atom_exponent (2 * k) t (k + 1 - d) ht]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega]
  rw [antidiagonalExponent_even_left (k + 1) d hd]
  rw [evenContent_eq_center]
  simp only [Nat.mul_assoc]
  omega

/-- **Odd left-shift formula.**  On `n=2k+1`, moving both midpoint
indices `d` places left of the left center raises the atom exponent by exactly
`4d(d+1)` above the canonical content. -/
theorem canonical_midpoint_odd_left_shift
    (k t d : Nat) (ht : t < 2 * k + 1)
    (hd : d ≤ k + 1) :
    (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) 0
        (k + 1 - d) (k + 1 - d)).exponent =
      oddContent k + 4 * d * (d + 1) := by
  rw [canonical_midpoint_atom_exponent (2 * k + 1) t
    (k + 1 - d) ht]
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
  rw [antidiagonalExponent_odd_left (k + 1) d hd]
  rw [show k + 1 + 1 = k + 2 by omega]
  rw [oddContent_eq_center]
  simp only [Nat.mul_assoc]
  omega

/-! ## 3. Window/window numerator gaps -/

/-- The window/window numerator atom has fixed antidiagonal totals `n+1` and
`n+3` along the canonical consumer diagonal. -/
theorem canonical_window_numerator_atom_exponent
    (n t p q : Nat) (ht : t < n) :
    (aAtomicMonomial (t + 1) (n - 1 - t) 0 p q).exponent =
      antidiagonalExponent (n + 1) p +
        antidiagonalExponent (n + 3) q := by
  simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
    windowMonomial, WeightMonomial.mul, antidiagonalExponent,
    coefficientMonomial]
  rw [show t + 1 + (n - 1 - t + 1) = n + 1 by omega]
  rw [show t + 1 + (n - 1 - t + 3) = n + 3 by omega]

/-- At even consumer length, the two adjacent odd antidiagonals have a
combined center exactly two exponent units above the common content. -/
theorem even_window_numerator_center (k : Nat) :
    antidiagonalExponent (2 * k + 1) k +
        antidiagonalExponent (2 * (k + 1) + 1) (k + 1) =
      evenContent k + 2 := by
  have hleft := antidiagonalExponent_odd_left k 0 (by omega)
  have hright := antidiagonalExponent_odd_left (k + 1) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero] at hleft hright
  rw [hleft, hright]
  rw [show k + 1 + 1 = k + 2 by omega]
  rw [evenContent_eq_center]
  unfold c4
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- At odd consumer length, the two adjacent even antidiagonals attain the
common content exactly. -/
theorem odd_window_numerator_center (k : Nat) :
    antidiagonalExponent (2 * (k + 1)) (k + 1) +
        antidiagonalExponent (2 * (k + 2)) (k + 2) =
      oddContent k := by
  have hleft := antidiagonalExponent_even_left (k + 1) 0 (by omega)
  have hright := antidiagonalExponent_even_left (k + 2) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero] at hleft hright
  rw [hleft, hright]
  rw [oddContent_eq_center]
  omega

/-- Every bounded numerator selector on an even canonical diagonal has the
unavoidable two-unit gap above common content. -/
theorem canonical_numerator_even_content_lower_all
    (k t i p q : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i) :
    evenContent k + 2 ≤
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent := by
  rw [canonical_a_atom_exponent_all (2 * k) t i p q ht]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
  have hl := antidiagonalExponent_odd_center_minimum
    k (canonicalALeftIndex (t + 1) i p)
    (canonicalALeftIndex_le (2 * k) t i p ht hp)
  have hr := antidiagonalExponent_odd_center_minimum
    (k + 1) (canonicalARightIndex (t + 1) i q)
    (by
      rw [← show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
      exact canonicalARightIndex_le (2 * k) t i q ht hq)
  have hadd := Nat.add_le_add hl hr
  rw [← even_window_numerator_center k]
  exact hadd

/-- Every bounded numerator selector on an odd canonical diagonal has at
least the common two-center content. -/
theorem canonical_numerator_odd_content_lower_all
    (k t i p q : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i) :
    oddContent k ≤
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent := by
  rw [canonical_a_atom_exponent_all (2 * k + 1) t i p q ht]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
  have hl := antidiagonalExponent_even_center_minimum
    (k + 1) (canonicalALeftIndex (t + 1) i p)
    (by
      rw [← show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      exact canonicalALeftIndex_le (2 * k + 1) t i p ht hp)
  have hr := antidiagonalExponent_even_center_minimum
    (k + 2) (canonicalARightIndex (t + 1) i q)
    (by
      rw [← show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
      exact canonicalARightIndex_le (2 * k + 1) t i q ht hq)
  have hadd := Nat.add_le_add hl hr
  rw [← odd_window_numerator_center k]
  exact hadd

/-- Exact even-parity left/right quadratic gap for a window/window numerator
atom.  The right displacement contributes `2e(e+1)`, whose minimum is zero. -/
theorem canonical_window_numerator_even_gaps
    (k t d e : Nat) (ht : t < 2 * k)
    (hd : d ≤ k) (he : e ≤ k + 1) :
    (aAtomicMonomial (t + 1) (2 * k - 1 - t) 0
        (k - d) (k + 2 + e)).exponent =
      evenContent k + 2 + 2 * d * (d + 1) + 2 * e * (e + 1) := by
  rw [canonical_window_numerator_atom_exponent (2 * k) t
    (k - d) (k + 2 + e) ht]
  rw [show 2 * k + 1 = 2 * k + 1 by rfl]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
  rw [antidiagonalExponent_odd_left k d hd]
  rw [antidiagonalExponent_odd_right (k + 1) e he]
  have hcenter := even_window_numerator_center k
  have hleft := antidiagonalExponent_odd_left k 0 (by omega)
  have hright := antidiagonalExponent_odd_left (k + 1) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hleft hright
  rw [hleft, hright] at hcenter
  rw [show k + 1 + 1 = k + 2 by omega] at hcenter ⊢
  omega

/-- Exact odd-parity left/right quadratic gap for a window/window numerator
atom.  The right displacement contributes `2e²`, again with minimum zero. -/
theorem canonical_window_numerator_odd_gaps
    (k t d e : Nat) (ht : t < 2 * k + 1)
    (hd : d ≤ k + 1) (he : e ≤ k + 2) :
    (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) 0
        (k + 1 - d) (k + 2 + e)).exponent =
      oddContent k + 2 * d * d + 2 * e * e := by
  rw [canonical_window_numerator_atom_exponent (2 * k + 1) t
    (k + 1 - d) (k + 2 + e) ht]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
  rw [antidiagonalExponent_even_left (k + 1) d hd]
  rw [antidiagonalExponent_even_right (k + 2) e he]
  have hcenter := odd_window_numerator_center k
  have hleft := antidiagonalExponent_even_left (k + 1) 0 (by omega)
  have hright := antidiagonalExponent_even_left (k + 2) 0 (by omega)
  simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero] at hleft hright
  rw [hleft, hright] at hcenter
  simp only [Nat.mul_assoc]
  omega

/-- The even right quadratic has minimum zero, attained at `e=0`. -/
theorem canonical_window_numerator_even_right_gap_minimum
    (k t d e : Nat) (ht : t < 2 * k)
    (hd : d ≤ k) (he : e ≤ k + 1) :
    evenContent k + 2 + 2 * d * (d + 1) ≤
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) 0
        (k - d) (k + 2 + e)).exponent := by
  rw [canonical_window_numerator_even_gaps k t d e ht hd he]
  omega

/-- The odd right quadratic has minimum zero, attained at `e=0`. -/
theorem canonical_window_numerator_odd_right_gap_minimum
    (k t d e : Nat) (ht : t < 2 * k + 1)
    (hd : d ≤ k + 1) (he : e ≤ k + 2) :
    oddContent k + 2 * d * d ≤
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) 0
        (k + 1 - d) (k + 2 + e)).exponent := by
  rw [canonical_window_numerator_odd_gaps k t d e ht hd he]
  omega

/-! ## 4. Canonical coefficient scales -/

/-- Central coefficient scale for an even-length numerator atom. -/
def evenNumeratorCoefficientScale (k : Nat) : Nat :=
  ((k + 1) * (k + 2)) * ((k + 2) * (k + 3))

/-- Central coefficient scale for an even-length midpoint atom, including the
factor two needed by the collected `j=1` component. -/
def evenMidpointCoefficientScale (k : Nat) : Nat :=
  2 * (((k + 2) * (k + 2)) * ((k + 2) * (k + 2)))

/-- Uniform coefficient reserve for one even canonical atom pair. -/
def evenPairCoefficientReserve (k : Nat) : Nat :=
  evenNumeratorCoefficientScale k * evenMidpointCoefficientScale k

/-- Central coefficient scale for an odd-length numerator atom. -/
def oddNumeratorCoefficientScale (k : Nat) : Nat :=
  ((k + 2) * (k + 2)) * ((k + 3) * (k + 3))

/-- Central coefficient scale for an odd-length midpoint atom, including the
factor two needed by the collected `j=1` component. -/
def oddMidpointCoefficientScale (k : Nat) : Nat :=
  2 * (((k + 2) * (k + 3)) * ((k + 2) * (k + 3)))

/-- Uniform coefficient reserve for one odd canonical atom pair. -/
def oddPairCoefficientReserve (k : Nat) : Nat :=
  oddNumeratorCoefficientScale k * oddMidpointCoefficientScale k

/-- Every even canonical numerator selector is bounded by the product of its
two central odd-antidiagonal coefficients. -/
theorem canonical_numerator_even_coefficient_le_all
    (k t i p q : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i) :
    (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).coefficientNat ≤
      evenNumeratorCoefficientScale k := by
  rw [canonical_a_atom_coefficient_all (2 * k) t i p q ht]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
  have hl := antidiagonalCoefficient_odd_center_max
    k (canonicalALeftIndex (t + 1) i p)
    (canonicalALeftIndex_le (2 * k) t i p ht hp)
  have hr := antidiagonalCoefficient_odd_center_max
    (k + 1) (canonicalARightIndex (t + 1) i q)
    (by
      rw [← show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
      exact canonicalARightIndex_le (2 * k) t i q ht hq)
  exact Nat.mul_le_mul hl hr

/-- Every odd canonical numerator selector is bounded by the product of its
two central even-antidiagonal coefficients. -/
theorem canonical_numerator_odd_coefficient_le_all
    (k t i p q : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i) :
    (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).coefficientNat ≤
      oddNumeratorCoefficientScale k := by
  rw [canonical_a_atom_coefficient_all (2 * k + 1) t i p q ht]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
  have hl := antidiagonalCoefficient_even_center_max
    (k + 1) (canonicalALeftIndex (t + 1) i p)
    (by
      rw [← show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      exact canonicalALeftIndex_le (2 * k + 1) t i p ht hp)
  have hr := antidiagonalCoefficient_even_center_max
    (k + 2) (canonicalARightIndex (t + 1) i q)
    (by
      rw [← show 2 * k + 1 + 3 = 2 * (k + 2) by omega]
      exact canonicalARightIndex_le (2 * k + 1) t i q ht hq)
  exact Nat.mul_le_mul hl hr

/-- Every even canonical midpoint selector, including the doubled `j=1`
family, is bounded by twice the squared central coefficient. -/
theorem canonical_midpoint_even_coefficient_le_all
    (k t j u v : Nat) (ht : t < 2 * k)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).coefficientNat ≤
      evenMidpointCoefficientScale k := by
  rw [canonical_m_atom_coefficient_all (2 * k) t j u v ht]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega]
  have hl := antidiagonalCoefficient_even_center_max
    (k + 1) (canonicalMLeftIndex (t + 1) j u)
    (by
      rw [← show 2 * k + 2 = 2 * (k + 1) by omega]
      exact canonicalMLeftIndex_le (2 * k) t j u ht hu)
  have hr := antidiagonalCoefficient_even_center_max
    (k + 1) (canonicalMRightIndex (t + 1) j v)
    (by
      rw [← show 2 * k + 2 = 2 * (k + 1) by omega]
      exact canonicalMRightIndex_le (2 * k) t j v ht hv)
  exact Nat.mul_le_mul (midpointCoefficientMultiplicity_le_two j)
    (Nat.mul_le_mul hl hr)

/-- Every odd canonical midpoint selector, including the doubled `j=1`
family, is bounded by twice the squared two-center coefficient. -/
theorem canonical_midpoint_odd_coefficient_le_all
    (k t j u v : Nat) (ht : t < 2 * k + 1)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).coefficientNat ≤
      oddMidpointCoefficientScale k := by
  rw [canonical_m_atom_coefficient_all (2 * k + 1) t j u v ht]
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
  have hl := antidiagonalCoefficient_odd_center_max
    (k + 1) (canonicalMLeftIndex (t + 1) j u)
    (by
      rw [← show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
      exact canonicalMLeftIndex_le (2 * k + 1) t j u ht hu)
  have hr := antidiagonalCoefficient_odd_center_max
    (k + 1) (canonicalMRightIndex (t + 1) j v)
    (by
      rw [← show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
      exact canonicalMRightIndex_le (2 * k + 1) t j v ht hv)
  exact Nat.mul_le_mul (midpointCoefficientMultiplicity_le_two j)
    (Nat.mul_le_mul hl hr)

/-- The natural coefficient mass of every even canonical atom pair is bounded
by the parity-central reserve. -/
theorem canonical_even_pair_coefficient_le_reserve_all
    (k t i j p q u v : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).coefficientNat *
        (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).coefficientNat ≤
      evenPairCoefficientReserve k := by
  exact Nat.mul_le_mul
    (canonical_numerator_even_coefficient_le_all k t i p q ht hp hq)
    (canonical_midpoint_even_coefficient_le_all k t j u v ht hu hv)

/-- The natural coefficient mass of every odd canonical atom pair is bounded
by the parity-central reserve. -/
theorem canonical_odd_pair_coefficient_le_reserve_all
    (k t i j p q u v : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).coefficientNat *
        (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).coefficientNat ≤
      oddPairCoefficientReserve k := by
  exact Nat.mul_le_mul
    (canonical_numerator_odd_coefficient_le_all k t i p q ht hp hq)
    (canonical_midpoint_odd_coefficient_le_all k t j u v ht hu hv)

/-! ## 5. Quotient endpoint-degree consequences -/

/-- Total degree of an endpoint monomial in the square-gap quotient after
removing common `(wh)^content`. -/
def quotientEndpointDegree (content numerator midpoint : Nat) : Nat :=
  numerator + midpoint - 2 - 2 * content

/-- If the numerator supplies at least the common content and the midpoint is
the adverse (higher-exponent) endpoint, then the half-exponent chain length is
controlled by half of the quotient endpoint degree, with the two powers spent
by division restored. -/
theorem adverse_chain_length_le_endpoint_half
    (content numerator midpoint : Nat)
    (hcontent : content ≤ numerator) (hadverse : numerator ≤ midpoint)
    (hcontentEven : content % 2 = 0)
    (hnumeratorEven : numerator % 2 = 0)
    (hmidpointEven : midpoint % 2 = 0) :
    midpoint / 2 - numerator / 2 ≤
      (quotientEndpointDegree content numerator midpoint + 2) / 2 := by
  unfold quotientEndpointDegree
  omega

/-- Every even canonical atom pair has enough combined exponent to remove two
copies of common content and the two powers spent by the square gap. -/
theorem canonical_even_endpoint_balance_all
    (k t i j p q u v : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    2 * evenContent k + 2 ≤
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent +
        (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent := by
  have ha := canonical_numerator_even_content_lower_all k t i p q ht hp hq
  have hm := canonical_midpoint_even_content_lower_all k t j u v ht hu hv
  omega

/-- In odd length every canonical atom pair contains two copies of the common
content.  A further two-unit gap is exactly the remaining classification
needed for a nonzero endpoint discount. -/
theorem canonical_odd_endpoint_balance_all
    (k t i j p q u v : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    2 * oddContent k ≤
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent +
        (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent := by
  have ha := canonical_numerator_odd_content_lower_all k t i p q ht hp hq
  have hm := canonical_midpoint_odd_content_lower_all k t j u v ht hu hv
  omega

/-- Classification-independent adverse-chain bound for every even canonical
component selector. -/
theorem canonical_even_adverse_chain_length_le_endpoint_half_all
    (k t i j p q u v : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hadverse :
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent ≤
        (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent) :
    (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent / 2 -
        (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent / 2 ≤
      (quotientEndpointDegree (evenContent k)
        (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent
        (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent + 2) / 2 := by
  apply adverse_chain_length_le_endpoint_half
  · exact Nat.le_trans (by omega)
      (canonical_numerator_even_content_lower_all k t i p q ht hp hq)
  · exact hadverse
  · simp [evenContent, Nat.mul_mod]
  · exact aAtomicMonomial_exponent_even
      (t + 1) (2 * k - 1 - t) i p q hp hq
  · exact mAtomicMonomial_exponent_even
      (t + 1) (2 * k - 1 - t) j u v hu hv

/-- Classification-independent adverse-chain bound for every odd canonical
component selector. -/
theorem canonical_odd_adverse_chain_length_le_endpoint_half_all
    (k t i j p q u v : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hadverse :
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent ≤
        (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent) :
    (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent / 2 -
        (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent / 2 ≤
      (quotientEndpointDegree (oddContent k)
        (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent
        (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent + 2) / 2 := by
  apply adverse_chain_length_le_endpoint_half
  · exact canonical_numerator_odd_content_lower_all k t i p q ht hp hq
  · exact hadverse
  · simp [oddContent, Nat.add_mod, Nat.mul_mod]
  · exact aAtomicMonomial_exponent_even
      (t + 1) (2 * k + 1 - 1 - t) i p q hp hq
  · exact mAtomicMonomial_exponent_even
      (t + 1) (2 * k + 1 - 1 - t) j u v hu hv

/-- Converting separate numerator and midpoint content gaps into the endpoint
degree of their divided determinant. -/
theorem quotientEndpointDegree_of_gaps
    (content numerator midpoint numeratorGap midpointGap : Nat)
    (hn : content + numeratorGap ≤ numerator)
    (hm : content + midpointGap ≤ midpoint)
    (hgap : 2 ≤ numeratorGap + midpointGap) :
    numeratorGap + midpointGap - 2 ≤
      quotientEndpointDegree content numerator midpoint := by
  unfold quotientEndpointDegree
  omega

/-- Even midpoint displacement `d`, together with the unavoidable two-unit
numerator center gap, forces endpoint degree at least `4d²`. -/
theorem even_adverse_endpoint_degree_lower
    (k d numerator midpoint : Nat)
    (hn : evenContent k + 2 ≤ numerator)
    (hm : evenContent k + 4 * d * d ≤ midpoint) :
    4 * d * d ≤
      quotientEndpointDegree (evenContent k) numerator midpoint := by
  have h := quotientEndpointDegree_of_gaps
    (evenContent k) numerator midpoint 2 (4 * d * d) hn hm (by omega)
  simpa only [Nat.add_sub_cancel_left] using h

/-- Odd midpoint displacement `d≥1` forces endpoint degree at least
`4d(d+1)-2`, even before any positive numerator gap is used. -/
theorem odd_adverse_endpoint_degree_lower
    (k d numerator midpoint : Nat) (hd : 1 ≤ d)
    (hn : oddContent k ≤ numerator)
    (hm : oddContent k + 4 * d * (d + 1) ≤ midpoint) :
    4 * d * (d + 1) - 2 ≤
      quotientEndpointDegree (oddContent k) numerator midpoint := by
  have hd4 : 2 ≤ 4 * d * (d + 1) := by
    have h4d : 4 ≤ 4 * d := by
      simpa using Nat.mul_le_mul_left 4 hd
    have hprod : 4 * d ≤ (4 * d) * (d + 1) :=
      Nat.le_mul_of_pos_right (4 * d) (by omega)
    exact Nat.le_trans (by decide) (Nat.le_trans h4d hprod)
  simpa only [Nat.zero_add] using
    (quotientEndpointDegree_of_gaps
      (oddContent k) numerator midpoint 0 (4 * d * (d + 1))
        hn hm (by simpa only [Nat.zero_add] using hd4))

/-! ## 5. Homogeneous-chain endpoint bounds -/

/-- Pull the common `x^base y^base` factor out of every homogeneous-chain
term.  This exact identity separates the common content from the endpoint
degree which supplies the physical discount. -/
theorem homChain_common_base (x y : Q') (base : Nat) : ∀ len,
    homChain x y base len ≈
      (qpow x base * qpow y base) * homChain x y 0 len
  | 0 => by
      simp only [homChain]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  | n + 1 => by
      simp only [homChain, Nat.zero_add]
      have ih := homChain_common_base x y base n
      have hxadd := qpow_add x base n
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ (qpow y base) hxadd)
          (Q'.mul_eqv_congr_left y _ _ ih)) ?_
      atomwise_ring

/-- Base-zero chain bound: each of the `len` homogeneous terms is at most
the upper endpoint power `x^(len-1)` when `0 ≤ y ≤ x`. -/
theorem homChain_zero_le_length_mul_high
    {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hyx : y ≤ x) :
    ∀ len, homChain x y 0 len ≤ Q'.ofNat len * qpow x (len - 1)
  | 0 => by
      unfold homChain
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | 1 => by
      simp only [homChain, qpow]
      exact Q'.le_of_eqv (by atomwise_ring)
  | n + 2 => by
      have ih := homChain_zero_le_length_mul_high hx0 hy0 hyx (n + 1)
      have ih' : homChain x y 0 (n + 1) ≤
          Q'.ofNat (n + 1) * qpow x n := by
        simpa only [Nat.add_sub_cancel] using ih
      have hymul := Q'.mul_le_mul_of_nonneg_left _ _ y ih' hy0
      have hbound0 : (0 : Q') ≤ Q'.ofNat (n + 1) * qpow x n :=
        Q'.mul_nonneg _ _ (zero_le_ofNat _)
          (qpow_nonneg x hx0 n)
      have hyToX := Q'.mul_le_mul_of_nonneg_right y x
        (Q'.ofNat (n + 1) * qpow x n) hyx hbound0
      have htail : y * homChain x y 0 (n + 1) ≤
          Q'.ofNat (n + 1) * qpow x (n + 1) := by
        have htailEq :
            x * (Q'.ofNat (n + 1) * qpow x n) ≈
              Q'.ofNat (n + 1) * qpow x (n + 1) := by
          change x * (Q'.ofNat (n + 1) * qpow x n) ≈
            Q'.ofNat (n + 1) * (qpow x n * x)
          atomwise_ring
        exact Q'.le_trans' _ _ _ hymul
          (Q'.le_trans' _ _ _ hyToX (Q'.le_of_eqv htailEq))
      have hadd := Q'.add_le_add_left (qpow x (n + 1)) _ _ htail
      unfold homChain
      rw [show n + 2 - 1 = n + 1 by omega]
      have hcast : Q'.ofNat (n + 2) ≈
          Q'.ofNat (n + 1) + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (n + 1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hhead : qpow x (0 + (n + 1)) * qpow y 0 ≈
          qpow x (n + 1) := by
        simp only [Nat.zero_add, qpow_zero]
        exact Q'.mul_one_eqv _
      have hsum : qpow x (n + 1) +
          Q'.ofNat (n + 1) * qpow x (n + 1) ≈
            Q'.ofNat (n + 2) * qpow x (n + 1) := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (n + 1) + (1 : Q')) * qpow x (n + 1)) _ ?_ ?_
        · atomwise_ring
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hcast)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (Q'.add_eqv_congr_right _ _ _ hhead))
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hsum))

/-- **Generic adverse-chain endpoint bound.**  After extracting common base
`base`, a length-`len` chain is at most `len` copies of the largest endpoint
monomial `x^(2*base+len-1)`. -/
theorem homChain_le_length_mul_endpoint
    {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hyx : y ≤ x)
    (base len : Nat) :
    homChain x y base len ≤
      Q'.ofNat len * qpow x (2 * base + len - 1) := by
  cases len with
  | zero =>
      unfold homChain
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ n =>
      have hzero := homChain_zero_le_length_mul_high
        hx0 hy0 hyx (n + 1)
      have hzero' : homChain x y 0 (n + 1) ≤
          Q'.ofNat (n + 1) * qpow x n := by
        simpa only [Nat.add_sub_cancel] using hzero
      have hfactor0 : (0 : Q') ≤ qpow x base * qpow y base :=
        Q'.mul_nonneg _ _
          (qpow_nonneg x hx0 base) (qpow_nonneg y hy0 base)
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _
        (qpow x base * qpow y base) hzero' hfactor0
      have hpowY : qpow y base ≤ qpow x base :=
        qpow_mono hy0 hyx base
      have hpowX0 : (0 : Q') ≤ qpow x base := qpow_nonneg x hx0 base
      have hcommon : qpow x base * qpow y base ≤ qpow x (2 * base) := by
        have hprod := Q'.mul_le_mul_of_nonneg_left _ _ _
          hpowY hpowX0
        exact Q'.le_trans' _ _ _ hprod
          (Q'.le_of_eqv (Q'.eqv_symm (by
            rw [show 2 * base = base + base by omega]
            exact qpow_add x base base)))
      have hright0 : (0 : Q') ≤
          Q'.ofNat (n + 1) * qpow x n :=
        Q'.mul_nonneg _ _ (zero_le_ofNat _)
          (qpow_nonneg x hx0 n)
      have hcommonMul := Q'.mul_le_mul_of_nonneg_right _ _
        (Q'.ofNat (n + 1) * qpow x n) hcommon hright0
      have hnormalize :
          qpow x (2 * base) *
              (Q'.ofNat (n + 1) * qpow x n) ≈
            Q'.ofNat (n + 1) * qpow x (2 * base + n) := by
        have hp := qpow_add x (2 * base) n
        change qpow x (2 * base) *
              (Q'.ofNat (n + 1) * qpow x n) ≈
            Q'.ofNat (n + 1) * qpow x (2 * base + n)
        refine Q'.eqv_trans _
          (Q'.ofNat (n + 1) *
            (qpow x (2 * base) * qpow x n)) _ (by atomwise_ring) ?_
        exact Q'.mul_eqv_congr_left (Q'.ofNat (n + 1)) _ _
          (Q'.eqv_symm hp)
      have hfactor := homChain_common_base x y base (n + 1)
      rw [show 2 * base + (n + 1) - 1 = 2 * base + n by omega]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
        (Q'.le_trans' _ _ _ hmul
          (Q'.le_trans' _ _ _ hcommonMul
            (Q'.le_of_eqv hnormalize)))

#print axioms antidiagonalExponent_even_left
#print axioms antidiagonalExponent_odd_left
#print axioms antidiagonalExponent_even_right
#print axioms antidiagonalExponent_odd_right
#print axioms antidiagonalExponent_even_center_minimum
#print axioms antidiagonalExponent_odd_center_minimum
#print axioms antidiagonalCoefficient_even_center_max
#print axioms antidiagonalCoefficient_odd_center_max
#print axioms twice_antidiagonalExponent_eq_centeredSquare_add
#print axioms canonical_a_atom_exponent_all
#print axioms canonical_m_atom_exponent_all
#print axioms canonicalALeftIndex_le
#print axioms canonicalARightIndex_le
#print axioms canonicalMLeftIndex_le
#print axioms canonicalMRightIndex_le
#print axioms canonical_midpoint_atom_exponent
#print axioms evenContent_eq_center
#print axioms oddContent_eq_center
#print axioms canonical_midpoint_even_content_lower_all
#print axioms canonical_midpoint_odd_content_lower_all
#print axioms canonical_midpoint_even_left_shift
#print axioms canonical_midpoint_odd_left_shift
#print axioms canonical_window_numerator_atom_exponent
#print axioms even_window_numerator_center
#print axioms odd_window_numerator_center
#print axioms canonical_numerator_even_content_lower_all
#print axioms canonical_numerator_odd_content_lower_all
#print axioms canonical_window_numerator_even_gaps
#print axioms canonical_window_numerator_odd_gaps
#print axioms canonical_window_numerator_even_right_gap_minimum
#print axioms canonical_window_numerator_odd_right_gap_minimum
#print axioms canonical_numerator_even_coefficient_le_all
#print axioms canonical_numerator_odd_coefficient_le_all
#print axioms canonical_midpoint_even_coefficient_le_all
#print axioms canonical_midpoint_odd_coefficient_le_all
#print axioms canonical_even_pair_coefficient_le_reserve_all
#print axioms canonical_odd_pair_coefficient_le_reserve_all
#print axioms adverse_chain_length_le_endpoint_half
#print axioms canonical_even_endpoint_balance_all
#print axioms canonical_odd_endpoint_balance_all
#print axioms canonical_even_adverse_chain_length_le_endpoint_half_all
#print axioms canonical_odd_adverse_chain_length_le_endpoint_half_all
#print axioms quotientEndpointDegree_of_gaps
#print axioms even_adverse_endpoint_degree_lower
#print axioms odd_adverse_endpoint_degree_lower
#print axioms homChain_common_base
#print axioms homChain_zero_le_length_mul_high
#print axioms homChain_le_length_mul_endpoint

end YMGap.Continuum.CoreBAtomwiseGapBounds
