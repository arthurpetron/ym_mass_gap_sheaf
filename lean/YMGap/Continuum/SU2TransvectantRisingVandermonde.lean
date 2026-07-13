/-
# An all-order rising Chu--Vandermonde identity for transvectant Gram sums

The highest-weight row of an order-`k` Cayley transvectant contains the
positive convolution

  sum_{u=0}^k C(m-u,k-u) C(n-k+u,u).

This file proves its closed form constructively for arbitrary natural labels.
The proof first establishes the more transparent rising convolution

  sum_{u=0}^k C(a+k-u,a) C(b+u,b) = C(a+b+k+1,a+b+1)

by a two-dimensional Pascal induction, and then specializes with
`a=m-k`, `b=n-k`.  A final theorem lifts the identity to the exact rational
factorial carrier `tvBinomQ` used by the transvectant development.
-/

import YMGap.Continuum.SU2TransvectantFactorialRecurrence
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2TransvectantRisingVandermonde

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence

local infix:50 " ≈ " => Q'.eqv

/-! ## A small natural finite-sum substrate -/

def natFinSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => natFinSum f N + f N

@[simp] theorem natFinSum_zero (f : Nat → Nat) : natFinSum f 0 = 0 := rfl

@[simp] theorem natFinSum_succ (f : Nat → Nat) (N : Nat) :
    natFinSum f (N + 1) = natFinSum f N + f N := rfl

theorem natFinSum_congr (f g : Nat → Nat) : ∀ N,
    (∀ i, i < N → f i = g i) → natFinSum f N = natFinSum g N
  | 0, _ => rfl
  | N + 1, h => by
      rw [natFinSum_succ, natFinSum_succ]
      rw [natFinSum_congr f g N (fun i hi => h i (by omega))]
      rw [h N (by omega)]

theorem natFinSum_add (f g : Nat → Nat) : ∀ N,
    natFinSum (fun i => f i + g i) N = natFinSum f N + natFinSum g N
  | 0 => by simp
  | N + 1 => by
      simp only [natFinSum_succ, natFinSum_add f g N]
      omega

/-! ## Pascal symmetry and edges -/

@[simp] theorem choose_zero_right (n : Nat) : PNPaths.choose n 0 = 1 := by
  cases n <;> rfl

theorem choose_self : ∀ n : Nat, PNPaths.choose n n = 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose, choose_self n]
      rw [choose_zero_of_lt n (n + 1) (by omega)]

theorem choose_symm : ∀ n r : Nat, r ≤ n →
    PNPaths.choose n r = PNPaths.choose n (n - r)
  | 0, r, hr => by
      have : r = 0 := by omega
      subst r
      rfl
  | n + 1, 0, _ => by
      simp only [Nat.sub_zero, choose_zero_right, choose_self]
  | n + 1, r + 1, hr => by
      by_cases htop : r = n
      · subst r
        rw [Nat.sub_self]
        simp only [choose_self, choose_zero_right]
      · have hrn : r < n := by omega
        have hs1 : n + 1 - (r + 1) = (n - (r + 1)) + 1 := by omega
        rw [hs1]
        simp only [PNPaths.choose]
        rw [choose_symm n r (by omega)]
        rw [choose_symm n (r + 1) (by omega)]
        have hsub : n - r = n - (r + 1) + 1 := by omega
        rw [hsub]
        exact Nat.add_comm _ _

/-! ## The rising convolution and its exact recurrence -/

def risingChuTerm (a b k u : Nat) : Nat :=
  PNPaths.choose (a + (k - u)) a * PNPaths.choose (b + u) b

def risingChuSum (a b k : Nat) : Nat :=
  natFinSum (risingChuTerm a b k) (k + 1)

theorem risingChuTerm_pascal (a b k u : Nat) (hu : u ≤ k) :
    risingChuTerm (a + 1) b (k + 1) u =
      risingChuTerm a b (k + 1) u + risingChuTerm (a + 1) b k u := by
  unfold risingChuTerm
  have hsub : k + 1 - u = k - u + 1 := by omega
  rw [hsub]
  have htop : a + 1 + (k - u + 1) = (a + (k - u) + 1) + 1 := by omega
  have hright : a + 1 + (k - u) = a + (k - u) + 1 := by omega
  rw [htop, hright]
  simp only [PNPaths.choose]
  exact Nat.add_mul _ _ _

theorem risingChuTerm_endpoint (a b k : Nat) :
    risingChuTerm (a + 1) b (k + 1) (k + 1) =
      risingChuTerm a b (k + 1) (k + 1) := by
  simp [risingChuTerm, choose_self]

theorem risingChuTerm_zero_left (b k u : Nat) :
    risingChuTerm 0 b k u = PNPaths.choose (b + u) b := by
  simp [risingChuTerm]

/-- The contiguous Pascal recurrence for the complete rising convolution. -/
theorem risingChuSum_contiguous (a b k : Nat) :
    risingChuSum (a + 1) b (k + 1) =
      risingChuSum (a + 1) b k + risingChuSum a b (k + 1) := by
  change
    natFinSum (risingChuTerm (a + 1) b (k + 1)) (k + 1) +
        risingChuTerm (a + 1) b (k + 1) (k + 1) =
      natFinSum (risingChuTerm (a + 1) b k) (k + 1) +
        (natFinSum (risingChuTerm a b (k + 1)) (k + 1) +
          risingChuTerm a b (k + 1) (k + 1))
  have hprefix :
      natFinSum (risingChuTerm (a + 1) b (k + 1)) (k + 1) =
        natFinSum (fun u =>
          risingChuTerm a b (k + 1) u + risingChuTerm (a + 1) b k u) (k + 1) :=
    natFinSum_congr _ _ _ (fun u hu => risingChuTerm_pascal a b k u (by omega))
  rw [hprefix, natFinSum_add]
  rw [risingChuTerm_endpoint]
  omega

/-- Exact `a=0` base: the rising convolution is the Pascal hockey stick. -/
theorem risingChuSum_zero_left (b : Nat) : ∀ k,
    risingChuSum 0 b k = PNPaths.choose (b + k + 1) (b + 1)
  | 0 => by
      simp [risingChuSum, risingChuTerm, choose_self]
  | k + 1 => by
      unfold risingChuSum
      rw [natFinSum_succ]
      have hprefix :
          natFinSum (risingChuTerm 0 b (k + 1)) (k + 1) =
            risingChuSum 0 b k := by
        unfold risingChuSum
        exact natFinSum_congr _ _ _ (fun u _ => by
          rw [risingChuTerm_zero_left, risingChuTerm_zero_left])
      rw [hprefix]
      rw [risingChuSum_zero_left b k]
      simp only [risingChuTerm, Nat.sub_self, Nat.zero_add, choose_zero_right, Nat.one_mul]
      have htop : b + (k + 1) = b + k + 1 := by omega
      rw [htop]
      simp only [PNPaths.choose]
      exact Nat.add_comm _ _

/-- **All-order rising Chu--Vandermonde convolution.** -/
theorem risingChuVandermonde : ∀ a b k : Nat,
    risingChuSum a b k = PNPaths.choose (a + b + k + 1) (a + b + 1)
  | 0, b, k => by
      simpa only [Nat.zero_add] using risingChuSum_zero_left b k
  | a + 1, b, 0 => by
      simp [risingChuSum, risingChuTerm, choose_self]
  | a + 1, b, k + 1 => by
      rw [risingChuSum_contiguous]
      rw [risingChuVandermonde (a + 1) b k]
      rw [risingChuVandermonde a b (k + 1)]
      have htop : a + 1 + b + (k + 1) + 1 = (a + b + k + 2) + 1 := by omega
      have hleft0 : a + 1 + b + k + 1 = a + b + k + 2 := by omega
      have hleft1 : a + b + (k + 1) + 1 = a + b + k + 2 := by omega
      have hidx0 : a + 1 + b + 1 = (a + b + 1) + 1 := by omega
      rw [htop, hleft0, hleft1, hidx0]
      simp only [PNPaths.choose]
      exact Nat.add_comm _ _

/-! ## The shifted transvectant form -/

def transvectChuSum (m n k : Nat) : Nat :=
  natFinSum (fun u =>
    PNPaths.choose (m - u) (k - u) *
      PNPaths.choose (n - k + u) u) (k + 1)

theorem transvectChuTerm_eq_rising (m n k u : Nat)
    (hm : k ≤ m) (hu : u ≤ k) :
    PNPaths.choose (m - u) (k - u) * PNPaths.choose (n - k + u) u =
      risingChuTerm (m - k) (n - k) k u := by
  unfold risingChuTerm
  have hm1 : m - u = (m - k) + (k - u) := by omega
  have hn1 : n - k + u = (n - k) + u := rfl
  rw [hm1, hn1]
  rw [choose_symm ((m - k) + (k - u)) (k - u) (by omega)]
  rw [choose_symm ((n - k) + u) u (by omega)]
  have hcomp0 : (m - k) + (k - u) - (k - u) = m - k := by omega
  have hcomp1 : (n - k) + u - u = n - k := by omega
  rw [hcomp0, hcomp1]

/-- The exact convolution occurring in the highest-output row of the
order-`k` transvectant. -/
theorem transvectChuVandermonde (m n k : Nat) (hm : k ≤ m) (hn : k ≤ n) :
    transvectChuSum m n k = PNPaths.choose (m + n - k + 1) k := by
  unfold transvectChuSum
  have hcongr :
      natFinSum (fun u =>
        PNPaths.choose (m - u) (k - u) * PNPaths.choose (n - k + u) u) (k + 1) =
        natFinSum (risingChuTerm (m - k) (n - k) k) (k + 1) :=
    natFinSum_congr _ _ _ (fun u hu =>
      transvectChuTerm_eq_rising m n k u hm (by omega))
  rw [hcongr]
  change risingChuSum (m - k) (n - k) k = _
  rw [risingChuVandermonde]
  have htop : (m - k) + (n - k) + k + 1 = m + n - k + 1 := by omega
  rw [htop]
  rw [choose_symm (m + n - k + 1) ((m - k) + (n - k) + 1) (by omega)]
  have hcomp : m + n - k + 1 - ((m - k) + (n - k) + 1) = k := by omega
  rw [hcomp]

/-! ## Lift to exact constructive rationals -/

private theorem ofNat_add_eqv (a b : Nat) :
    Q'.ofNat (a + b) ≈ Q'.ofNat a + Q'.ofNat b := by
  show (Q'.ofNat (a + b)).num * ((Q'.ofNat a + Q'.ofNat b).den : Int) =
    (Q'.ofNat a + Q'.ofNat b).num * ((Q'.ofNat (a + b)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

theorem finSum_ofNat_natFinSum (f : Nat → Nat) : ∀ N,
    finSum (fun u => Q'.ofNat (f u)) N ≈ Q'.ofNat (natFinSum f N)
  | 0 => Q'.ofNat_zero_eqv
  | N + 1 => by
      simp only [finSum_succ, natFinSum_succ]
      refine Q'.eqv_trans _ (Q'.ofNat (natFinSum f N) + Q'.ofNat (f N)) _
        (Q'.add_eqv_congr_right _ _ _ (finSum_ofNat_natFinSum f N)) ?_
      exact Q'.eqv_symm (ofNat_add_eqv _ _)

def transvectChuSumQ (m n k : Nat) : Q' :=
  finSum (fun u =>
    tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u) (k + 1)

/-- Exact-rational Chu--Vandermonde collapse for the factorial binomials that
occur in the transvectant Gram row. -/
theorem transvectChuVandermondeQ (m n k : Nat) (hm : k ≤ m) (hn : k ≤ n) :
    transvectChuSumQ m n k ≈ tvBinomQ (m + n - k + 1) k := by
  unfold transvectChuSumQ
  let f : Nat → Nat := fun u =>
    PNPaths.choose (m - u) (k - u) * PNPaths.choose (n - k + u) u
  have hterms :
      finSum (fun u =>
        tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u) (k + 1) ≈
        finSum (fun u => Q'.ofNat (f u)) (k + 1) := by
    refine finSum_eqv_congr _ _ (fun u => ?_) (k + 1)
    refine Q'.eqv_trans _
      (Q'.ofNat (PNPaths.choose (m - u) (k - u)) *
        Q'.ofNat (PNPaths.choose (n - k + u) u)) _
      (Q'.eqv_trans _
        (Q'.ofNat (PNPaths.choose (m - u) (k - u)) *
          tvBinomQ (n - k + u) u) _
        (Q'.mul_eqv_congr_right _ _ _
          (tvBinomQ_eqv_choose_all (m - u) (k - u)))
        (Q'.mul_eqv_congr_left _ _ _
          (tvBinomQ_eqv_choose_all (n - k + u) u))) ?_
    exact Q'.eqv_symm (ofNat_mul_eqv _ _)
  refine Q'.eqv_trans _ _ _ hterms ?_
  refine Q'.eqv_trans _ (Q'.ofNat (natFinSum f (k + 1))) _
    (finSum_ofNat_natFinSum f (k + 1)) ?_
  have hnat : natFinSum f (k + 1) = PNPaths.choose (m + n - k + 1) k := by
    exact transvectChuVandermonde m n k hm hn
  rw [hnat]
  exact Q'.eqv_symm (tvBinomQ_eqv_choose_all (m + n - k + 1) k)

end YMGap.Continuum.SU2TransvectantRisingVandermonde

#print axioms YMGap.Continuum.SU2TransvectantRisingVandermonde.risingChuSum_contiguous
#print axioms YMGap.Continuum.SU2TransvectantRisingVandermonde.risingChuSum_zero_left
#print axioms YMGap.Continuum.SU2TransvectantRisingVandermonde.risingChuVandermonde
#print axioms YMGap.Continuum.SU2TransvectantRisingVandermonde.transvectChuVandermonde
#print axioms YMGap.Continuum.SU2TransvectantRisingVandermonde.transvectChuVandermondeQ
