/-
# The constructive SU(2) Cartan branching kernel

A face-strand switch does more than reassociate a fixed tensor product: it
splits one symmetric power into two packets of strands and later recombines
packets into a new symmetric power.  For binary forms this is the highest-spin
(Cartan) Clebsch--Gordan channel.

This module constructs its exact coefficient law.  At output monomial index
`s`, the split index `i` has the hypergeometric weight

  C(m,i) C(n,s-i) / C(m+n,s).

An all-label Pascal proof of Vandermonde normalization makes these weights a
finite rational kernel.  The resulting coefficient-level split is a proved
right inverse of order-zero transvectant recombination.  Equivariance of the
split and its insertion into the geometric component switch remain separate
frontiers.

Constructive contract: Mathlib-free, exact `Nat` and `Q'` recursion, explicit
positive denominators, no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2TransvectantRisingVandermonde
import YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2CartanBranchingKernel

set_option maxHeartbeats 1800000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantRisingVandermonde
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Ordinary Pascal--Vandermonde convolution over naturals -/

/-- The ordinary binomial convolution at coefficient index `s`. -/
def chooseConvolution (m n s : Nat) : Nat :=
  natFinSum
    (fun i => PNPaths.choose m i * PNPaths.choose n (s - i)) (s + 1)

private theorem natFinSum_peel_left (f : Nat → Nat) : ∀ N,
    natFinSum f (N + 1) =
      f 0 + natFinSum (fun i => f (i + 1)) N
  | 0 => by simp
  | N + 1 => by
      change natFinSum f (N + 1) + f (N + 1) =
        f 0 + (natFinSum (fun i => f (i + 1)) N + f (N + 1))
      rw [natFinSum_peel_left f N]
      omega

private theorem natFinSum_zero : ∀ N,
    natFinSum (fun _ => 0) N = 0
  | 0 => rfl
  | N + 1 => by simp only [natFinSum_succ, natFinSum_zero N, Nat.add_zero]

theorem chooseConvolution_zero_left (n s : Nat) :
    chooseConvolution 0 n s = PNPaths.choose n s := by
  unfold chooseConvolution
  rw [natFinSum_peel_left
    (fun i => PNPaths.choose 0 i * PNPaths.choose n (s - i)) s]
  have htail :
      natFinSum
          (fun i => PNPaths.choose 0 (i + 1) *
            PNPaths.choose n (s - (i + 1))) s = 0 := by
    refine Eq.trans (natFinSum_congr _ (fun _ => 0) s (fun i _ => ?_))
      (natFinSum_zero s)
    rw [choose_zero_of_lt 0 (i + 1) (by omega), Nat.zero_mul]
  rw [htail]
  simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero, Nat.add_zero]

/-- Pascal recurrence in the first upper label for the complete ordinary
convolution. -/
theorem chooseConvolution_succ_left (m n s : Nat) :
    chooseConvolution (m + 1) n (s + 1) =
      chooseConvolution m n s + chooseConvolution m n (s + 1) := by
  unfold chooseConvolution
  rw [natFinSum_peel_left
    (fun i => PNPaths.choose (m + 1) i *
      PNPaths.choose n (s + 1 - i)) (s + 1)]
  have htail :
      natFinSum
          (fun i => PNPaths.choose (m + 1) (i + 1) *
            PNPaths.choose n (s + 1 - (i + 1))) (s + 1) =
        natFinSum
          (fun i =>
            PNPaths.choose m i * PNPaths.choose n (s - i) +
            PNPaths.choose m (i + 1) * PNPaths.choose n (s - i))
          (s + 1) := by
    apply natFinSum_congr
    intro i hi
    have hsub : s + 1 - (i + 1) = s - i := by omega
    rw [hsub]
    simp only [PNPaths.choose]
    exact Nat.add_mul _ _ _
  rw [htail, natFinSum_add]
  have hnext :
      natFinSum
          (fun i => PNPaths.choose m i *
            PNPaths.choose n (s + 1 - i)) (s + 2) =
        PNPaths.choose n (s + 1) +
          natFinSum
            (fun i => PNPaths.choose m (i + 1) *
              PNPaths.choose n (s - i)) (s + 1) := by
    refine Eq.trans
      (natFinSum_peel_left
        (fun i => PNPaths.choose m i *
          PNPaths.choose n (s + 1 - i)) (s + 1)) ?_
    congr 1
    · simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero]
    · apply natFinSum_congr
      intro i hi
      have hsub : s + 1 - (i + 1) = s - i := by omega
      rw [hsub]
  rw [hnext]
  simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero]
  omega

/-- **Ordinary Vandermonde identity for the repository's constructive Pascal
coefficients.** -/
theorem chooseConvolution_vandermonde : ∀ m n s : Nat,
    chooseConvolution m n s = PNPaths.choose (m + n) s
  | 0, n, s => by
      simpa only [Nat.zero_add] using chooseConvolution_zero_left n s
  | m + 1, n, 0 => by
      unfold chooseConvolution
      simp [natFinSum, choose_zero_right]
  | m + 1, n, s + 1 => by
      rw [chooseConvolution_succ_left]
      rw [chooseConvolution_vandermonde m n s]
      rw [chooseConvolution_vandermonde m n (s + 1)]
      have htop : m + 1 + n = (m + n) + 1 := by omega
      rw [htop]
      simp only [PNPaths.choose]

/-! ## 2. Exact rational Vandermonde and the normalized branching row -/

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (Q'.ofNat (a * b)).num *
      ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num *
      ((Q'.ofNat (a * b)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- Rational ordinary convolution in the exact factorial normalization used
by the transvectant development. -/
def cartanBranchRawMass (m n s : Nat) : Q' :=
  finSum (fun i => tvBinomQ m i * tvBinomQ n (s - i)) (s + 1)

/-- Exact-rational ordinary Vandermonde. -/
theorem cartanBranchRawMass_eq_binom (m n s : Nat) :
    cartanBranchRawMass m n s ≈ tvBinomQ (m + n) s := by
  let f : Nat → Nat := fun i =>
    PNPaths.choose m i * PNPaths.choose n (s - i)
  have hterms : cartanBranchRawMass m n s ≈
      finSum (fun i => Q'.ofNat (f i)) (s + 1) := by
    unfold cartanBranchRawMass
    apply finSum_eqv_congr
    intro i
    refine Q'.eqv_trans _
      (Q'.ofNat (PNPaths.choose m i) *
        Q'.ofNat (PNPaths.choose n (s - i))) _ ?_ ?_
    · exact Q'.eqv_trans _
        (Q'.ofNat (PNPaths.choose m i) * tvBinomQ n (s - i)) _
        (Q'.mul_eqv_congr_right _ _ _ (tvBinomQ_eqv_choose_all m i))
        (Q'.mul_eqv_congr_left _ _ _
          (tvBinomQ_eqv_choose_all n (s - i)))
    · exact Q'.eqv_symm (ofNat_mul_eqv _ _)
  refine Q'.eqv_trans _ _ _ hterms ?_
  refine Q'.eqv_trans _ (Q'.ofNat (natFinSum f (s + 1))) _
    (finSum_ofNat_natFinSum f (s + 1)) ?_
  have hnat : natFinSum f (s + 1) = PNPaths.choose (m + n) s := by
    exact chooseConvolution_vandermonde m n s
  rw [hnat]
  exact Q'.eqv_symm (tvBinomQ_eqv_choose_all (m + n) s)

private theorem tvBinomQ_pos_of_le (n i : Nat) (hi : i ≤ n) :
    (0 : Q') < tvBinomQ n i := by
  unfold tvBinomQ
  rw [if_pos hi]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact n)
  exact Int.natCast_pos.mpr (tvFact_pos n)

/-- One unnormalized hypergeometric split weight. -/
def cartanBranchRawAt (m n s i : Nat) : Q' :=
  tvBinomQ m i * tvBinomQ n (s - i)

/-- The normalized Cartan split kernel at a physically bounded output
monomial index. -/
def cartanBranchKernelAt (m n s : Nat) (hs : s ≤ m + n)
    (i : Nat) : Q' :=
  Q'.divPos (cartanBranchRawAt m n s i) (tvBinomQ (m + n) s)
    (tvBinomQ_pos_of_le (m + n) s hs)

theorem cartanBranchKernelAt_nonnegative (m n s : Nat)
    (hs : s ≤ m + n) (i : Nat) :
    (0 : Q') ≤ cartanBranchKernelAt m n s hs i := by
  unfold cartanBranchKernelAt Q'.divPos cartanBranchRawAt
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (tvBinomQ_nonneg_all m i)
      (tvBinomQ_nonneg_all n (s - i)))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

def cartanBranchRowMass (m n s : Nat) (hs : s ≤ m + n) : Q' :=
  finSum (cartanBranchKernelAt m n s hs) (s + 1)

/-- **The Cartan split weights form an exact finite stochastic row.** -/
theorem cartanBranchKernel_row_normalized (m n s : Nat)
    (hs : s ≤ m + n) :
    cartanBranchRowMass m n s hs ≈ 1 := by
  let D := tvBinomQ (m + n) s
  let hD := tvBinomQ_pos_of_le (m + n) s hs
  let r := Q'.recipPos D hD
  have hpull := RationalTail.finSum_mul_const
    (fun i => cartanBranchRawAt m n s i) r (s + 1)
  have hmass := cartanBranchRawMass_eq_binom m n s
  refine Q'.eqv_trans _ (cartanBranchRawMass m n s * r) _ ?_ ?_
  · exact Q'.eqv_symm (by
      simpa only [cartanBranchRowMass, cartanBranchKernelAt, Q'.divPos,
        D, hD, r, cartanBranchRawMass] using hpull)
  · exact Q'.eqv_trans _ (D * r) _
      (Q'.mul_eqv_congr_right _ _ r hmass)
      (by simpa only [r] using Q'.mul_recipPos_eqv D hD)

/-! ## 3. Split and recombine the highest-spin binary-form channel -/

/-- Coefficient-level Cartan split of a degree-`m+n` binary form into the
highest-spin part of bidegree `(m,n)`. -/
def cartanSplit (m n : Nat) (f : BForm) : BForm2 :=
  fun i j =>
    if hs : i + j ≤ m + n then
      cartanBranchKernelAt m n (i + j) hs i * f (i + j)
    else 0

/-- Recombine a biform through the order-zero transvectant, i.e. polynomial
multiplication/diagonal restriction. -/
def cartanRecombine (m n : Nat) (x : BForm2) : BForm :=
  transvect m n 0 x

/-- **Exact split/recombine law.**  On every physical coefficient of
`V_(m+n)`, the normalized Cartan split is a constructive section of the
order-zero Clebsch--Gordan map. -/
theorem cartanRecombine_split (m n : Nat) (f : BForm)
    (s : Nat) (hs : s ≤ m + n) :
    cartanRecombine m n (cartanSplit m n f) s ≈ f s := by
  have hterms :
      finSum (fun i => cartanSplit m n f i (s - i)) (s + 1) ≈
        finSum (fun i => cartanBranchKernelAt m n s hs i * f s) (s + 1) := by
    apply finSum_eqv_congr_lt
    intro i hi
    have his : i ≤ s := by omega
    have hadd : i + (s - i) = s := Nat.add_sub_of_le his
    unfold cartanSplit
    simp only [hadd, hs, dite_true]
    exact Q'.eqv_refl _
  have hpull := RationalTail.finSum_mul_const
    (cartanBranchKernelAt m n s hs) (f s) (s + 1)
  unfold cartanRecombine transvect OmegaK diag
  exact Q'.eqv_trans _ _ _ hterms
    (Q'.eqv_trans _
      (cartanBranchRowMass m n s hs * f s) _
      (Q'.eqv_symm (by
        simpa only [cartanBranchRowMass] using hpull))
      (Q'.eqv_trans _ ((1 : Q') * f s) _
        (Q'.mul_eqv_congr_right _ _ (f s)
          (cartanBranchKernel_row_normalized m n s hs))
        (Q'.one_mul_eqv (f s))))

end YMGap.Continuum.SU2CartanBranchingKernel

#print axioms YMGap.Continuum.SU2CartanBranchingKernel.chooseConvolution_vandermonde
#print axioms YMGap.Continuum.SU2CartanBranchingKernel.cartanBranchRawMass_eq_binom
#print axioms YMGap.Continuum.SU2CartanBranchingKernel.cartanBranchKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2CartanBranchingKernel.cartanBranchKernel_row_normalized
#print axioms YMGap.Continuum.SU2CartanBranchingKernel.cartanRecombine_split
