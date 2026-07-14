/-
# Factorial square normalization of the signed Racah candidate

This module exposes the closed binary Gram factor associated with one
admissible Clebsch--Gordan channel and begins the arbitrary-label cancellation
which connects the signed rational Racah candidate to the faithful squared
kernel.  The first theorem is the key local cancellation:

  Gram(m,n;k) * Delta(m,n,out)^2
    = m! n! (k!)^2 / out!.

It removes the large triangle denominator exactly and is uniform in every
admissible label.  No square root or measured normalization enters.
-/

import YMGap.Continuum.SU2SignedRacahFactorialCandidate
import YMGap.Continuum.SU2TransvectantAdmissibleExtremal
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.SU2SignedRacahSquareNormalization

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2SignedRacahFactorialCandidate
open YMGap.Continuum.FusionCoreStepRoundD

local infix:50 " ≈ " => Q'.eqv

/-- Numerator of the closed invariant binary transvectant Gram in an
admissible output channel. -/
def closedBinaryGramNum (m n out : Nat) : Nat :=
  let k := couplingOrder m n out
  fact m * fact n * fact k * fact (m + n - k + 1)

/-- Denominator of the same closed binary Gram. -/
def closedBinaryGramDen (m n out : Nat) : Nat :=
  let k := couplingOrder m n out
  fact (m - k) * fact (n - k) * fact out

theorem closedBinaryGramDen_pos (m n out : Nat) :
    0 < closedBinaryGramDen m n out := by
  unfold closedBinaryGramDen
  exact Nat.mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _)

/-- Closed factorial binary Gram, indexed by its physical output label. -/
def closedBinaryGram (m n out : Nat) : Q' :=
  Q'.mkPos (closedBinaryGramNum m n out) (closedBinaryGramDen m n out)
    (closedBinaryGramDen_pos m n out)

/-- The small factorial product left after one binary Gram is paired with its
squared triangle coefficient. -/
def gramTriangleCore (m n out : Nat) : Q' :=
  let k := couplingOrder m n out
  Q'.mkPos (fact m * fact n * (fact k * fact k)) (fact out) (fact_pos out)

/-- **Uniform Gram--triangle cancellation.**  On every admissible SU(2)
channel, the exact closed binary Gram times the corresponding squared triangle
coefficient collapses to `m! n! (k!)^2 / out!`. -/
theorem closedBinaryGram_mul_triSq
    (m n out : Nat) (h : fusionOK m n out = true) :
    closedBinaryGram m n out * triSq m n out ≈
      gramTriangleCore m n out := by
  let k := couplingOrder m n out
  have hs := fusionOK_couplingOrder_spec m n out h
  have hk_m : k ≤ m := by simpa only [k] using hs.2.1
  have hk_n : k ≤ n := by simpa only [k] using hs.2.2.1
  have hout : out + 2 * k = m + n := by simpa only [k] using hs.2.2.2
  have h0 : (m + n - out) / 2 = k := by
    have ht : 2 * k = m + n - out := by simpa only [k] using hs.1
    omega
  have h1 : (m + out - n) / 2 = m - k := by omega
  have h2 : (n + out - m) / 2 = n - k := by omega
  have h3 : (m + n + out) / 2 + 1 = m + n - k + 1 := by omega
  have htriDen : 0 < triSqDen m n out := fact_pos _
  unfold closedBinaryGram gramTriangleCore closedBinaryGramNum
    closedBinaryGramDen triSq triSqNum triSqDen
  dsimp only
  rw [h0, h1, h2, h3]
  unfold Q'.eqv
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  simp only [Q'.mkN, Q'.den]
  have hfac : 0 < fact (m + n - k + 1) := fact_pos _
  rw [show fact (m + n - k + 1) - 1 + 1 = fact (m + n - k + 1) by
    omega]
  dsimp only [k]
  push_cast
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  ac_rfl

/-- Squared triangle coefficients are structurally invariant under a cyclic
permutation of their three labels. -/
theorem triSq_cyclic (x y z : Nat) : triSq x y z = triSq y z x := by
  unfold triSq triSqNum triSqDen
  congr 1
  · simp only [Nat.add_comm]
    ac_rfl
  · congr 2
    omega

theorem triSq_swap_first (x y z : Nat) : triSq x y z = triSq y x z := by
  unfold triSq triSqNum triSqDen
  congr 1
  · simp only [Nat.add_comm]
    ac_rfl
  · congr 2
    omega

theorem triSq_swap_last (x y z : Nat) : triSq x y z = triSq x z y := by
  unfold triSq triSqNum triSqDen
  congr 1
  · simp only [Nat.add_comm]
    ac_rfl
  · congr 2
    omega

/-- The local Gram--triangle cancellation in the cyclic orientation used by
the fourth face of `racahKernel6`. -/
theorem closedBinaryGram_mul_triSq_cyclic
    (m n out : Nat) (h : fusionOK m n out = true) :
    closedBinaryGram m n out * triSq n out m ≈
      gramTriangleCore m n out := by
  rw [← triSq_cyclic m n out]
  exact closedBinaryGram_mul_triSq m n out h

def channelResidualNum (m n out : Nat) : Nat :=
  let k := couplingOrder m n out
  fact (m - k) * fact (n - k)

def channelResidualDen (m n out : Nat) : Nat :=
  let k := couplingOrder m n out
  fact (m + n - k + 1)

theorem channelResidualDen_pos (m n out : Nat) :
    0 < channelResidualDen m n out := by
  unfold channelResidualDen
  exact fact_pos _

def channelResidual (m n out : Nat) : Q' :=
  Q'.mkPos (channelResidualNum m n out) (channelResidualDen m n out)
    (channelResidualDen_pos m n out)

def binaryBaseFactor (m n out : Nat) : Q' :=
  Q'.mkPos (fact m * fact n) (fact out) (fact_pos out)

/-- One admissible binary Gram absorbs the square of its residual factorial
ratio and leaves a simple base factor times the corresponding triangle. -/
theorem closedBinaryGram_mul_residual_square
    (m n out : Nat) (h : fusionOK m n out = true) :
    closedBinaryGram m n out *
        (channelResidual m n out * channelResidual m n out) ≈
      binaryBaseFactor m n out * triSq m n out := by
  let k := couplingOrder m n out
  have hs := fusionOK_couplingOrder_spec m n out h
  have h0 : (m + n - out) / 2 = k := by
    have ht : 2 * k = m + n - out := by simpa only [k] using hs.1
    omega
  have h1 : (m + out - n) / 2 = m - k := by
    have hm : k ≤ m := by simpa only [k] using hs.2.1
    have hout : out + 2 * k = m + n := by simpa only [k] using hs.2.2.2
    omega
  have h2 : (n + out - m) / 2 = n - k := by
    have hn : k ≤ n := by simpa only [k] using hs.2.2.1
    have hout : out + 2 * k = m + n := by simpa only [k] using hs.2.2.2
    omega
  have h3 : (m + n + out) / 2 + 1 = m + n - k + 1 := by
    have hout : out + 2 * k = m + n := by simpa only [k] using hs.2.2.2
    omega
  have hD : 0 < fact (m + n - k + 1) := fact_pos _
  unfold closedBinaryGram closedBinaryGramNum closedBinaryGramDen
    channelResidual channelResidualNum channelResidualDen binaryBaseFactor
    triSq triSqNum triSqDen
  dsimp only
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  simp only [Q'.mkN, Q'.den]
  rw [h0, h1, h2, h3]
  rw [show fact (m + n - k + 1) - 1 + 1 = fact (m + n - k + 1) by omega]
  dsimp only [k]
  push_cast
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  ac_rfl

/-- The signed prefactor separates into the two left contraction factorials
and one residual ratio for each right channel. -/
theorem signedInverseFactor_residual_factorization (a b c d e f : Nat) :
    signedInverseFactor a b c d e f ≈
      (Q'.ofNat (f + 1) *
        (Q'.ofNat (fact (leftInnerOrder a b e)) *
          Q'.ofNat (fact (leftOuterOrder e c d)))) *
        (channelResidual b c f * channelResidual a f d) := by
  unfold signedInverseFactor signedInverseFactorNum signedInverseFactorDen
    channelResidual channelResidualNum channelResidualDen couplingOrder
    rightInnerOrder rightOuterOrder
  dsimp only
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  ac_rfl

/-- The two base factors recombine with the left contraction factorials into
the two left Gram--triangle cores; the intermediate factorials cancel
crosswise. -/
theorem binaryBaseFactor_recombine (a b c d e f : Nat) :
    let K := Q'.ofNat (fact (leftInnerOrder a b e)) *
      Q'.ofNat (fact (leftOuterOrder e c d))
    (K * K) * (binaryBaseFactor b c f * binaryBaseFactor a f d) ≈
      gramTriangleCore a b e * gramTriangleCore e c d := by
  dsimp only
  unfold binaryBaseFactor gramTriangleCore couplingOrder
    leftInnerOrder leftOuterOrder
  dsimp only
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  ac_rfl

private theorem square_eqv_congr {x y : Q'} (h : x ≈ y) : x * x ≈ y * y := by
  refine Q'.eqv_trans _ (y * x) _
    (Q'.mul_eqv_congr_right x y x h) ?_
  exact Q'.mul_eqv_congr_left y x y h

private theorem residual_square_reorder
    (G1 G2 D K R1 R2 : Q') :
    (G1 * G2) * (((D * K) * (R1 * R2)) * ((D * K) * (R1 * R2))) ≈
      (D * D) * ((K * K) *
        ((G1 * (R1 * R1)) * (G2 * (R2 * R2)))) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem residual_core_reorder
    (D K B1 B2 T1 T2 : Q') :
    (D * D) * ((K * K) * ((B1 * T1) * (B2 * T2))) ≈
      (D * D) * (((K * K) * (B1 * B2)) * (T2 * T1)) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The only nonlocal factorial cancellation needed for Racah normalization,
assembled from two one-channel residual cancellations. -/
theorem signedInverseFactor_core_square_normalization
    (a b c d e f : Nat) (hvalid : valid6 a b c d e f = true) :
    (closedBinaryGram b c f * closedBinaryGram a f d) *
        (signedInverseFactor a b c d e f *
          signedInverseFactor a b c d e f) ≈
      (Q'.ofNat (f + 1) * Q'.ofNat (f + 1)) *
        ((gramTriangleCore a b e * gramTriangleCore e c d) *
          (triSq a d f * triSq c b f)) := by
  have hv := hvalid
  unfold valid6 at hv
  simp only [Bool.and_eq_true] at hv
  rcases hv with ⟨⟨⟨_hvab, hvadf⟩, hvcbf⟩, _hvcde⟩
  have hbcf : fusionOK b c f = true := by
    rw [fusionOK_symm_ab b c f]
    exact hvcbf
  have hafd : fusionOK a f d = true := by
    rw [fusionOK_symm_bt a f d]
    exact hvadf
  let D := Q'.ofNat (f + 1)
  let K := Q'.ofNat (fact (leftInnerOrder a b e)) *
    Q'.ofNat (fact (leftOuterOrder e c d))
  let G1 := closedBinaryGram b c f
  let G2 := closedBinaryGram a f d
  let R1 := channelResidual b c f
  let R2 := channelResidual a f d
  let B1 := binaryBaseFactor b c f
  let B2 := binaryBaseFactor a f d
  let T1 := triSq b c f
  let T2 := triSq a f d
  let R := signedInverseFactor a b c d e f
  have hR : R ≈ (D * K) * (R1 * R2) := by
    simpa only [R, D, K, R1, R2] using
      signedInverseFactor_residual_factorization a b c d e f
  have h1 : G1 * (R1 * R1) ≈ B1 * T1 := by
    simpa only [G1, R1, B1, T1] using
      closedBinaryGram_mul_residual_square b c f hbcf
  have h2 : G2 * (R2 * R2) ≈ B2 * T2 := by
    simpa only [G2, R2, B2, T2] using
      closedBinaryGram_mul_residual_square a f d hafd
  have hK : (K * K) * (B1 * B2) ≈
      gramTriangleCore a b e * gramTriangleCore e c d := by
    simpa only [K, B1, B2] using binaryBaseFactor_recombine a b c d e f
  change (G1 * G2) * (R * R) ≈
    (D * D) * ((gramTriangleCore a b e * gramTriangleCore e c d) *
      (triSq a d f * triSq c b f))
  refine Q'.eqv_trans _
    ((G1 * G2) * (((D * K) * (R1 * R2)) * ((D * K) * (R1 * R2)))) _
    (Q'.mul_eqv_congr_left (G1 * G2) _ _ (square_eqv_congr hR)) ?_
  refine Q'.eqv_trans _
    ((D * D) * ((K * K) * ((G1 * (R1 * R1)) * (G2 * (R2 * R2))))) _
    (residual_square_reorder G1 G2 D K R1 R2) ?_
  refine Q'.eqv_trans _
    ((D * D) * ((K * K) * ((B1 * T1) * (B2 * T2)))) _
    (Q'.mul_eqv_congr_left (D * D) _ _
      (Q'.mul_eqv_congr_left (K * K) _ _
        (Q'.eqv_trans _ (B1 * T1 * (G2 * (R2 * R2))) _
          (Q'.mul_eqv_congr_right _ _ _ h1)
          (Q'.mul_eqv_congr_left (B1 * T1) _ _ h2)))) ?_
  refine Q'.eqv_trans _
    ((D * D) * (((K * K) * (B1 * B2)) * (T2 * T1))) _
    (residual_core_reorder D K B1 B2 T1 T2) ?_
  have htri2 : T2 = triSq a d f := by
    dsimp only [T2]
    exact triSq_swap_last a f d
  have htri1 : T1 = triSq c b f := by
    dsimp only [T1]
    exact triSq_swap_first b c f
  rw [htri2, htri1]
  exact Q'.mul_eqv_congr_left (D * D) _ _
    (Q'.mul_eqv_congr_right _ _ _ hK)

private theorem paired_channel_reorder
    (D G1 G2 T1 T2 U1 U2 : Q') :
    D * ((G1 * G2) * (T1 * U1 * U2 * T2)) ≈
      D * (((G1 * T1) * (G2 * T2)) * (U1 * U2)) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The factorial prefactor of the signed inverse Racah candidate has exactly
the square normalization forced by the four triangle faces and the two
binary-channel Gram products. -/
theorem signedInverseFactor_gram_square_normalization
    (a b c d e f : Nat) (hvalid : valid6 a b c d e f = true) :
    (closedBinaryGram b c f * closedBinaryGram a f d) *
        (signedInverseFactor a b c d e f *
          signedInverseFactor a b c d e f) ≈
      (Q'.ofNat (f + 1) * Q'.ofNat (f + 1)) *
        ((closedBinaryGram a b e * closedBinaryGram e c d) *
          (triSq a b e * triSq a d f * triSq c b f * triSq c d e)) := by
  have hv := hvalid
  unfold valid6 at hv
  simp only [Bool.and_eq_true] at hv
  rcases hv with ⟨⟨⟨hvab, _hvadf⟩, _hvcbf⟩, hvcde⟩
  have hecd : fusionOK e c d = true := by
    rw [fusionOK_symm_ab e c d, fusionOK_symm_bt c e d]
    exact hvcde
  refine Q'.eqv_trans _
    ((Q'.ofNat (f + 1) * Q'.ofNat (f + 1)) *
      ((gramTriangleCore a b e * gramTriangleCore e c d) *
        (triSq a d f * triSq c b f))) _
    (signedInverseFactor_core_square_normalization a b c d e f hvalid) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (f + 1) * Q'.ofNat (f + 1)) *
      (((closedBinaryGram a b e * triSq a b e) *
        (closedBinaryGram e c d * triSq c d e)) *
        (triSq a d f * triSq c b f))) _ ?_ ?_
  · have hAB := closedBinaryGram_mul_triSq a b e hvab
    have hEC := closedBinaryGram_mul_triSq_cyclic e c d hecd
    have hPair :
        (closedBinaryGram a b e * triSq a b e) *
            (closedBinaryGram e c d * triSq c d e) ≈
          gramTriangleCore a b e * gramTriangleCore e c d := by
      refine Q'.eqv_trans _
        (gramTriangleCore a b e *
          (closedBinaryGram e c d * triSq c d e)) _
        (Q'.mul_eqv_congr_right _ _ _ hAB) ?_
      exact Q'.mul_eqv_congr_left _ _ _ hEC
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hPair))
  · exact Q'.eqv_symm
      (paired_channel_reorder
        (Q'.ofNat (f + 1) * Q'.ofNat (f + 1))
        (closedBinaryGram a b e) (closedBinaryGram e c d)
        (triSq a b e) (triSq c d e) (triSq a d f) (triSq c b f))

private theorem reassociate_scaled_product (a b c d : Q') :
    a * (b * (c * d)) ≈ a * ((b * c) * d) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem dimension_factor_reorder
    (de df GL T S2 : Q') :
    de * (((df * df) * (GL * T)) * S2) ≈
      df * (GL * (((de * df) * T) * S2)) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- **Signed-square to faithful-kernel bridge.**  On every physical
tetrahedron, the signed candidate square and `racahKernel6` differ by exactly
the two channel Gram products and the forced output-dimension factors:

`(e+1) G_right candidate² = (f+1) G_left kernel`.

This is division-free, uniform in all six labels, and fixes the precise
normalization that a later Casimir-recursion identification must satisfy. -/
theorem signedCandidate_square_gram_kernel_normalization
    (a b c d e f : Nat) (hvalid : valid6 a b c d e f = true) :
    Q'.ofNat (e + 1) *
        ((closedBinaryGram b c f * closedBinaryGram a f d) *
          (signedRacahInverseCandidate a b c d e f *
            signedRacahInverseCandidate a b c d e f)) ≈
      Q'.ofNat (f + 1) *
        ((closedBinaryGram a b e * closedBinaryGram e c d) *
          racahKernel6 a b c d e f) := by
  let de := Q'.ofNat (e + 1)
  let df := Q'.ofNat (f + 1)
  let GR := closedBinaryGram b c f * closedBinaryGram a f d
  let GL := closedBinaryGram a b e * closedBinaryGram e c d
  let R2 := signedInverseFactor a b c d e f *
    signedInverseFactor a b c d e f
  let S2 := racahSum a b e c d f * racahSum a b e c d f
  let T := triSq a b e * triSq a d f * triSq c b f * triSq c d e
  let C2 := signedRacahInverseCandidate a b c d e f *
    signedRacahInverseCandidate a b c d e f
  let P := racahKernel6 a b c d e f
  have hC : C2 ≈ R2 * S2 := by
    simpa only [C2, R2, S2] using
      signedRacahInverseCandidate_square_of_valid a b c d e f hvalid
  have hF : GR * R2 ≈ (df * df) * (GL * T) := by
    simpa only [GR, R2, df, GL, T] using
      signedInverseFactor_gram_square_normalization a b c d e f hvalid
  have hP : P ≈ ((de * df) * T) * S2 := by
    unfold P racahKernel6
    rw [if_pos hvalid]
    dsimp only [de, df, T, S2, dimRep]
    exact Q'.eqv_refl _
  change de * (GR * C2) ≈ df * (GL * P)
  refine Q'.eqv_trans _ (de * (GR * (R2 * S2))) _
    (Q'.mul_eqv_congr_left de _ _
      (Q'.mul_eqv_congr_left GR _ _ hC)) ?_
  refine Q'.eqv_trans _ (de * ((GR * R2) * S2)) _
    (reassociate_scaled_product de GR R2 S2) ?_
  refine Q'.eqv_trans _ (de * (((df * df) * (GL * T)) * S2)) _
    (Q'.mul_eqv_congr_left de _ _
      (Q'.mul_eqv_congr_right _ _ S2 hF)) ?_
  refine Q'.eqv_trans _ (df * (GL * (((de * df) * T) * S2))) _
    (dimension_factor_reorder de df GL T S2) ?_
  exact Q'.mul_eqv_congr_left df _ _
    (Q'.mul_eqv_congr_left GL _ _ (Q'.eqv_symm hP))

end YMGap.Continuum.SU2SignedRacahSquareNormalization

#print axioms YMGap.Continuum.SU2SignedRacahSquareNormalization.closedBinaryGramDen_pos
#print axioms YMGap.Continuum.SU2SignedRacahSquareNormalization.closedBinaryGram_mul_triSq
#print axioms YMGap.Continuum.SU2SignedRacahSquareNormalization.signedInverseFactor_gram_square_normalization
#print axioms YMGap.Continuum.SU2SignedRacahSquareNormalization.signedCandidate_square_gram_kernel_normalization
