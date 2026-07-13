/-
Exact integer / half-integer theta representation of the retained harmonic
correlation quotient.

With `n=a+1` and `q=w^2`, multiplying the diagonal and adjacent sums by their
vacuum powers gives

  w^2 D_N = sum_{1<=n<=N+1} n^2 q^{n^2},
  w   A_N = sum_{1<=n<=N}   n(n+1) q^{n(n+1)}.

The second exponent is `(n+1/2)^2-1/4`, i.e. the half-integer theta sector.
-/

import YMGap.Continuum.HarmonicThetaRatioExtension
import YMGap.Continuum.RDThetaCentered

namespace YMGap.Continuum.HarmonicThetaRepresentation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicThetaRatioExtension
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

local macro "ring_mul_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             ac_rfl))

/-- Integer-theta derivative summand `n² (w²)^{n²}`. -/
def integerThetaTerm (w : Q') (n : Nat) : Q' :=
  Q'.ofNat (n * n) * qpow (w * w) (n * n)

/-- Half-integer-theta derivative summand
`n(n+1) (w²)^{n(n+1)}`. -/
def halfThetaTerm (w : Q') (n : Nat) : Q' :=
  Q'.ofNat (n * (n + 1)) * qpow (w * w) (n * (n + 1))

def integerThetaSum (w : Q') (N : Nat) : Q' :=
  finSum (fun j => integerThetaTerm w (j + 1)) (N + 1)

def halfThetaSum (w : Q') (N : Nat) : Q' :=
  finSum (fun j => halfThetaTerm w (j + 1)) N

private theorem qpow_sqbase_eq_double (w : Q') (n : Nat) :
    qpow (w * w) n ≈ qpow w (n + n) := by
  exact Q'.eqv_trans _ _ _ (qpow_mul_self w n)
    (Q'.eqv_symm (qpow_add w n n))

private theorem ofNat_sq_eqv (n : Nat) :
    Q'.ofNat n * Q'.ofNat n ≈ Q'.ofNat (n * n) := by
  exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv n n)

private theorem ofNat_adj_eqv (n : Nat) :
    Q'.ofNat n * Q'.ofNat (n + 1) ≈ Q'.ofNat (n * (n + 1)) := by
  exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv n (n + 1))

/-- Per-mode integer-sector identity. -/
theorem diagonal_term_theta_eqv (w : Q') (a : Nat) :
    qpow w 2 * (coeffW w a * coeffW w a) ≈
      integerThetaTerm w (a + 1) := by
  let q := w * w
  have hsquare := coeffW_sq_eqv w a
  have hq2 : qpow w 2 ≈ q := by
    change ((1 : Q') * w) * w ≈ w * w
    exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)
  have hpow : qpow q (c4 a) * q ≈ qpow q (c4 a + 1) := by
    have hq1 : qpow q 1 ≈ q := by
      change (1 : Q') * q ≈ q
      exact Q'.one_mul_eqv q
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow q (c4 a)) _ _ (Q'.eqv_symm hq1))
      (Q'.eqv_symm (qpow_add q (c4 a) 1))
  have hexp : c4 a + 1 = (a + 1) * (a + 1) := by
    unfold c4
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  unfold integerThetaTerm
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hq2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q _ _ hsquare) ?_
  unfold dimQ q
  -- Reorder `q·n·n·q^c` into `(n·n)·(q^c·q)`.
  have hreorder :
      q * (Q'.ofNat (a + 1) *
          (Q'.ofNat (a + 1) * qpow (w * w) (c4 a))) ≈
        (Q'.ofNat (a + 1) * Q'.ofNat (a + 1)) *
          (qpow (w * w) (c4 a) * q) := by
    ring_mul_qeqv
  refine Q'.eqv_trans _ _ _ hreorder ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_sq_eqv (a + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat ((a + 1) * (a + 1))) _ _ hpow) ?_
  rw [hexp]
  exact Q'.eqv_refl _

/-- Per-edge half-integer-sector identity. -/
theorem adjacent_term_theta_eqv (w : Q') (a : Nat) :
    w * (coeffW w a * coeffW w (a + 1)) ≈
      halfThetaTerm w (a + 1) := by
  let n := a + 1
  have hexp : 1 + (c4 a + c4 (a + 1)) =
      (n * (n + 1)) + (n * (n + 1)) := by
    unfold c4 n
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  unfold coeffW halfThetaTerm dimQ
  have hp : w * (qpow w (c4 a) * qpow w (c4 (a + 1))) ≈
      qpow w (1 + (c4 a + c4 (a + 1))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _
        (Q'.eqv_symm (qpow_add w (c4 a) (c4 (a + 1))))) ?_
    have hw1 : w ≈ qpow w 1 := by
      change w ≈ (1 : Q') * w
      exact Q'.eqv_symm (Q'.one_mul_eqv w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hw1) ?_
    exact Q'.eqv_symm (qpow_add w 1 (c4 a + c4 (a + 1)))
  have hreorder :
      w * ((Q'.ofNat n * qpow w (c4 a)) *
        (Q'.ofNat (n + 1) * qpow w (c4 (a + 1)))) ≈
      (Q'.ofNat n * Q'.ofNat (n + 1)) *
        (w * (qpow w (c4 a) * qpow w (c4 (a + 1)))) := by
    ring_mul_qeqv
  refine Q'.eqv_trans _ _ _ hreorder ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_adj_eqv n)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n * (n + 1))) _ _ hp) ?_
  rw [hexp]
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (qpow_sqbase_eq_double w (n * (n + 1))))

/-- Exact finite integer-theta representation of the diagonal norm. -/
theorem coordNormSq_theta_eqv (w : Q') (N : Nat) :
    qpow w 2 * coordNormSq w N ≈ integerThetaSum w N := by
  unfold coordNormSq integerThetaSum
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_const_mul (qpow w 2)
      (fun a => coeffW w a * coeffW w a) (N + 1)) ?_
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_eqv_congr _ _ (diagonal_term_theta_eqv w) (N + 1)) ?_
  exact Q'.eqv_of_eq (MovingCutoff.fsum_eq_finSum _ (N + 1))

/-- Exact finite half-integer-theta representation of the adjacent numerator. -/
theorem adjCorr_theta_eqv (w : Q') (N : Nat) :
    w * adjCorr w N ≈ halfThetaSum w N := by
  unfold adjCorr halfThetaSum
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_const_mul w
      (fun a => coeffW w a * coeffW w (a + 1)) N) ?_
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_eqv_congr _ _ (adjacent_term_theta_eqv w) N) ?_
  exact Q'.eqv_of_eq (MovingCutoff.fsum_eq_finSum _ N)

/-- A theta-sector comparison implies the original finite Rayleigh comparison.
This is the exact constructive target for a Jacobi product/modular argument. -/
theorem theta_comparison_implies_retune {w : Q'}
    (hw0 : (0 : Q') < w) (N : Nat)
    (htheta :
      w * halfThetaSum w N ≤ retuneCube w * integerThetaSum w N) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hww : (0 : Q') < qpow w 2 := qpow_pos hw0 2
  have hL : qpow w 2 * adjCorr w N ≈ w * halfThetaSum w N := by
    have hq2 : qpow w 2 ≈ w * w := by
      change ((1 : Q') * w) * w ≈ w * w
      exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (adjCorr w N) hq2) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv w w (adjCorr w N)) ?_
    exact Q'.mul_eqv_congr_left w _ _ (adjCorr_theta_eqv w N)
  have hR : qpow w 2 * (retuneCube w * coordNormSq w N) ≈
      retuneCube w * integerThetaSum w N := by
    have hreorder : qpow w 2 * (retuneCube w * coordNormSq w N) ≈
        retuneCube w * (qpow w 2 * coordNormSq w N) := by
      ring_mul_qeqv
    exact Q'.eqv_trans _ _ _ hreorder
      (Q'.mul_eqv_congr_left (retuneCube w) _ _
        (coordNormSq_theta_eqv w N))
  have hscaled : qpow w 2 * adjCorr w N ≤
      qpow w 2 * (retuneCube w * coordNormSq w N) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ htheta (Q'.ge_of_eqv hR))
  exact Q'.le_of_mul_le_mul_left hscaled hww

/-! ## Explicit finite-cutoff errors in the two theta sectors -/

private theorem adjTailWindow_nonneg (k M : Nat) :
    (0 : Q') ≤ adjTailWindow k M := by
  unfold adjTailWindow
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ m ih =>
      exact Q'.zero_le_add _ _ ih
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg k) _)
          (coeffW_nonneg (harmW_nonneg k) _))

/-- The half-integer theta numerator has the explicit inherited cutoff error
`4/(k+2)^2`. -/
theorem halfTheta_cutoff_extension_le (k M : Nat) :
    halfThetaSum (harmW k) (Ncut k + M) ≤
      halfThetaSum (harmW k) (Ncut k) +
        Q'.ofNat 4 * invSqTerm 2 (by decide) k := by
  let w := harmW k
  let S := Ncut k
  let T := adjTailWindow k M
  have hsplit := adjCorr_cutoff_split_eqv k M
  have hT0 : (0 : Q') ≤ T := adjTailWindow_nonneg k M
  have hwT : w * T ≤ T := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ T (harmW_le_one k) hT0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv T))
  have htail : w * T ≤ Q'.ofNat 4 * invSqTerm 2 (by decide) k :=
    Q'.le_trans' _ _ _ hwT (adjTailWindow_le_four_invSq k M)
  have hre : halfThetaSum w (S + M) ≈ halfThetaSum w S + w * T := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (adjCorr_theta_eqv w (S + M))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ hsplit) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv w (adjCorr w S) T) ?_
    exact Q'.add_eqv_congr_right _ _ (w * T) (adjCorr_theta_eqv w S)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
    (Q'.add_le_add_left _ _ _ htail)

/-- Diagonal square increment beyond the retained cutoff. -/
def diagTailWindow (k M : Nat) : Q' :=
  finSum (fun j => coeffSqTerm k (Ncut k + j + 1)) M

theorem diagTailWindow_le_two_invSq (k M : Nat) :
    diagTailWindow k M ≤ Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  let f := fun j => coeffSqTerm k (Ncut k + j)
  have hnonneg : ∀ j, (0 : Q') ≤ f j := by
    intro j
    unfold f coeffSqTerm
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) _) (coeffW_nonneg (harmW_nonneg k) _)
  have hsplit := YMGap.Constructive.finSum_split f 1 M
  have hhead : (0 : Q') ≤ finSum f 1 := by
    show (0 : Q') ≤ (0 : Q') + f 0
    exact Q'.zero_le_add _ _ (Q'.le_refl' 0) (hnonneg 0)
  have hshift : finSum (fun j => f (1 + j)) M ≤ finSum f (1 + M) := by
    have h1 := Q'.add_le_self_of_nonneg
      (finSum (fun j => f (1 + j)) M) (finSum f 1) hhead
    exact Q'.le_trans' _ _ _ h1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
        (Q'.ge_of_eqv hsplit))
  have hre : diagTailWindow k M ≈ finSum (fun j => f (1 + j)) M := by
    unfold diagTailWindow
    exact finSum_eqv_congr _ _ (fun j => by
      unfold f
      rw [show Ncut k + j + 1 = Ncut k + (1 + j) by omega]
      exact Q'.eqv_refl _) M
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
    (Q'.le_trans' _ _ _ hshift
      (bulkThetaWindow_le_two_mul_invSq k (1 + M)))

private theorem coordNormSq_cutoff_split_eqv (k M : Nat) :
    coordNormSq (harmW k) (Ncut k + M) ≈
      coordNormSq (harmW k) (Ncut k) + diagTailWindow k M := by
  unfold coordNormSq diagTailWindow
  rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
  rw [show Ncut k + M + 1 = (Ncut k + 1) + M by omega]
  have hs := YMGap.Constructive.finSum_split
    (fun a => coeffW (harmW k) a * coeffW (harmW k) a) (Ncut k + 1) M
  refine Q'.eqv_trans _ _ _ hs ?_
  exact Q'.add_eqv_congr_left _ _ _
    (finSum_eqv_congr _ _ (fun j => by
      rw [show Ncut k + 1 + j = Ncut k + j + 1 by omega]
      exact Q'.eqv_refl _) M)

/-- The integer theta denominator has cutoff error `2/(k+2)^2`. -/
theorem integerTheta_cutoff_extension_le (k M : Nat) :
    integerThetaSum (harmW k) (Ncut k + M) ≤
      integerThetaSum (harmW k) (Ncut k) +
        Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  let w := harmW k
  let S := Ncut k
  let T := diagTailWindow k M
  let q := qpow w 2
  have hT0 : (0 : Q') ≤ T := by
    unfold T diagTailWindow
    induction M with
    | zero => exact Q'.le_refl' 0
    | succ m ih =>
        exact Q'.zero_le_add _ _ ih
          (Q'.mul_nonneg _ _
            (coeffW_nonneg (harmW_nonneg k) _)
            (coeffW_nonneg (harmW_nonneg k) _))
  have hsplit := coordNormSq_cutoff_split_eqv k M
  have hq1 : q ≤ (1 : Q') := by
    unfold q
    exact HeatKernelGap.qpow_le_one (harmW_nonneg k) (harmW_le_one k) 2
  have hqT : q * T ≤ T := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ T hq1 hT0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv T))
  have htail : q * T ≤ Q'.ofNat 2 * invSqTerm 2 (by decide) k :=
    Q'.le_trans' _ _ _ hqT (diagTailWindow_le_two_invSq k M)
  have hre : integerThetaSum w (S + M) ≈ integerThetaSum w S + q * T := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (coordNormSq_theta_eqv w (S + M))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q _ _ hsplit) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv q (coordNormSq w S) T) ?_
    exact Q'.add_eqv_congr_right _ _ (q * T) (coordNormSq_theta_eqv w S)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
    (Q'.add_le_add_left _ _ _ htail)

end YMGap.Continuum.HarmonicThetaRepresentation

#print axioms YMGap.Continuum.HarmonicThetaRepresentation.diagonal_term_theta_eqv
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.adjacent_term_theta_eqv
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.coordNormSq_theta_eqv
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.adjCorr_theta_eqv
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.theta_comparison_implies_retune
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.halfTheta_cutoff_extension_le
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.diagTailWindow_le_two_invSq
#print axioms YMGap.Continuum.HarmonicThetaRepresentation.integerTheta_cutoff_extension_le
