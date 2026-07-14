/-
Sharp geometric envelope inside the first lower-six square-root block.

The seven-block contraction controls the infinite tail but is deliberately
coarse within its first block.  Here the exact adjacent-mode exponent gives a
constant-ratio geometric majorant.  Reciprocal Bernoulli supplies a derived,
division-free bound on the complete block.
-/

import YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope

namespace YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem block_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "block_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               block_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pOneSubSquareL : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .add (.const 1) (.neg (.mul w w))

private def pOneSubSquareR : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .mul u (.add (.const 1) w)

private theorem pOneSubSquare_normal :
    RingNormaliser.normalize pOneSubSquareL =
      RingNormaliser.normalize pOneSubSquareR := by decide

private theorem oneSubSquare_algebra (u : Q') :
    (1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u)) ≈
      u * ((1 : Q') + ((1 : Q') + -u)) := by
  simpa [pOneSubSquareL, pOneSubSquareR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pOneSubSquareL pOneSubSquareR pOneSubSquare_normal (fun _ => u))

private theorem one_sub_harmW_square_eqv (k : Nat) :
    (1 : Q') + -(harmW k * harmW k) ≈
      harmU k * ((1 : Q') + harmW k) := by
  unfold harmW oneSub
  exact oneSubSquare_algebra _

/-- Constant adjacent-mode ratio used inside the first square-root block. -/
def lowerSixWithinBlockRate (k : Nat) : Q' :=
  let σ := harmW k * harmW k
  let K := thetaWindowLeft k + 1
  qpow σ (2 * K + 1)

private theorem ten_center_le_harmonicDen
    {k : Nat} (hk : 247 ≤ k) :
    10 * thetaWindowCenter k ≤ k + 2 := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h20c : 20 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 20 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  rcases Nat.le_total (10 * c) D with h | h
  · change 10 * c ≤ D
    exact h
  · rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hupper : 2 * D + 1 < 20 * c := by omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · change 10 * c ≤ D
      omega

private theorem eight_withinBlockExponent_le_harmonicDen
    {k : Nat} (hk : 247 ≤ k) :
    8 * (2 * (thetaWindowLeft k + 1) + 1) ≤ k + 2 := by
  let c := thetaWindowCenter k
  let d := thetaWindowLeft k
  let D := k + 2
  have hc := ten_center_le_harmonicDen hk
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hd : 2 * d ≤ c := by
    dsimp only [d]
    unfold thetaWindowLeft
    omega
  dsimp only [c, d, D] at hc hc22 hd ⊢
  omega

private theorem lowerSixWithinBlockLinearSmall
    {k : Nat} (hk : 247 ≤ k) :
    Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
        ((1 : Q') + -(harmW k * harmW k)) ≤ oneFourth := by
  let D := k + 2
  let m := 2 * (thetaWindowLeft k + 1) + 1
  have hDpos : 0 < D := by
    dsimp only [D]
    omega
  have hDDpos : 0 < D * D := Nat.mul_pos hDpos hDpos
  have hm : 8 * m ≤ D := by
    dsimp only [m, D]
    exact eight_withinBlockExponent_le_harmonicDen hk
  have hnat : 4 * m * (2 * D - 1) ≤ D * D := by
    have htwo : 2 * D - 1 ≤ 2 * D := by omega
    calc
      4 * m * (2 * D - 1) ≤ 4 * m * (2 * D) :=
        Nat.mul_le_mul_left (4 * m) htwo
      _ = (8 * m) * D := by
        calc
          4 * m * (2 * D) = (4 * 2) * (m * D) := by ac_rfl
          _ = 8 * (m * D) := by rw [show 4 * 2 = 8 by decide]
          _ = (8 * m) * D := by rw [Nat.mul_assoc]
      _ ≤ D * D := Nat.mul_le_mul_right D hm
  let u := (1 : Q') + -(harmW k * harmW k)
  let v := Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos
  have huv : u ≈ v := by
    refine Q'.eqv_trans _ (harmU k * ((1 : Q') + harmW k)) _ ?_ ?_
    · dsimp only [u]
      exact one_sub_harmW_square_eqv k
    · dsimp only [v, D]
      unfold harmW harmU oneSub unit
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
        Q'.mul_den_cast, Q'.neg_den, block_neg_num_cast,
        Q'.mkPos_num, Q'.mkPos_den,
        show (1 : Q').num = 1 from rfl,
        show ((1 : Q').den : Int) = 1 from rfl,
        Int.one_mul, Int.mul_one]
      push_cast [Int.natCast_sub (by omega : 1 ≤ 2 * (k + 2))]
      congr 1 <;> omega
  have hbound : Q'.ofNat m * v ≤ oneFourth := by
    unfold oneFourth
    dsimp only [v]
    show
      (Q'.ofNat m *
        Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos).num *
          ((Q'.mkPos 1 4 (by decide)).den : Int) ≤
        (Q'.mkPos 1 4 (by decide)).num *
          (Q'.ofNat m *
            Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos).den
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
    have hnat' : m * (2 * D - 1) * 4 ≤ D * D := by
      exact Nat.le_trans (Nat.le_of_eq (by ac_rfl)) hnat
    exact_mod_cast hnat'
  dsimp only [m, u] at huv ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ huv)) hbound

/-- Quantitative decrement of the first-block constant ratio. -/
theorem lowerSixWithinBlockRate_decrement
    {k : Nat} (hk : 247 ≤ k) :
    fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k))) ≤
      (1 : Q') + -lowerSixWithinBlockRate k := by
  have hσ0 : (0 : Q') ≤ harmW k * harmW k :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : harmW k * harmW k ≤ (1 : Q') := by
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  unfold lowerSixWithinBlockRate
  exact qpow_decrement_ge_fourFifths_linear hσ0 hσ1 _
    (lowerSixWithinBlockLinearSmall hk)

/-- Cleared geometric cofactor bound for the first square-root block. -/
theorem lowerSixWithinBlockRate_geomSum_cleared
    {k : Nat} (hk : 247 ≤ k) :
    (fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k)))) *
        HeatKernelRGStep.geomSum (lowerSixWithinBlockRate k)
          (thetaWindowCenter k) ≤ (1 : Q') := by
  let r := lowerSixWithinBlockRate k
  let a := fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let c := thetaWindowCenter k
  have hr0 : (0 : Q') ≤ r := by
    dsimp only [r, lowerSixWithinBlockRate]
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hgeom0 : (0 : Q') ≤ HeatKernelRGStep.geomSum r c :=
    HeatKernelRGStep.geomSum_nonneg hr0 c
  have hdec : a ≤ (1 : Q') + -r := by
    dsimp only [a, r]
    exact lowerSixWithinBlockRate_decrement hk
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _
    (HeatKernelRGStep.geomSum r c) hdec hgeom0
  have hfactor : ((1 : Q') + -r) * HeatKernelRGStep.geomSum r c ≈
      (1 : Q') + -(qpow r c) := by
    change ((1 : Q') - r) * HeatKernelRGStep.geomSum r c ≈
      (1 : Q') - qpow r c
    exact Q'.eqv_symm (HeatKernelRGStep.oneSub_pow_factor r c)
  have hpow0 : (0 : Q') ≤ qpow r c := qpow_nonneg _ hr0 _
  have hone : (1 : Q') + -(qpow r c) ≤ (1 : Q') := by
    have hneg := Q'.nonpos_neg_of_nonneg hpow0
    have hadd := Q'.add_le_add_left (1 : Q') _ _ hneg
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv 1))
  dsimp only [a, r, c] at hmul ⊢
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hone)

private theorem nat_le_self_mul_self : ∀ n : Nat, n ≤ n * n
  | 0 => by omega
  | n + 1 => by
      have h := Nat.mul_le_mul_left (n + 1)
        (show 1 ≤ n + 1 by omega)
      simpa only [Nat.mul_one] using h

/-- Pointwise constant-ratio majorant inside the first block. -/
theorem lowerSixModeWeight_firstBlock_le_geometric (k s : Nat) :
    lowerSixModeWeight k (thetaWindowLeft k + 1 + s) ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) *
        qpow (lowerSixWithinBlockRate k) s := by
  let σ := harmW k * harmW k
  let K := thetaWindowLeft k + 1
  let m := 2 * K + 1
  let δ := 2 * K * s + s * s
  have hsq : s ≤ s * s := nat_le_self_mul_self s
  have hδ : s * m ≤ δ := by
    dsimp only [m, δ]
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm s (2 * K)]
    exact Nat.add_le_add_left hsq (2 * K * s)
  have hexp : (K + s) * (K + s) = K * K + δ := by
    dsimp only [δ]
    simp only [Nat.add_mul, Nat.mul_add]
    rw [show s * K = K * s from Nat.mul_comm s K]
    rw [show 2 * K = K + K by omega, Nat.add_mul]
    rw [Nat.add_mul K K s]
    ac_rfl
  have hsplit : lowerSixModeWeight k (K + s) ≈
      lowerSixModeWeight k K * qpow σ δ := by
    unfold lowerSixModeWeight
    dsimp only [σ]
    rw [hexp]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hσ0 : (0 : Q') ≤ σ := by
    dsimp only [σ]
    exact Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : σ ≤ (1 : Q') := by
    dsimp only [σ]
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hpow0 := HeatKernelRGStep.qpow_antitone hσ0 hσ1
    (s * m) δ hδ
  have hiter : qpow σ (s * m) ≈
      qpow (lowerSixWithinBlockRate k) s := by
    unfold lowerSixWithinBlockRate
    dsimp only [σ, K, m]
    rw [Nat.mul_comm s (2 * (thetaWindowLeft k + 1) + 1)]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow _ _ _)
  have hpow : qpow σ δ ≤ qpow (lowerSixWithinBlockRate k) s :=
    Q'.le_trans' _ _ _ hpow0 (Q'.le_of_eqv hiter)
  have hW0 : (0 : Q') ≤ lowerSixModeWeight k K := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _ hσ0 _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (lowerSixModeWeight k K) hpow hW0
  dsimp only [K] at hsplit hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hmul

private theorem finSum_qpow_eqv_geomSum (r : Q') : ∀ N,
    finSum (fun s => qpow r s) N ≈ HeatKernelRGStep.geomSum r N
  | 0 => Q'.eqv_refl _
  | N + 1 => by
      rw [finSum_succ, HeatKernelRGStep.geomSum_succ]
      exact Q'.add_eqv_congr_right _ _ _ (finSum_qpow_eqv_geomSum r N)

theorem lowerSixGaussianFirstBlock_le_geometric (k : Nat) :
    lowerSixGaussianTailBlock k 0 ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) *
        HeatKernelRGStep.geomSum (lowerSixWithinBlockRate k)
          (thetaWindowCenter k) := by
  let W := lowerSixModeWeight k (thetaWindowLeft k + 1)
  let r := lowerSixWithinBlockRate k
  let c := thetaWindowCenter k
  let f := fun s => lowerSixModeWeight k (thetaWindowLeft k + 1 + s)
  let g := fun s => W * qpow r s
  have hterm : ∀ s, s < c → f s ≤ g s := by
    intro s _
    dsimp only [f, g, W, r]
    exact lowerSixModeWeight_firstBlock_le_geometric k s
  have hsum := YMGap.Constructive.finSum_le_lt f g c hterm
  have hclosed : finSum g c ≈ W * HeatKernelRGStep.geomSum r c := by
    refine Q'.eqv_trans _ (W * finSum (fun s => qpow r s) c) _ ?_ ?_
    · exact Q'.eqv_symm
        (RationalTail.const_mul_finSum (fun s => qpow r s) W c)
    · exact Q'.mul_eqv_congr_left _ _ _
        (finSum_qpow_eqv_geomSum r c)
  unfold lowerSixGaussianTailBlock
  dsimp only [f, g, W, r, c] at hsum hclosed ⊢
  simpa only [Nat.zero_mul, Nat.add_zero] using
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hclosed))

/-- Division-free sharp bound for the production first Gaussian block. -/
theorem lowerSixGaussianFirstBlock_cleared
    {k : Nat} (hk : 247 ≤ k) :
    (fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k)))) *
        lowerSixGaussianTailBlock k 0 ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) := by
  let a := fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let W := lowerSixModeWeight k (thetaWindowLeft k + 1)
  let S := HeatKernelRGStep.geomSum (lowerSixWithinBlockRate k)
    (thetaWindowCenter k)
  have hu0 : (0 : Q') ≤ (1 : Q') + -(harmW k * harmW k) := by
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    have hσ1 := Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    exact Q'.sub_nonneg_of_le hσ1
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact Q'.mul_nonneg _ _ (by
      unfold fourFifths
      decide) (Q'.mul_nonneg _ _
        (HeatKernelRGStep.zero_le_ofNat _) hu0)
  have hblock := lowerSixGaussianFirstBlock_le_geometric k
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ a hblock ha0
  have hAS : a * S ≤ (1 : Q') := by
    dsimp only [a, S]
    exact lowerSixWithinBlockRate_geomSum_cleared hk
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hWAS := Q'.mul_le_mul_of_nonneg_left _ _ W hAS hW0
  have hreassoc : a * (W * S) ≈ W * (a * S) := by ring_qeqv
  dsimp only [a, W, S] at hscaled hWAS hreassoc ⊢
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc)
      (Q'.le_trans' _ _ _ hWAS (Q'.le_of_eqv (Q'.mul_one_eqv _))))

#print axioms lowerSixWithinBlockRate_decrement
#print axioms lowerSixWithinBlockRate_geomSum_cleared
#print axioms lowerSixModeWeight_firstBlock_le_geometric
#print axioms lowerSixGaussianFirstBlock_le_geometric
#print axioms lowerSixGaussianFirstBlock_cleared

end YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric
