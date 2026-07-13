/-
# A two-anchor block plus PF2 tail correlation bound

For `c_a=(a+1)w^{a(a+2)}`, isolate the vacuum edge `c_0c_1` and control
every later adjacent product by the first excited ratio

    q_1 = c_2/c_1 = (3/2)w^5.

PF2 gives `c_a c_{a+1} <= q_1 c_a^2` for `a>=1`.  Summing this finite
tail and retaining the explicit diagonal block `c_0^2+c_1^2=1+4w^6`
reduces the all-cutoff retune estimate to one degree-eleven polynomial.
Its positivity on `0 <= w <= 3/4` is certified below by twelve exact
nonnegative Bernstein coefficients after the rational rescaling `x=4w/3`.
-/

import YMGap.Continuum.CutoffCorrelationMonotone
import YMGap.Continuum.CircleFourierPowerModel
import YMGap.Continuum.AllWindowCorrDirichlet

namespace YMGap.Continuum.TwoAnchorBlockCorrBound

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AllWindowCorrDirichlet

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

def blockCap : Q' := Q'.mkPos 3 4 (by decide)
private def fourThirds : Q' := Q'.mkPos 4 3 (by decide)
private def threeHalves : Q' := Q'.mkPos 3 2 (by decide)

/-- The exact first excited tail ratio `(3/2)w^5`. -/
def tailRatio (w : Q') : Q' := threeHalves * RGTransport.qpow w 5

private def cOneP : Poly := [0, 0, 0, Q'.ofNat 2]
private def ratioP : Poly := [0, 0, 0, 0, 0, threeHalves]
private def retuneP : Poly :=
  [Q'.mkPos 1 8 (by decide), Q'.mkPos 3 8 (by decide),
   Q'.mkPos 3 8 (by decide), Q'.mkPos 1 8 (by decide)]
private def blockP : Poly := [1, 0, 0, 0, 0, 0, Q'.ofNat 4]
private def blockLHS : Poly := padd cOneP (pmul ratioP blockP)
private def blockRHS : Poly := padd (pmul retuneP blockP) ratioP
private def blockSlackP : Poly := psub blockRHS blockLHS
private def ratioSlackP : Poly := psub retuneP ratioP

/-- Scale the variable of a coefficient-list polynomial: coefficients become
`a_i k^i`, so evaluation at `x` is evaluation of the original at `kx`. -/
private def scaleVar (k : Q') : Poly → Poly
  | [] => []
  | a :: p => a :: pscale k (scaleVar k p)

private theorem eval_scaleVar (k x : Q') : ∀ p : Poly,
    eval (scaleVar k p) x ≈ eval p (k * x)
  | [] => Q'.eqv_refl 0
  | a :: p => by
      show (a + x * eval (pscale k (scaleVar k p)) x) ≈
        (a + (k * x) * eval p (k * x))
      refine Q'.add_eqv_congr_left a _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (eval_pscale k (scaleVar k p) x)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _
          (Q'.mul_eqv_congr_left k _ _ (eval_scaleVar k x p))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv x k (eval p (k * x)))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv x k)

private theorem eval_eqv_arg {x y : Q'} (hxy : x ≈ y) : ∀ p : Poly,
    eval p x ≈ eval p y
  | [] => Q'.eqv_refl 0
  | a :: p => by
      show a + x * eval p x ≈ a + y * eval p y
      refine Q'.add_eqv_congr_left a _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (eval p x) hxy) ?_
      exact Q'.mul_eqv_congr_left y _ _ (eval_eqv_arg hxy p)

private theorem mul_eqv_both {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private def blockBernTerms : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 53 32 (by decide)),
   (2, Q'.mkPos 1267 128 (by decide)),
   (3, Q'.mkPos 17607 512 (by decide)),
   (4, Q'.mkPos 4881 64 (by decide)),
   (5, Q'.mkPos 14385 128 (by decide)),
   (6, Q'.mkPos 909273 8192 (by decide)),
   (7, Q'.mkPos 2364693 32768 (by decide)),
   (8, Q'.mkPos 3884691 131072 (by decide)),
   (9, Q'.mkPos 3961447 524288 (by decide)),
   (10, Q'.mkPos 400885 262144 (by decide)),
   (11, Q'.mkPos 104203 2097152 (by decide))]

/-- Exact Bernstein certificate for the degree-eleven block slack. -/
theorem blockSlack_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ blockCap) :
    (0 : Q') ≤ eval blockSlackP w := by
  let x := fourThirds * w
  have hx0 : (0 : Q') ≤ x :=
    Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ fourThirds hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP 11 blockBernTerms) x :=
    eval_bernTermsP_nonneg hx0 hx1 11 blockBernTerms (by decide)
  have hrep : allZero
      (psub (scaleVar blockCap blockSlackP) (bernTermsP 11 blockBernTerms)) := by
    decide
  have hs : (0 : Q') ≤ eval (scaleVar blockCap blockSlackP) x :=
    Q'.le_trans' _ _ _ hb
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  have he : eval (scaleVar blockCap blockSlackP) x ≈ eval blockSlackP w := by
    refine Q'.eqv_trans _ _ _ (eval_scaleVar blockCap x blockSlackP) ?_
    apply eval_eqv_arg
    unfold x blockCap fourThirds
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
    have hk : (Q'.mkPos 3 4 (by decide) * Q'.mkPos 4 3 (by decide)) ≈ (1 : Q') := by
      decide
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ w hk) ?_
    exact Q'.one_mul_eqv w
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he)

private def ratioBernTerms : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)), (1, Q'.mkPos 29 32 (by decide)),
   (2, Q'.mkPos 331 128 (by decide)), (3, Q'.mkPos 1855 512 (by decide)),
   (4, Q'.mkPos 637 256 (by decide)), (5, Q'.mkPos 643 2048 (by decide))]

/-- The tail multiplier is below the retune eigenvalue throughout the block window. -/
theorem tailRatio_le_retune {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ blockCap) :
    tailRatio w ≤ retuneCube w := by
  let x := fourThirds * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ fourThirds hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hrep : allZero
      (psub (scaleVar blockCap ratioSlackP) (bernTermsP 5 ratioBernTerms)) := by decide
  have hs0 : (0 : Q') ≤ eval (scaleVar blockCap ratioSlackP) x :=
    Q'.le_trans' _ _ _ (eval_bernTermsP_nonneg hx0 hx1 5 ratioBernTerms (by decide))
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  have hk : blockCap * fourThirds ≈ (1 : Q') := by decide
  have hs : (0 : Q') ≤ eval ratioSlackP w := by
    refine Q'.le_trans' _ _ _ hs0 (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (eval_scaleVar blockCap x ratioSlackP) ?_
    apply eval_eqv_arg
    unfold x
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w hk) ?_
    exact Q'.one_mul_eqv w
  have hdiff := eval_psub retuneP ratioP w
  have heval : eval ratioP w ≤ eval retuneP w := by
    have hs' : (0 : Q') ≤ eval retuneP w + -eval ratioP w :=
      Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hdiff)
    have h := Q'.add_le_add_right 0 (eval retuneP w + -eval ratioP w)
      (eval ratioP w) hs'
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_zero_add_eqv _))) ?_
    refine Q'.le_trans' _ _ _ h ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)) ?_
    exact q_add_zero_eqv _
  have hq : tailRatio w ≈ eval ratioP w := by
    unfold tailRatio ratioP
    exact Q'.eqv_symm (eval_monoP threeHalves w 5)
  have hr : retuneCube w ≈ eval retuneP w := by
    unfold retuneCube retuneBase
    change RGTransport.qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈ _
    have hpow : RGTransport.qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) := by
      change (((1 : Q') * _) * _) * _ ≈ _
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))
    refine Q'.eqv_trans _ _ _ hpow ?_
    let linP : Poly := [Q'.mkPos 1 2 (by decide), Q'.mkPos 1 2 (by decide)]
    let base : Q' := Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)
    have hlin : base ≈ eval linP w := by
      unfold base linP
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ 1 w) ?_
      refine Q'.eqv_trans _ _ _
        (q_add_congr (Q'.mul_one_eqv _) (Q'.mul_comm_eqv _ _)) ?_
      show _ ≈ Q'.mkPos 1 2 (by decide) + w * (Q'.mkPos 1 2 (by decide) + w * 0)
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.mul_eqv_congr_left w _ _ ?_
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (q_mul_zero w)) (q_add_zero_eqv _))
    have hprod : base * base * base ≈ eval (pmul (pmul linP linP) linP) w := by
      refine Q'.eqv_trans _ _ _ (mul_eqv_both (mul_eqv_both hlin hlin) hlin) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_both (Q'.eqv_symm (eval_pmul linP linP w)) (Q'.eqv_refl _)) ?_
      exact Q'.eqv_symm (eval_pmul (pmul linP linP) linP w)
    refine Q'.eqv_trans _ _ _ hprod ?_
    exact poly_eqv (pmul (pmul linP linP) linP) retuneP w (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hq)
    (Q'.le_trans' _ _ _ heval (Q'.le_of_eqv (Q'.eqv_symm hr)))

/-- Exact identity `c_2 = ((3/2)w^5)c_1`. -/
theorem coeffW_two_eq_tailRatio_mul_one (w : Q') :
    coeffW w 2 ≈ tailRatio w * coeffW w 1 := by
  have hc2 := CircleFourierPowerModel.hcoeff w 2
  have hq : tailRatio w ≈ eval ratioP w := by
    unfold tailRatio ratioP
    exact Q'.eqv_symm (eval_monoP threeHalves w 5)
  have hc1 : coeffW w 1 ≈ eval cOneP w := by
    refine Q'.eqv_trans _ _ _ (CircleFourierPowerModel.hcoeff w 1) ?_
    exact poly_eqv _ _ w (by decide)
  refine Q'.eqv_trans _ _ _ hc2 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv _ (pmul ratioP cOneP) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc1)

/-- PF2 controls every adjacent product after the vacuum edge by `q_1 c_a^2`. -/
theorem adjacent_tail_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwp : (0 : Q') < w) {a : Nat} (ha : 1 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio w * (coeffW w a * coeffW w a) := by
  by_cases h1 : a = 1
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 1) _ _
        (coeffW_two_eq_tailRatio_mul_one w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha2 : 1 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 1) (N := a) ha2
    have hr : coeffW w (a + 1) * coeffW w 1 ≤ coeffW w a * coeffW w 2 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc1p := FusionResidualBound.coeffW_pos hwp 1
    have hR : coeffW w 2 * (coeffW w a * coeffW w a) ≈
        coeffW w 1 * (tailRatio w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_two_eq_tailRatio_mul_one w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 1 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 1 * (tailRatio w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc1p

/-- Finite PF2 tail, with the vacuum edge isolated exactly. -/
theorem adjCorr_le_vacuum_plus_tail {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) (n : Nat) :
    adjCorr w (n + 1) ≤ coeffW w 1 + tailRatio w *
      fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) n := by
  let T := fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) n
  have ht : fsum (fun i => coeffW w (i + 1) * coeffW w ((i + 1) + 1)) n ≤
      fsum (fun i => tailRatio w *
        (coeffW w (i + 1) * coeffW w (i + 1))) n :=
    fsum_mono_lt n (fun i _ => adjacent_tail_le hw0 hw1 hwp (by omega))
  have hpull : fsum (fun i => tailRatio w *
      (coeffW w (i + 1) * coeffW w (i + 1))) n ≈ tailRatio w * T :=
    Q'.eqv_symm (fsum_const_mul (tailRatio w)
      (fun i => coeffW w (i + 1) * coeffW w (i + 1)) n)
  have hpeel := fsum_peel_local
    (fun a => coeffW w a * coeffW w (a + 1)) n
  have hhead : coeffW w 0 * coeffW w 1 ≈ coeffW w 1 := by
    rw [coeffW_zero]
    exact Q'.one_mul_eqv _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpeel) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left (coeffW w 0 * coeffW w 1) _ _ ht) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (q_add_congr hhead hpull) (Q'.eqv_refl _))

private theorem eval_sub_slack (w : Q') :
    eval blockRHS w ≈ eval blockLHS w + eval blockSlackP w := by
  have h := eval_psub blockRHS blockLHS w
  have h1 : eval blockLHS w + eval blockSlackP w ≈ eval blockRHS w := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ h) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv _)) ?_
    exact q_add_zero_eqv _
  exact Q'.eqv_symm h1

/-- The explicit two-coordinate block pays for the first-tail-ratio estimate. -/
theorem two_anchor_block_inequality {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ blockCap) :
    coeffW w 1 + tailRatio w * ((1 : Q') + coeffW w 1 * coeffW w 1) ≤
      retuneCube w * ((1 : Q') + coeffW w 1 * coeffW w 1) + tailRatio w := by
  have hs := blockSlack_nonneg hw0 hwc
  have hp : eval blockLHS w ≤ eval blockRHS w :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (eval blockLHS w) (eval blockSlackP w) hs)
      (Q'.ge_of_eqv (eval_sub_slack w))
  have hc : coeffW w 1 ≈ eval cOneP w := by
    refine Q'.eqv_trans _ _ _ (CircleFourierPowerModel.hcoeff w 1) ?_
    exact poly_eqv _ _ w (by decide)
  have hq : tailRatio w ≈ eval ratioP w := by
    unfold tailRatio ratioP
    exact Q'.eqv_symm (eval_monoP threeHalves w 5)
  have hr : retuneCube w ≈ eval retuneP w := by
    unfold retuneCube retuneBase
    change RGTransport.qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈ _
    have hpow : RGTransport.qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) := by
      change (((1 : Q') * _) * _) * _ ≈ _
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))
    refine Q'.eqv_trans _ _ _ hpow ?_
    let linP : Poly := [Q'.mkPos 1 2 (by decide), Q'.mkPos 1 2 (by decide)]
    let base : Q' := Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)
    have hlin : base ≈ eval linP w := by
      unfold base linP
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (Q'.mkPos 1 2 (by decide)) 1 w) ?_
      refine Q'.eqv_trans _ _ _
        (q_add_congr (Q'.mul_one_eqv _) (Q'.mul_comm_eqv _ _)) ?_
      show _ ≈ Q'.mkPos 1 2 (by decide) + w *
        (Q'.mkPos 1 2 (by decide) + w * 0)
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.mul_eqv_congr_left w _ _ ?_
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero w))
          (q_add_zero_eqv _))
    have hprod : base * base * base ≈ eval (pmul (pmul linP linP) linP) w := by
      refine Q'.eqv_trans _ _ _ (mul_eqv_both (mul_eqv_both hlin hlin) hlin) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_both (Q'.eqv_symm (eval_pmul linP linP w)) (Q'.eqv_refl _)) ?_
      exact Q'.eqv_symm (eval_pmul (pmul linP linP) linP w)
    refine Q'.eqv_trans _ _ _ hprod ?_
    exact poly_eqv (pmul (pmul linP linP) linP) retuneP w (by decide)
  have hB : ((1 : Q') + coeffW w 1 * coeffW w 1) ≈ eval blockP w := by
    have hOne : (1 : Q') ≈ eval ([1] : Poly) w := by
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 1 _ _ (q_mul_zero w))
          (q_add_zero_eqv 1))
    refine Q'.eqv_trans _ _ _
      (hEvalAdd hOne (hEvalMul hc hc)) ?_
    exact poly_eqv (padd [1] (pmul cOneP cOneP)) blockP w (by decide)
  have hL : coeffW w 1 + tailRatio w * ((1 : Q') + coeffW w 1 * coeffW w 1) ≈
      eval blockLHS w := by
    exact hEvalAdd hc (hEvalMul hq hB)
  have hR : retuneCube w * ((1 : Q') + coeffW w 1 * coeffW w 1) + tailRatio w ≈
      eval blockRHS w := by
    exact hEvalAdd (hEvalMul hr hB) hq
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (Q'.eqv_symm hR)))

/-- The two-coordinate certificate after cancelling its common tail term. -/
theorem two_anchor_head_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ blockCap) :
    coeffW w 1 + tailRatio w * (coeffW w 1 * coeffW w 1) ≤
      retuneCube w * ((1 : Q') + coeffW w 1 * coeffW w 1) := by
  have hb := two_anchor_block_inequality hw0 hwc
  have hL :
      (coeffW w 1 + tailRatio w * (coeffW w 1 * coeffW w 1)) + tailRatio w ≈
        coeffW w 1 + tailRatio w * ((1 : Q') + coeffW w 1 * coeffW w 1) := by
    ring_qeqv
  have hc :
      (coeffW w 1 + tailRatio w * (coeffW w 1 * coeffW w 1)) + tailRatio w ≤
        (retuneCube w * ((1 : Q') + coeffW w 1 * coeffW w 1)) + tailRatio w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hb
  exact YMGap.Continuum.MeanExpConvexProgress.le_of_add_le_add_right hc

/-- **Arbitrary-cutoff correlation theorem on the two-anchor window.** -/
theorem arbitrary_truncation_retune_two_anchor {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ blockCap) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hwc (by decide : blockCap ≤ (1 : Q'))
  by_cases hwz : w.eqv 0
  · have hAz : adjCorr w N ≈ (0 : Q') := by
      unfold adjCorr
      refine Q'.eqv_trans _ _ _
        (fsum_eqv_congr _ (fun _ => (0 : Q')) (fun a => ?_) N) ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w a) _ _
            (coeffW_excited_zero hwz a)) ?_
        exact Q'.mul_zero_eqv _
      · rw [fsum_zero_seq]
        exact Q'.eqv_refl 0
    have hR : (0 : Q') ≤ retuneCube w * coordNormSq w N :=
      Q'.mul_nonneg _ _
        (RGTransport.qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3)
        (coordNormSq_nonneg hw0 N)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hAz) hR
  · have hwp : (0 : Q') < w := pos_of_nonneg_not_eqv_zero hw0 hwz
    cases N with
    | zero =>
        exact Q'.mul_nonneg _ _
          (RGTransport.qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
    | succ n =>
        have hA := adjCorr_le_vacuum_plus_tail hw0 hw1 hwp n
        let T := fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) n
        cases n with
        | zero =>
            have hA1 : adjCorr w 1 ≤ coeffW w 1 := by
              refine Q'.le_trans' _ _ _ hA (Q'.le_of_eqv ?_)
              refine Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) ?_
              exact q_add_zero_eqv _
            have hhead := two_anchor_head_bound hw0 hwc
            have hc1sq : (0 : Q') ≤ tailRatio w * (coeffW w 1 * coeffW w 1) :=
              Q'.mul_nonneg _ _
                (Q'.mul_nonneg _ _ (by decide)
                  (RGTransport.qpow_nonneg w hw0 5))
                (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 1) (coeffW_nonneg hw0 1))
            have hc1 : coeffW w 1 ≤
                coeffW w 1 + tailRatio w * (coeffW w 1 * coeffW w 1) :=
              Q'.add_le_self_of_nonneg _ _ hc1sq
            have hD : (1 : Q') + coeffW w 1 * coeffW w 1 ≤ coordNormSq w 1 :=
              Q'.le_of_eqv (Q'.eqv_symm (by
                have hpeel : coordNormSq w 1 ≈
                    coeffW w 0 * coeffW w 0 +
                      fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) 1 := by
                  unfold coordNormSq
                  exact fsum_peel_local
                    (fun i => coeffW w i * coeffW w i) 1
                have h0 : coeffW w 0 * coeffW w 0 ≈ (1 : Q') := by
                  rw [coeffW_zero]
                  exact Q'.one_mul_eqv 1
                have ht : fsum
                    (fun i => coeffW w (i + 1) * coeffW w (i + 1)) 1 ≈
                      coeffW w 1 * coeffW w 1 := by
                  change (0 : Q') + coeffW w 1 * coeffW w 1 ≈ _
                  exact q_zero_add_eqv _
                exact Q'.eqv_trans _ _ _ hpeel (q_add_congr h0 ht)))
            have hr0 : (0 : Q') ≤ retuneCube w :=
              RGTransport.qpow_nonneg _
                (Q'.mul_nonneg _ _ (by decide)
                  (Q'.zero_le_add _ _ (by decide) hw0)) 3
            exact Q'.le_trans' _ _ _ hA1
              (Q'.le_trans' _ _ _ hc1
                (Q'.le_trans' _ _ _ hhead
                  (Q'.mul_le_mul_of_nonneg_left _ _ _ hD hr0)))
        | succ m =>
            let U := fsum
              (fun i => coeffW w ((i + 1) + 1) * coeffW w ((i + 1) + 1)) m
            have hT : T ≈ coeffW w 1 * coeffW w 1 + U := by
              unfold T U
              exact fsum_peel_local
                (fun i => coeffW w (i + 1) * coeffW w (i + 1)) m
            have hU0 : (0 : Q') ≤ U := fsum_nonneg (fun i =>
              Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)) m
            have hhead := two_anchor_head_bound hw0 hwc
            have htail := Q'.mul_le_mul_of_nonneg_right _ _ _
              (tailRatio_le_retune hw0 hwc) hU0
            have hadd := Q'.le_trans' _ _ _
              (Q'.add_le_add_right _ _ _ hhead)
              (Q'.add_le_add_left _ _ _ htail)
            have hmid : coeffW w 1 + tailRatio w * T ≤
                retuneCube w * (((1 : Q') + coeffW w 1 * coeffW w 1) + U) := by
              refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
                (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv ?_))
              · refine Q'.eqv_trans _ _ _
                  (Q'.add_eqv_congr_left _ _ _
                    (Q'.mul_eqv_congr_left (tailRatio w) _ _ hT)) ?_
                refine Q'.eqv_trans _ _ _
                  (Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv _ _ _)) ?_
                exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
              · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
            let last := coeffW w (m + 2) * coeffW w (m + 2)
            have hlast : (0 : Q') ≤ last :=
              Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)
            have hD : coordNormSq w (m + 2) ≈
                ((1 : Q') + coeffW w 1 * coeffW w 1) + (U + last) := by
              have h0 := fsum_peel_local
                (fun i => coeffW w i * coeffW w i) (m + 2)
              have h1 := fsum_peel_local
                (fun i => coeffW w (i + 1) * coeffW w (i + 1)) (m + 1)
              refine Q'.eqv_trans _ _ _ h0 ?_
              have hc0 : coeffW w 0 * coeffW w 0 ≈ (1 : Q') := by
                rw [coeffW_zero]
                exact Q'.one_mul_eqv 1
              have htail :
                  fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) (m + 2) ≈
                    coeffW w 1 * coeffW w 1 + (U + last) := by
                refine Q'.eqv_trans _ _ _ h1 ?_
                refine Q'.add_eqv_congr_left _ _ _ ?_
                unfold U last
                exact Q'.eqv_refl _
              refine Q'.eqv_trans _ _ _ (q_add_congr hc0 htail) ?_
              exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
            have hprefix :
                ((1 : Q') + coeffW w 1 * coeffW w 1) + U ≤ coordNormSq w (m + 2) := by
              refine Q'.le_trans' _ _ _
                (Q'.add_le_self_of_nonneg
                  (((1 : Q') + coeffW w 1 * coeffW w 1) + U) last hlast) ?_
              exact Q'.le_of_eqv
                (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
                  (Q'.eqv_symm hD))
            have hr0 : (0 : Q') ≤ retuneCube w :=
              RGTransport.qpow_nonneg _
                (Q'.mul_nonneg _ _ (by decide)
                  (Q'.zero_le_add _ _ (by decide) hw0)) 3
            exact Q'.le_trans' _ _ _ hA
              (Q'.le_trans' _ _ _ hmid
                (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0))

/-- Equivalent weighted Dirichlet/Poincaré form on `0≤w≤3/4`. -/
theorem weighted_poincare_two_anchor {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ blockCap) (N : Nat) :
    Q'.ofNat 2 * ((1 : Q') - retuneCube w) * coordNormSq w N ≤
      coeffW w 0 * coeffW w 0 + coeffW w N * coeffW w N +
        dirichletEnergy w N := by
  let D := coordNormSq w N
  let A := adjCorr w N
  let R := retuneCube w * D
  have hAR : A ≤ R := arbitrary_truncation_retune_two_anchor hw0 hwc N
  have hsub : D + (-R) ≤ D + (-A) :=
    Q'.add_le_add_left D _ _ (Q'.neg_le_neg hAR)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hsub (by decide)
  have hL : Q'.ofNat 2 * ((1 : Q') - retuneCube w) * D ≈
      Q'.ofNat 2 * (D + (-R)) := by
    unfold R
    have hdist : (((1 : Q') - retuneCube w) * D).eqv
        (D + (-(retuneCube w * D))) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-retuneCube w) D) ?_
      exact Q'.add_eqv_congr' (Q'.one_mul_eqv D)
        (Q'.neg_mul_eqv (retuneCube w) D)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 2) ((1 : Q') - retuneCube w) D) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hdist
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv (twice_norm_sub_corr_eq_boundary_dirichlet w N)))

end YMGap.Continuum.TwoAnchorBlockCorrBound

#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.blockSlack_nonneg
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.tailRatio_le_retune
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.coeffW_two_eq_tailRatio_mul_one
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.adjacent_tail_le
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.adjCorr_le_vacuum_plus_tail
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.two_anchor_block_inequality
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.two_anchor_head_bound
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.arbitrary_truncation_retune_two_anchor
#print axioms YMGap.Continuum.TwoAnchorBlockCorrBound.weighted_poincare_two_anchor
