/-
An exact three-anchor correlation window through `w = 5/6`.

The retained head uses the three adjacent edges `A_3`, but only the diagonal
mass `D_2`.  Thus the square `c_3^2` remains available for the first symbolic
tail edge.  Positivity of the head residual on `0 <= w <= 5/6` is certified by
an exact degree-26 Bernstein decomposition after the rescaling `w=(5/6)x`.
The tail is controlled by the exact anchor ratio `c_3/c_2=(4/3)w^7` and PF2.
-/

import YMGap.Continuum.HarmonicK3Retune

namespace YMGap.Continuum.ThreeAnchorWindowRetune

set_option maxHeartbeats 1800000
set_option maxRecDepth 40000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicK3Retune
open YMGap.Continuum.HarmonicThetaRatioExtension
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

def threeAnchorCap : Q' := Q'.mkPos 5 6 (by decide)
private def capInv : Q' := Q'.mkPos 6 5 (by decide)
private def fourThirds : Q' := Q'.mkPos 4 3 (by decide)

/-- The exact PF2 anchor ratio `c_3/c_2`. -/
def tailRatio3 (w : Q') : Q' := fourThirds * qpow w 7

private def retuneP : Poly :=
  [Q'.mkPos 1 8 (by decide), Q'.mkPos 3 8 (by decide),
   Q'.mkPos 3 8 (by decide), Q'.mkPos 1 8 (by decide)]

private def prefixAP (N : Nat) : Poly :=
  fsumP (fun a => pmul (coeffPoly a) (coeffPoly (a + 1))) N

private def prefixDP (N : Nat) : Poly :=
  fsumP (fun a => pmul (coeffPoly a) (coeffPoly a)) (N + 1)

private def headSlackP : Poly :=
  psub (pmul retuneP (prefixDP 2)) (prefixAP 3)

private def oneSlackP : Poly :=
  psub (pmul retuneP (prefixDP 1)) (prefixAP 1)

private def ratio3P : Poly := monoP fourThirds 7
private def ratioSlackP : Poly := psub retuneP ratio3P

/-- Scale the variable of a coefficient-list polynomial. -/
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

private theorem scaled_bernstein_nonneg
    (p : Poly) (D : Nat) (terms : List (Nat × Q'))
    (hrep : allZero
      (psub (scaleVar threeAnchorCap p) (bernTermsP D terms)))
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) :
    (0 : Q') ≤ eval p w := by
  let x := capInv * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ capInv hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP D terms) x :=
    eval_bernTermsP_nonneg hx0 hx1 D terms hnn
  have hs : (0 : Q') ≤ eval (scaleVar threeAnchorCap p) x :=
    Q'.le_trans' _ _ _ hb
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (eval_scaleVar threeAnchorCap x p) ?_
  apply eval_eqv_arg
  unfold x
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w (by decide : threeAnchorCap * capInv ≈ 1)) ?_
  exact Q'.one_mul_eqv w

private def headBern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 57 16 (by decide)),
   (2, Q'.mkPos 4675 96 (by decide)),
   (3, Q'.mkPos 244175 576 (by decide)),
   (4, Q'.mkPos 1517425 576 (by decide)),
   (5, Q'.mkPos 7158635 576 (by decide)),
   (6, Q'.mkPos 4313587195 93312 (by decide)),
   (7, Q'.mkPos 2882987825 20736 (by decide)),
   (8, Q'.mkPos 385284631675 1119744 (by decide)),
   (9, Q'.mkPos 14298769904525 20155392 (by decide)),
   (10, Q'.mkPos 24774706648315 20155392 (by decide)),
   (11, Q'.mkPos 108853890994795 60466176 (by decide)),
   (12, Q'.mkPos 15026954520325 6718464 (by decide)),
   (13, Q'.mkPos 47592699482725 20155392 (by decide)),
   (14, Q'.mkPos 128086130547425 60466176 (by decide)),
   (15, Q'.mkPos 32502794746165 20155392 (by decide)),
   (16, Q'.mkPos 2605803995823651265 2507653251072 (by decide)),
   (17, Q'.mkPos 2832939015207038425 5015306502144 (by decide)),
   (18, Q'.mkPos 7761984724954540675 30091839012864 (by decide)),
   (19, Q'.mkPos 53320685957891174525 541653102231552 (by decide)),
   (20, Q'.mkPos 16872745968402953795 541653102231552 (by decide)),
   (21, Q'.mkPos 1453919763682883315 180551034077184 (by decide)),
   (22, Q'.mkPos 895101907973136475 541653102231552 (by decide)),
   (23, Q'.mkPos 33836678941290179675 131621703842267136 (by decide)),
   (24, Q'.mkPos 1265768733177389975 43873901280755712 (by decide)),
   (25, Q'.mkPos 95087813523051389 43873901280755712 (by decide)),
   (26, Q'.mkPos 4075003491981647 131621703842267136 (by decide))]

private theorem head_bernstein_identity :
    allZero (psub (scaleVar threeAnchorCap headSlackP)
      (bernTermsP 26 headBern)) := by decide

private def oneBern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 23 16 (by decide)),
   (2, Q'.mkPos 697 96 (by decide)),
   (3, Q'.mkPos 11513 576 (by decide)),
   (4, Q'.mkPos 773 24 (by decide)),
   (5, Q'.mkPos 5849 192 (by decide)),
   (6, Q'.mkPos 1453861 93312 (by decide)),
   (7, Q'.mkPos 627743 186624 (by decide)),
   (8, Q'.mkPos 700897 1119744 (by decide)),
   (9, Q'.mkPos 12993659 20155392 (by decide))]

private theorem one_bernstein_identity :
    allZero (psub (scaleVar threeAnchorCap oneSlackP)
      (bernTermsP 9 oneBern)) := by decide

private def ratioBern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 19 16 (by decide)),
   (2, Q'.mkPos 457 96 (by decide)),
   (3, Q'.mkPos 18035 1728 (by decide)),
   (4, Q'.mkPos 365 27 (by decide)),
   (5, Q'.mkPos 2981 288 (by decide)),
   (6, Q'.mkPos 3751 864 (by decide)),
   (7, Q'.mkPos 167183 419904 (by decide))]

private theorem ratio_bernstein_identity :
    allZero (psub (scaleVar threeAnchorCap ratioSlackP)
      (bernTermsP 7 ratioBern)) := by decide

private theorem prefixA_eval (w : Q') (N : Nat) :
    adjCorr w N ≈ eval (prefixAP N) w := by
  unfold adjCorr prefixAP
  exact fsum_eval
    (fun a => coeffW w a * coeffW w (a + 1))
    (fun a => pmul (coeffPoly a) (coeffPoly (a + 1)))
    (fun a => hEvalMul (hcoeff w a) (hcoeff w (a + 1))) N

private theorem prefixD_eval (w : Q') (N : Nat) :
    coordNormSq w N ≈ eval (prefixDP N) w := by
  unfold coordNormSq prefixDP
  exact fsum_eval
    (fun a => coeffW w a * coeffW w a)
    (fun a => pmul (coeffPoly a) (coeffPoly a))
    (fun a => hEvalMul (hcoeff w a) (hcoeff w a)) (N + 1)

private theorem retune_eval (w : Q') : retuneCube w ≈ eval retuneP w := by
  unfold retuneCube retuneBase retuneP
  change qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈ _
  have hpow : qpow (Q'.mkPos 1 2 (by decide) * ((1 : Q') + w)) 3 ≈
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
      (Q'.add_eqv_congr' (Q'.mul_one_eqv _) (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.mul_eqv_congr_left w _ _ ?_
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv w))
      (QPoly.q_add_zero_eqv _))
  have hprod : base * base * base ≈ eval (pmul (pmul linP linP) linP) w := by
    refine Q'.eqv_trans _ _ _ (mul_eqv_both (mul_eqv_both hlin hlin) hlin) ?_
    refine Q'.eqv_trans _ _ _
      (mul_eqv_both (Q'.eqv_symm (eval_pmul linP linP w)) (Q'.eqv_refl _)) ?_
    exact Q'.eqv_symm (eval_pmul (pmul linP linP) linP w)
  refine Q'.eqv_trans _ _ _ hprod ?_
  exact poly_eqv (pmul (pmul linP linP) linP)
    [Q'.mkPos 1 8 (by decide), Q'.mkPos 3 8 (by decide),
     Q'.mkPos 3 8 (by decide), Q'.mkPos 1 8 (by decide)] w (by decide)

private theorem slack_nonneg_to_bound (w : Q') (A D : Q')
    (pA pD slack : Poly)
    (hA : A ≈ eval pA w) (hD : D ≈ eval pD w)
    (hslackDef : slack = psub (pmul retuneP pD) pA)
    (hs : (0 : Q') ≤ eval slack w) :
    A ≤ retuneCube w * D := by
  have hRD : retuneCube w * D ≈ eval (pmul retuneP pD) w :=
    hEvalMul (retune_eval w) hD
  have he : eval slack w ≈ retuneCube w * D + -A := by
    rw [hslackDef]
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm hRD) (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hA))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

/-- **Bernstein-certified strengthened three-anchor head.**  Uniformly on
`0≤w≤5/6`, all three retained edges are paid for by `D_2`, leaving `c_3²`
unused for the tail. -/
theorem strengthened_three_anchor_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) :
    adjCorr w 3 ≤ retuneCube w * coordNormSq w 2 := by
  apply slack_nonneg_to_bound w (adjCorr w 3) (coordNormSq w 2)
    (prefixAP 3) (prefixDP 2) headSlackP
    (prefixA_eval w 3) (prefixD_eval w 2) rfl
  exact scaled_bernstein_nonneg headSlackP 26 headBern
    head_bernstein_identity (by decide) hw0 hwc

/-- The only shorter prefix not inherited from the strengthened head. -/
theorem one_edge_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) :
    adjCorr w 1 ≤ retuneCube w * coordNormSq w 1 := by
  apply slack_nonneg_to_bound w (adjCorr w 1) (coordNormSq w 1)
    (prefixAP 1) (prefixDP 1) oneSlackP
    (prefixA_eval w 1) (prefixD_eval w 1) rfl
  exact scaled_bernstein_nonneg oneSlackP 9 oneBern
    one_bernstein_identity (by decide) hw0 hwc

/-- The exact tail anchor remains below the retune factor on the full window. -/
theorem tailRatio3_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) :
    tailRatio3 w ≤ retuneCube w := by
  have hs := scaled_bernstein_nonneg ratioSlackP 7 ratioBern
    ratio_bernstein_identity (by decide) hw0 hwc
  have hq : tailRatio3 w ≈ eval ratio3P w := by
    unfold tailRatio3 ratio3P
    exact Q'.eqv_symm (eval_monoP fourThirds w 7)
  have he : eval ratioSlackP w ≈ retuneCube w + -(tailRatio3 w) := by
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (retune_eval w))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hq))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

theorem coeffW_three_eq_tailRatio3_mul_two (w : Q') :
    coeffW w 3 ≈ tailRatio3 w * coeffW w 2 := by
  have hc3 := hcoeff w 3
  have hq : tailRatio3 w ≈ eval ratio3P w := by
    unfold tailRatio3 ratio3P
    exact Q'.eqv_symm (eval_monoP fourThirds w 7)
  have hc2 := hcoeff w 2
  refine Q'.eqv_trans _ _ _ hc3 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 3) (pmul ratio3P (coeffPoly 2)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc2)

/-- PF2 propagates the exact `c_3/c_2` ratio through every later edge. -/
theorem adjacent_tail3_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    {a : Nat} (ha : 2 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio3 w * (coeffW w a * coeffW w a) := by
  by_cases h2 : a = 2
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 2) _ _
        (coeffW_three_eq_tailRatio3_mul_two w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha3 : 2 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 2) (N := a) ha3
    have hr : coeffW w (a + 1) * coeffW w 2 ≤ coeffW w a * coeffW w 3 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc2p := FusionResidualBound.coeffW_pos hwp 2
    have hR : coeffW w 3 * (coeffW w a * coeffW w a) ≈
        coeffW w 2 * (tailRatio3 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_three_eq_tailRatio3_mul_two w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 2 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 2 * (tailRatio3 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc2p

private def edgeTail (w : Q') (j : Nat) : Q' :=
  coeffW w (3 + j) * coeffW w (3 + j + 1)

private def squareTail (w : Q') (j : Nat) : Q' :=
  coeffW w (3 + j) * coeffW w (3 + j)

private theorem tail_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hwc : w ≤ threeAnchorCap) (M : Nat) :
    fsum (edgeTail w) M ≤ retuneCube w * fsum (squareTail w) M := by
  have hterm : ∀ j, edgeTail w j ≤ retuneCube w * squareTail w j := by
    intro j
    have ht := adjacent_tail3_le hw0 hw1 hwp (a := 3 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (tailRatio3_le_retune hw0 hwc)
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (3 + j)) (coeffW_nonneg hw0 (3 + j))))
  have hsum : fsum (edgeTail w) M ≤
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : retuneCube w * fsum (squareTail w) M ≈
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail w) (retuneCube w) M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-- **All-cutoff interval theorem.**  This is uniform in both `w` and `N`; the
only closed computation is the finite Bernstein certificate, not enumeration
of harmonic scales or cutoffs. -/
theorem three_anchor_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  by_cases hwz : w.eqv 0
  · have hA0 : adjCorr w N ≈ (0 : Q') := by
      unfold adjCorr
      refine Q'.eqv_trans _ _ _
        (fsum_eqv_congr _ (fun _ => (0 : Q')) (fun a => ?_) N) ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w a) _ _
            (coeffW_excited_zero hwz a)) ?_
        exact Q'.mul_zero_eqv _
      · rw [fsum_zero_seq]
        exact Q'.eqv_refl 0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA0)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3)
        (coordNormSq_nonneg hw0 N))
  · have hwp : (0 : Q') < w := pos_of_nonneg_not_eqv_zero hw0 hwz
    rcases Nat.le_total N 3 with hsmall | hlarge
    · have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact Q'.mul_nonneg _ _
          (qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
      · exact one_edge_head hw0 hwc
      · have hA23 : adjCorr w 2 ≤ adjCorr w 3 := by
          unfold adjCorr
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (i + 1))) (by omega)
        exact Q'.le_trans' _ _ _ hA23 (strengthened_three_anchor_head hw0 hwc)
      · have hD23 : coordNormSq w 2 ≤ coordNormSq w 3 := by
          unfold coordNormSq
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)) (by omega)
        have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3
        exact Q'.le_trans' _ _ _ (strengthened_three_anchor_head hw0 hwc)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hD23 hr0)
    · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
      have hA : adjCorr w (3 + M) ≈
          adjCorr w 3 + fsum (edgeTail w) M := by
        unfold adjCorr edgeTail
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w (a + 1)) 3 M
      have hD : coordNormSq w (3 + M) ≈
          coordNormSq w 2 + fsum (squareTail w) (M + 1) := by
        unfold coordNormSq squareTail
        rw [show 3 + M + 1 = 3 + (M + 1) by omega]
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w a) 3 (M + 1)
      have hsquare0 : ∀ j, (0 : Q') ≤ squareTail w j := by
        intro j
        unfold squareTail
        exact Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (3 + j)) (coeffW_nonneg hw0 (3 + j))
      have htailPrefix : fsum (squareTail w) M ≤
          fsum (squareTail w) (M + 1) :=
        AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
      have hprefix : coordNormSq w 2 + fsum (squareTail w) M ≤
          coordNormSq w (3 + M) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_left (coordNormSq w 2) _ _ htailPrefix)
          (Q'.ge_of_eqv hD)
      have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) hw0)) 3
      have hpaid : adjCorr w 3 + fsum (edgeTail w) M ≤
          retuneCube w * coordNormSq w 2 +
            retuneCube w * fsum (squareTail w) M :=
        AFRateCalibration.q_add_le_add
          (strengthened_three_anchor_head hw0 hwc)
          (tail_sum_le hw0 hw1 hwp hwc M)
      have hcollect : retuneCube w * coordNormSq w 2 +
          retuneCube w * fsum (squareTail w) M ≈
          retuneCube w * (coordNormSq w 2 + fsum (squareTail w) M) :=
        Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
        (Q'.le_trans' _ _ _ hpaid
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

theorem three_anchor_ratio_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) (N : Nat) :
    Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) ≤
      retuneCube w := by
  exact Q'.divPos_le_of_le_mul _ _ _
    (three_anchor_retune_all_cutoffs hw0 hwc N)

theorem three_anchor_lamPW_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ threeAnchorCap) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _ (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (three_anchor_ratio_all_cutoffs hw0 hwc N)

theorem harmW_four_mem_window : harmW 4 ≤ threeAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit threeAnchorCap
  decide

theorem harmonicMass_k4_retune_floor :
    (1 : Q') - retuneCube (harmW 4) ≤ harmonicMass 4 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (three_anchor_lamPW_le_retune
      (harmW_nonneg 4) harmW_four_mem_window (Ncut 4)))

theorem initial_five_retune {k : Nat} (hk : k ≤ 4) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact initial_four_retune (by decide)
  · exact initial_four_retune (by decide)
  · exact initial_four_retune (by decide)
  · exact initial_four_retune (by decide)
  · exact three_anchor_retune_all_cutoffs
      (harmW_nonneg 4) harmW_four_mem_window (Ncut 4)

theorem harmonicSchur_spacing_k4 :
    harmonicSchurAll 4 * harmonicSpacing 5 ≤
      harmonicMass 5 * harmonicSpacing 4 := by
  decide

theorem harmonicSchur_spacing_initial_five {k : Nat} (hk : k ≤ 4) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact harmonicSchur_spacing_initial_four (by decide)
  · exact harmonicSchur_spacing_initial_four (by decide)
  · exact harmonicSchur_spacing_initial_four (by decide)
  · exact harmonicSchur_spacing_initial_four (by decide)
  · exact harmonicSchur_spacing_k4

theorem harmonic_operator_spacing_k4 :
    harmonicHead 4 * harmonicSpacing 5 ≤
      (harmonicErosionAll 4 + harmonicMass 5) * harmonicSpacing 4 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 4)
    (harmonicErosionAll_nonneg 4)
    (Q'.le_of_lt (harmonicSpacing_pos 5))
    (harmonicSpacing_contracts 4)
    (harmonicCoupling_size_all 4)
    harmonicSchur_spacing_k4

theorem harmonic_operator_spacing_initial_five {k : Nat} (hk : k ≤ 4) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_five hk)

end YMGap.Continuum.ThreeAnchorWindowRetune

#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.strengthened_three_anchor_head
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.one_edge_head
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.tailRatio3_le_retune
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.coeffW_three_eq_tailRatio3_mul_two
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.adjacent_tail3_le
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.three_anchor_retune_all_cutoffs
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.three_anchor_ratio_all_cutoffs
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.three_anchor_lamPW_le_retune
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.harmonicMass_k4_retune_floor
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.initial_five_retune
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.harmonicSchur_spacing_k4
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.harmonicSchur_spacing_initial_five
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.harmonic_operator_spacing_k4
#print axioms YMGap.Continuum.ThreeAnchorWindowRetune.harmonic_operator_spacing_initial_five
