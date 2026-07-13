/-
Exact four-anchor correlation window through `w = 6/7`.

The three-anchor strengthened residual is negative at this endpoint, so the
minimal next localization retains four adjacent edges.  Its Bernstein-certified
head inequality is `A_4 <= r D_3`; hence `c_4^2` is not used by the head and
can pay the first tail edge.  PF2 propagates the exact ratio
`c_4/c_3 = (5/4) w^9` through every later mode.
-/

import YMGap.Continuum.ThreeAnchorWindowRetune

namespace YMGap.Continuum.FourAnchorWindowRetune

set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicK3Retune
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

def fourAnchorCap : Q' := Q'.mkPos 6 7 (by decide)
private def capInv : Q' := Q'.mkPos 7 6 (by decide)
private def fiveFourths : Q' := Q'.mkPos 5 4 (by decide)

/-- Exact anchor ratio `c_4/c_3`. -/
def tailRatio4 (w : Q') : Q' := fiveFourths * qpow w 9

private def headSlack4P : Poly :=
  psub (pmul retuneP (prefixDP 3)) (prefixAP 4)

private def oneSlack4P : Poly :=
  psub (pmul retuneP (prefixDP 1)) (prefixAP 1)

private def twoSlack4P : Poly :=
  psub (pmul retuneP (prefixDP 2)) (prefixAP 2)

private def ratio4P : Poly := monoP fiveFourths 9
private def ratioSlack4P : Poly := psub retuneP ratio4P

private theorem scaled_bernstein_nonneg
    (p : Poly) (D : Nat) (terms : List (Nat × Q'))
    (hrep : allZero
      (psub (scaleVar fourAnchorCap p) (bernTermsP D terms)))
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) :
    (0 : Q') ≤ eval p w := by
  let x := capInv * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ capInv hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP D terms) x :=
    eval_bernTermsP_nonneg hx0 hx1 D terms hnn
  have hs : (0 : Q') ≤ eval (scaleVar fourAnchorCap p) x :=
    Q'.le_trans' _ _ _ hb
      (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (eval_scaleVar fourAnchorCap x p) ?_
  apply eval_eqv_arg
  unfold x
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w (by decide : fourAnchorCap * capInv ≈ 1)) ?_
  exact Q'.one_mul_eqv w

private def head4Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 291 56 (by decide)),
   (2, Q'.mkPos 41205 392 (by decide)),
   (3, Q'.mkPos 3779455 2744 (by decide)),
   (4, Q'.mkPos 36039501 2744 (by decide)),
   (5, Q'.mkPos 38060343 392 (by decide)),
   (6, Q'.mkPos 544886197503 941192 (by decide)),
   (7, Q'.mkPos 18846138853341 6588344 (by decide)),
   (8, Q'.mkPos 137691882095337 11529602 (by decide)),
   (9, Q'.mkPos 3449939305876699 80707214 (by decide)),
   (10, Q'.mkPos 10706291032244043 80707214 (by decide)),
   (11, Q'.mkPos 1423947659111317191 3954653486 (by decide)),
   (12, Q'.mkPos 486296075948379199 564950498 (by decide)),
   (13, Q'.mkPos 1029551852032842555 564950498 (by decide)),
   (14, Q'.mkPos 1938831149709398835 564950498 (by decide)),
   (15, Q'.mkPos 3258891390931860735 564950498 (by decide)),
   (16, Q'.mkPos 1153468631373808794218847 132931722278404 (by decide)),
   (17, Q'.mkPos 10890851074851707728478973 930522055948828 (by decide)),
   (18, Q'.mkPos 92331339318768609501099339 6513654391641796 (by decide)),
   (19, Q'.mkPos 703435441091100072362531649 45595580741492572 (by decide)),
   (20, Q'.mkPos 688227953067705254063090715 45595580741492572 (by decide)),
   (21, Q'.mkPos 605226523901531930490353799 45595580741492572 (by decide)),
   (22, Q'.mkPos 478128137816545410297024783 45595580741492572 (by decide)),
   (23, Q'.mkPos 813940621673771115436781170539 109474989360323665372 (by decide)),
   (24, Q'.mkPos 258623940668545066493406287619 54737494680161832686 (by decide)),
   (25, Q'.mkPos 147051944417635230571636173327 54737494680161832686 (by decide)),
   (26, Q'.mkPos 10664089337782516715336684457 7819642097165976098 (by decide)),
   (27, Q'.mkPos 4819880461940276792338551373 7819642097165976098 (by decide)),
   (28, Q'.mkPos 1932821362043509571440842171 7819642097165976098 (by decide)),
   (29, Q'.mkPos 684525006602555088675950247 7819642097165976098 (by decide)),
   (30, Q'.mkPos 1226610616976685094914004403525791 45078680581384516175726498 (by decide)),
   (31, Q'.mkPos 2322586455920445010968170048250045 315550764069691613230085486 (by decide)),
   (32, Q'.mkPos 15132530274950885876017828199208009 8835421393951365170442393608 (by decide)),
   (33, Q'.mkPos 20880338145935152884095342275233531 61847949757659556193096755256 (by decide)),
   (34, Q'.mkPos 3417117874629889431530568562867899 61847949757659556193096755256 (by decide)),
   (35, Q'.mkPos 451719883424020874120630213663655 61847949757659556193096755256 (by decide)),
   (36, Q'.mkPos 46262342346534464688947584123573 61847949757659556193096755256 (by decide)),
   (37, Q'.mkPos 3425259727777054547243167835529 61847949757659556193096755256 (by decide)),
   (38, Q'.mkPos 169701548610613832634640553121 61847949757659556193096755256 (by decide)),
   (39, Q'.mkPos 381805460268496533042707843429365
      7276349441038889126561640159113144 (by decide))]

private theorem head4_bernstein_identity :
    allZero (psub (scaleVar fourAnchorCap headSlack4P)
      (bernTermsP 39 head4Bern)) := by decide

private def one4Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 81 56 (by decide)),
   (2, Q'.mkPos 360 49 (by decide)),
   (3, Q'.mkPos 6945 343 (by decide)),
   (4, Q'.mkPos 44523 1372 (by decide)),
   (5, Q'.mkPos 41409 1372 (by decide)),
   (6, Q'.mkPos 1732497 117649 (by decide)),
   (7, Q'.mkPos 2206332 823543 (by decide)),
   (8, Q'.mkPos 27306333 46118408 (by decide)),
   (9, Q'.mkPos 261892837 322828856 (by decide))]

private theorem one4_bernstein_identity :
    allZero (psub (scaleVar fourAnchorCap oneSlack4P)
      (bernTermsP 9 one4Bern)) := by decide

private def two4Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 151 56 (by decide)),
   (2, Q'.mkPos 10755 392 (by decide)),
   (3, Q'.mkPos 476925 2744 (by decide)),
   (4, Q'.mkPos 525039 686 (by decide)),
   (5, Q'.mkPos 1703151 686 (by decide)),
   (6, Q'.mkPos 1444773975 235298 (by decide)),
   (7, Q'.mkPos 19475910969 1647086 (by decide)),
   (8, Q'.mkPos 413937566559 23059204 (by decide)),
   (9, Q'.mkPos 3488202449065 161414428 (by decide)),
   (10, Q'.mkPos 3332258854723 161414428 (by decide)),
   (11, Q'.mkPos 123371967860235 7909306972 (by decide)),
   (12, Q'.mkPos 36669010714467 3954653486 (by decide)),
   (13, Q'.mkPos 2441373377253 564950498 (by decide)),
   (14, Q'.mkPos 895756055283 564950498 (by decide)),
   (15, Q'.mkPos 261205301211 564950498 (by decide)),
   (16, Q'.mkPos 27638307982678857 265863444556808 (by decide)),
   (17, Q'.mkPos 27568813948665039 1861044111897656 (by decide)),
   (18, Q'.mkPos 11538167183771563 13027308783283592 (by decide)),
   (19, Q'.mkPos 29370314644177813 91191161482985144 (by decide))]

private theorem two4_bernstein_identity :
    allZero (psub (scaleVar fourAnchorCap twoSlack4P)
      (bernTermsP 19 two4Bern)) := by decide

private def ratio4Bern : List (Nat × Q') :=
  [(0, Q'.mkPos 1 8 (by decide)),
   (1, Q'.mkPos 81 56 (by decide)),
   (2, Q'.mkPos 360 49 (by decide)),
   (3, Q'.mkPos 7377 343 (by decide)),
   (4, Q'.mkPos 54891 1372 (by decide)),
   (5, Q'.mkPos 67329 1372 (by decide)),
   (6, Q'.mkPos 13623 343 (by decide)),
   (7, Q'.mkPos 7020 343 (by decide)),
   (8, Q'.mkPos 16731 2744 (by decide)),
   (9, Q'.mkPos 157697893 322828856 (by decide))]

private theorem ratio4_bernstein_identity :
    allZero (psub (scaleVar fourAnchorCap ratioSlack4P)
      (bernTermsP 9 ratio4Bern)) := by decide

/-- Degree-39 exact Bernstein certificate for the strengthened four-anchor
head `A_4 <= r D_3` on the full interval. -/
theorem strengthened_four_anchor_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) :
    adjCorr w 4 ≤ retuneCube w * coordNormSq w 3 := by
  apply slack_nonneg_to_bound w (adjCorr w 4) (coordNormSq w 3)
    (prefixAP 4) (prefixDP 3) headSlack4P
    (prefixA_eval w 4) (prefixD_eval w 3) rfl
  exact scaled_bernstein_nonneg headSlack4P 39 head4Bern
    head4_bernstein_identity (by decide) hw0 hwc

theorem one_edge_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) :
    adjCorr w 1 ≤ retuneCube w * coordNormSq w 1 := by
  apply slack_nonneg_to_bound w (adjCorr w 1) (coordNormSq w 1)
    (prefixAP 1) (prefixDP 1) oneSlack4P
    (prefixA_eval w 1) (prefixD_eval w 1) rfl
  exact scaled_bernstein_nonneg oneSlack4P 9 one4Bern
    one4_bernstein_identity (by decide) hw0 hwc

theorem two_edge_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) :
    adjCorr w 2 ≤ retuneCube w * coordNormSq w 2 := by
  apply slack_nonneg_to_bound w (adjCorr w 2) (coordNormSq w 2)
    (prefixAP 2) (prefixDP 2) twoSlack4P
    (prefixA_eval w 2) (prefixD_eval w 2) rfl
  exact scaled_bernstein_nonneg twoSlack4P 19 two4Bern
    two4_bernstein_identity (by decide) hw0 hwc

theorem tailRatio4_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) :
    tailRatio4 w ≤ retuneCube w := by
  have hs := scaled_bernstein_nonneg ratioSlack4P 9 ratio4Bern
    ratio4_bernstein_identity (by decide) hw0 hwc
  have hq : tailRatio4 w ≈ eval ratio4P w := by
    unfold tailRatio4 ratio4P
    exact Q'.eqv_symm (eval_monoP fiveFourths w 9)
  have he : eval ratioSlack4P w ≈ retuneCube w + -(tailRatio4 w) := by
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (retune_eval w))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hq))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

theorem coeffW_four_eq_tailRatio4_mul_three (w : Q') :
    coeffW w 4 ≈ tailRatio4 w * coeffW w 3 := by
  have hc4 := hcoeff w 4
  have hq : tailRatio4 w ≈ eval ratio4P w := by
    unfold tailRatio4 ratio4P
    exact Q'.eqv_symm (eval_monoP fiveFourths w 9)
  have hc3 := hcoeff w 3
  refine Q'.eqv_trans _ _ _ hc4 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 4) (pmul ratio4P (coeffPoly 3)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc3)

theorem adjacent_tail4_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    {a : Nat} (ha : 3 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio4 w * (coeffW w a * coeffW w a) := by
  by_cases h3 : a = 3
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 3) _ _
        (coeffW_four_eq_tailRatio4_mul_three w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha4 : 3 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 3) (N := a) ha4
    have hr : coeffW w (a + 1) * coeffW w 3 ≤ coeffW w a * coeffW w 4 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc3p := FusionResidualBound.coeffW_pos hwp 3
    have hR : coeffW w 4 * (coeffW w a * coeffW w a) ≈
        coeffW w 3 * (tailRatio4 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_four_eq_tailRatio4_mul_three w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 3 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 3 * (tailRatio4 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc3p

private def edgeTail (w : Q') (j : Nat) : Q' :=
  coeffW w (4 + j) * coeffW w (4 + j + 1)

private def squareTail (w : Q') (j : Nat) : Q' :=
  coeffW w (4 + j) * coeffW w (4 + j)

private theorem tail_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hwc : w ≤ fourAnchorCap) (M : Nat) :
    fsum (edgeTail w) M ≤ retuneCube w * fsum (squareTail w) M := by
  have hterm : ∀ j, edgeTail w j ≤ retuneCube w * squareTail w j := by
    intro j
    have ht := adjacent_tail4_le hw0 hw1 hwp (a := 4 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (tailRatio4_le_retune hw0 hwc)
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (4 + j)) (coeffW_nonneg hw0 (4 + j))))
  have hsum : fsum (edgeTail w) M ≤
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : retuneCube w * fsum (squareTail w) M ≈
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail w) (retuneCube w) M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-- Uniform all-cutoff theorem on the exact window `0 <= w <= 6/7`. -/
theorem four_anchor_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) (N : Nat) :
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
    rcases Nat.le_total N 4 with hsmall | hlarge
    · have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl
      · exact Q'.mul_nonneg _ _
          (qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
      · exact one_edge_head hw0 hwc
      · exact two_edge_head hw0 hwc
      · have hA34 : adjCorr w 3 ≤ adjCorr w 4 := by
          unfold adjCorr
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (i + 1))) (by omega)
        exact Q'.le_trans' _ _ _ hA34 (strengthened_four_anchor_head hw0 hwc)
      · have hD34 : coordNormSq w 3 ≤ coordNormSq w 4 := by
          unfold coordNormSq
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)) (by omega)
        have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3
        exact Q'.le_trans' _ _ _ (strengthened_four_anchor_head hw0 hwc)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hD34 hr0)
    · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
      have hA : adjCorr w (4 + M) ≈
          adjCorr w 4 + fsum (edgeTail w) M := by
        unfold adjCorr edgeTail
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w (a + 1)) 4 M
      have hD : coordNormSq w (4 + M) ≈
          coordNormSq w 3 + fsum (squareTail w) (M + 1) := by
        unfold coordNormSq squareTail
        rw [show 4 + M + 1 = 4 + (M + 1) by omega]
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w a) 4 (M + 1)
      have hsquare0 : ∀ j, (0 : Q') ≤ squareTail w j := by
        intro j
        unfold squareTail
        exact Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (4 + j)) (coeffW_nonneg hw0 (4 + j))
      have htailPrefix : fsum (squareTail w) M ≤
          fsum (squareTail w) (M + 1) :=
        AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
      have hprefix : coordNormSq w 3 + fsum (squareTail w) M ≤
          coordNormSq w (4 + M) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_left (coordNormSq w 3) _ _ htailPrefix)
          (Q'.ge_of_eqv hD)
      have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) hw0)) 3
      have hpaid : adjCorr w 4 + fsum (edgeTail w) M ≤
          retuneCube w * coordNormSq w 3 +
            retuneCube w * fsum (squareTail w) M :=
        AFRateCalibration.q_add_le_add
          (strengthened_four_anchor_head hw0 hwc)
          (tail_sum_le hw0 hw1 hwp hwc M)
      have hcollect : retuneCube w * coordNormSq w 3 +
          retuneCube w * fsum (squareTail w) M ≈
          retuneCube w * (coordNormSq w 3 + fsum (squareTail w) M) :=
        Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
        (Q'.le_trans' _ _ _ hpaid
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

theorem four_anchor_ratio_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) (N : Nat) :
    Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) ≤
      retuneCube w :=
  Q'.divPos_le_of_le_mul _ _ _ (four_anchor_retune_all_cutoffs hw0 hwc N)

theorem four_anchor_lamPW_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ fourAnchorCap) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _ (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (four_anchor_ratio_all_cutoffs hw0 hwc N)

theorem harmW_five_mem_window : harmW 5 ≤ fourAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit fourAnchorCap
  decide

theorem harmonicMass_k5_retune_floor :
    (1 : Q') - retuneCube (harmW 5) ≤ harmonicMass 5 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (four_anchor_lamPW_le_retune
      (harmW_nonneg 5) harmW_five_mem_window (Ncut 5)))

theorem initial_six_retune {k : Nat} (hk : k ≤ 5) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact initial_five_retune (by decide)
  · exact initial_five_retune (by decide)
  · exact initial_five_retune (by decide)
  · exact initial_five_retune (by decide)
  · exact initial_five_retune (by decide)
  · exact four_anchor_retune_all_cutoffs
      (harmW_nonneg 5) harmW_five_mem_window (Ncut 5)

theorem harmonicSchur_spacing_k5 :
    harmonicSchurAll 5 * harmonicSpacing 6 ≤
      harmonicMass 6 * harmonicSpacing 5 := by
  decide

theorem harmonicSchur_spacing_initial_six {k : Nat} (hk : k ≤ 5) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact harmonicSchur_spacing_initial_five (by decide)
  · exact harmonicSchur_spacing_initial_five (by decide)
  · exact harmonicSchur_spacing_initial_five (by decide)
  · exact harmonicSchur_spacing_initial_five (by decide)
  · exact harmonicSchur_spacing_initial_five (by decide)
  · exact harmonicSchur_spacing_k5

theorem harmonic_operator_spacing_k5 :
    harmonicHead 5 * harmonicSpacing 6 ≤
      (harmonicErosionAll 5 + harmonicMass 6) * harmonicSpacing 5 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 5)
    (harmonicErosionAll_nonneg 5)
    (Q'.le_of_lt (harmonicSpacing_pos 6))
    (harmonicSpacing_contracts 5)
    (harmonicCoupling_size_all 5)
    harmonicSchur_spacing_k5

theorem harmonic_operator_spacing_initial_six {k : Nat} (hk : k ≤ 5) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_six hk)

end YMGap.Continuum.FourAnchorWindowRetune

#print axioms YMGap.Continuum.FourAnchorWindowRetune.strengthened_four_anchor_head
#print axioms YMGap.Continuum.FourAnchorWindowRetune.one_edge_head
#print axioms YMGap.Continuum.FourAnchorWindowRetune.two_edge_head
#print axioms YMGap.Continuum.FourAnchorWindowRetune.tailRatio4_le_retune
#print axioms YMGap.Continuum.FourAnchorWindowRetune.coeffW_four_eq_tailRatio4_mul_three
#print axioms YMGap.Continuum.FourAnchorWindowRetune.adjacent_tail4_le
#print axioms YMGap.Continuum.FourAnchorWindowRetune.four_anchor_retune_all_cutoffs
#print axioms YMGap.Continuum.FourAnchorWindowRetune.four_anchor_ratio_all_cutoffs
#print axioms YMGap.Continuum.FourAnchorWindowRetune.four_anchor_lamPW_le_retune
#print axioms YMGap.Continuum.FourAnchorWindowRetune.harmonicMass_k5_retune_floor
#print axioms YMGap.Continuum.FourAnchorWindowRetune.initial_six_retune
#print axioms YMGap.Continuum.FourAnchorWindowRetune.harmonicSchur_spacing_k5
#print axioms YMGap.Continuum.FourAnchorWindowRetune.harmonicSchur_spacing_initial_six
#print axioms YMGap.Continuum.FourAnchorWindowRetune.harmonic_operator_spacing_k5
#print axioms YMGap.Continuum.FourAnchorWindowRetune.harmonic_operator_spacing_initial_six
