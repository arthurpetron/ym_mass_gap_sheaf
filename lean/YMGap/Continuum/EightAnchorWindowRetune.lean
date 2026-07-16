/-
Exact eight-anchor correlation window through `w = 21/22`.

The strengthened head uses eight adjacent edges against the first eight
diagonal coordinates.  The unused `c_8^2` starts a symbolic PF2 tail from
the exact ratio `c_8/c_7 = (9/8)w^17`.

Unlike the earlier anchor modules, the Bernstein coefficients are generated
inside Lean from the polynomial coefficients and checked by closed rational
computation.  This avoids a large handwritten certificate table while
retaining a kernel-checked polynomial identity and coefficient sign audit.
-/

import YMGap.Continuum.SevenAnchorWindowRetune

namespace YMGap.Continuum.EightAnchorWindowRetune

set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

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
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SevenAnchorWindowRetune
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

def eightAnchorCap : Q' := Q'.mkPos 21 22 (by decide)
private def capInv : Q' := Q'.mkPos 22 21 (by decide)
private def nineEighths : Q' := Q'.mkPos 9 8 (by decide)

def tailRatio8 (w : Q') : Q' := nineEighths * qpow w 17

private def headSlack8P : Poly :=
  psub (pmul retuneP (prefixDP 7)) (prefixAP 8)
private def short1SlackP : Poly := psub (pmul retuneP (prefixDP 1)) (prefixAP 1)
private def short2SlackP : Poly := psub (pmul retuneP (prefixDP 2)) (prefixAP 2)
private def short3SlackP : Poly := psub (pmul retuneP (prefixDP 3)) (prefixAP 3)
private def short4SlackP : Poly := psub (pmul retuneP (prefixDP 4)) (prefixAP 4)
private def short5SlackP : Poly := psub (pmul retuneP (prefixDP 5)) (prefixAP 5)
private def short6SlackP : Poly := psub (pmul retuneP (prefixDP 6)) (prefixAP 6)
private def ratio8P : Poly := monoP nineEighths 17
private def ratioSlack8P : Poly := psub retuneP ratio8P

/-! ## Exact generated Bernstein certificates -/

private def chooseFast (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => chooseFast n k * (n - k) / (k + 1)

private def qsum : List Q' → Q'
  | [] => 0
  | x :: xs => x + qsum xs

private def generatedBernCoeff
    (cap : Q') (p : Poly) (degree i : Nat) : Q' :=
  qsum ((List.range (i + 1)).map (fun j =>
    Q'.ofNat (chooseFast (degree - j) (i - j)) *
      ((p.getD j 0) * qpow cap j)))

private def generatedBernTerms
    (cap : Q') (p : Poly) (degree : Nat) : List (Nat × Q') :=
  (List.range (degree + 1)).map
    (fun i => (i, generatedBernCoeff cap p degree i))

private def head8Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap headSlack8P 143
private def short1Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short1SlackP 10
private def short2Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short2SlackP 20
private def short3Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short3SlackP 35
private def short4Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short4SlackP 54
private def short5Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short5SlackP 74
private def short6Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap short6SlackP 99
private def ratio8Bern : List (Nat × Q') :=
  generatedBernTerms eightAnchorCap ratioSlack8P 17

private theorem head8_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap headSlack8P)
      (bernTermsP 143 head8Bern)) := by decide
private theorem head8_bernstein_nonnegative :
    ∀ t ∈ head8Bern, (0 : Q') ≤ t.2 := by decide
private theorem short1_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short1SlackP)
      (bernTermsP 10 short1Bern)) := by decide
private theorem short1_bernstein_nonnegative :
    ∀ t ∈ short1Bern, (0 : Q') ≤ t.2 := by decide
private theorem short2_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short2SlackP)
      (bernTermsP 20 short2Bern)) := by decide
private theorem short2_bernstein_nonnegative :
    ∀ t ∈ short2Bern, (0 : Q') ≤ t.2 := by decide
private theorem short3_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short3SlackP)
      (bernTermsP 35 short3Bern)) := by decide
private theorem short3_bernstein_nonnegative :
    ∀ t ∈ short3Bern, (0 : Q') ≤ t.2 := by decide
private theorem short4_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short4SlackP)
      (bernTermsP 54 short4Bern)) := by decide
private theorem short4_bernstein_nonnegative :
    ∀ t ∈ short4Bern, (0 : Q') ≤ t.2 := by decide
private theorem short5_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short5SlackP)
      (bernTermsP 74 short5Bern)) := by decide
private theorem short5_bernstein_nonnegative :
    ∀ t ∈ short5Bern, (0 : Q') ≤ t.2 := by decide
private theorem short6_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap short6SlackP)
      (bernTermsP 99 short6Bern)) := by decide
private theorem short6_bernstein_nonnegative :
    ∀ t ∈ short6Bern, (0 : Q') ≤ t.2 := by decide
private theorem ratio8_bernstein_identity :
    allZero (psub (scaleVar eightAnchorCap ratioSlack8P)
      (bernTermsP 17 ratio8Bern)) := by decide
private theorem ratio8_bernstein_nonnegative :
    ∀ t ∈ ratio8Bern, (0 : Q') ≤ t.2 := by decide

private theorem scaled_bernstein_nonneg
    (p : Poly) (degree : Nat) (terms : List (Nat × Q'))
    (hrep : allZero (psub (scaleVar eightAnchorCap p) (bernTermsP degree terms)))
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    (0 : Q') ≤ eval p w := by
  let x := capInv * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ (by decide) hw0
  have hx1 : x ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ capInv hwc (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hb : (0 : Q') ≤ eval (bernTermsP degree terms) x :=
    eval_bernTermsP_nonneg hx0 hx1 degree terms hnn
  have hs : (0 : Q') ≤ eval (scaleVar eightAnchorCap p) x :=
    Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv (poly_eqv _ _ x hrep))
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (eval_scaleVar eightAnchorCap x p) ?_
  apply eval_eqv_arg
  unfold x
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w (by decide : eightAnchorCap * capInv ≈ 1)) ?_
  exact Q'.one_mul_eqv w

/-! ## Head and symbolic tail -/

theorem strengthened_eight_anchor_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 8 ≤ retuneCube w * coordNormSq w 7 := by
  apply slack_nonneg_to_bound w (adjCorr w 8) (coordNormSq w 7)
    (prefixAP 8) (prefixDP 7) headSlack8P
    (prefixA_eval w 8) (prefixD_eval w 7) rfl
  exact scaled_bernstein_nonneg headSlack8P 143 head8Bern
    head8_bernstein_identity head8_bernstein_nonnegative hw0 hwc

theorem short_one_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 1 ≤ retuneCube w * coordNormSq w 1 := by
  apply slack_nonneg_to_bound w (adjCorr w 1) (coordNormSq w 1)
    (prefixAP 1) (prefixDP 1) short1SlackP
    (prefixA_eval w 1) (prefixD_eval w 1) rfl
  exact scaled_bernstein_nonneg short1SlackP 10 short1Bern
    short1_bernstein_identity short1_bernstein_nonnegative hw0 hwc

theorem short_two_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 2 ≤ retuneCube w * coordNormSq w 2 := by
  apply slack_nonneg_to_bound w (adjCorr w 2) (coordNormSq w 2)
    (prefixAP 2) (prefixDP 2) short2SlackP
    (prefixA_eval w 2) (prefixD_eval w 2) rfl
  exact scaled_bernstein_nonneg short2SlackP 20 short2Bern
    short2_bernstein_identity short2_bernstein_nonnegative hw0 hwc

theorem short_three_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 3 ≤ retuneCube w * coordNormSq w 3 := by
  apply slack_nonneg_to_bound w (adjCorr w 3) (coordNormSq w 3)
    (prefixAP 3) (prefixDP 3) short3SlackP
    (prefixA_eval w 3) (prefixD_eval w 3) rfl
  exact scaled_bernstein_nonneg short3SlackP 35 short3Bern
    short3_bernstein_identity short3_bernstein_nonnegative hw0 hwc

theorem short_four_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 4 ≤ retuneCube w * coordNormSq w 4 := by
  apply slack_nonneg_to_bound w (adjCorr w 4) (coordNormSq w 4)
    (prefixAP 4) (prefixDP 4) short4SlackP
    (prefixA_eval w 4) (prefixD_eval w 4) rfl
  exact scaled_bernstein_nonneg short4SlackP 54 short4Bern
    short4_bernstein_identity short4_bernstein_nonnegative hw0 hwc

theorem short_five_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 5 ≤ retuneCube w * coordNormSq w 5 := by
  apply slack_nonneg_to_bound w (adjCorr w 5) (coordNormSq w 5)
    (prefixAP 5) (prefixDP 5) short5SlackP
    (prefixA_eval w 5) (prefixD_eval w 5) rfl
  exact scaled_bernstein_nonneg short5SlackP 74 short5Bern
    short5_bernstein_identity short5_bernstein_nonnegative hw0 hwc

theorem short_six_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    adjCorr w 6 ≤ retuneCube w * coordNormSq w 6 := by
  apply slack_nonneg_to_bound w (adjCorr w 6) (coordNormSq w 6)
    (prefixAP 6) (prefixDP 6) short6SlackP
    (prefixA_eval w 6) (prefixD_eval w 6) rfl
  exact scaled_bernstein_nonneg short6SlackP 99 short6Bern
    short6_bernstein_identity short6_bernstein_nonnegative hw0 hwc

theorem tailRatio8_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) :
    tailRatio8 w ≤ retuneCube w := by
  have hs := scaled_bernstein_nonneg ratioSlack8P 17 ratio8Bern
    ratio8_bernstein_identity ratio8_bernstein_nonnegative hw0 hwc
  have hq : tailRatio8 w ≈ eval ratio8P w := by
    unfold tailRatio8 ratio8P
    exact Q'.eqv_symm (eval_monoP nineEighths w 17)
  have he : eval ratioSlack8P w ≈ retuneCube w + -(tailRatio8 w) := by
    refine Q'.eqv_trans _ _ _ (eval_psub _ _ w) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_symm (retune_eval w))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hq))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he))

theorem coeffW_eight_eq_tailRatio8_mul_seven (w : Q') :
    coeffW w 8 ≈ tailRatio8 w * coeffW w 7 := by
  have hc8 := hcoeff w 8
  have hq : tailRatio8 w ≈ eval ratio8P w := by
    unfold tailRatio8 ratio8P
    exact Q'.eqv_symm (eval_monoP nineEighths w 17)
  have hc7 := hcoeff w 7
  refine Q'.eqv_trans _ _ _ hc8 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 8) (pmul ratio8P (coeffPoly 7)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc7)

theorem adjacent_tail8_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a : Nat} (ha : 7 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio8 w * (coeffW w a * coeffW w a) := by
  by_cases h7 : a = 7
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 7) _ _
        (coeffW_eight_eq_tailRatio8_mul_seven w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha8 : 7 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 7) (N := a) ha8
    have hr : coeffW w (a + 1) * coeffW w 7 ≤ coeffW w a * coeffW w 8 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc7p := FusionResidualBound.coeffW_pos hwp 7
    have hR : coeffW w 8 * (coeffW w a * coeffW w a) ≈
        coeffW w 7 * (tailRatio8 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coeffW_eight_eq_tailRatio8_mul_seven w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 7 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 7 * (tailRatio8 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc7p

private def edgeTail (w : Q') (j : Nat) : Q' :=
  coeffW w (8 + j) * coeffW w (8 + j + 1)
private def squareTail (w : Q') (j : Nat) : Q' :=
  coeffW w (8 + j) * coeffW w (8 + j)

private theorem tail_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hwc : w ≤ eightAnchorCap) (M : Nat) :
    fsum (edgeTail w) M ≤ retuneCube w * fsum (squareTail w) M := by
  have hterm : ∀ j, edgeTail w j ≤ retuneCube w * squareTail w j := by
    intro j
    have ht := adjacent_tail8_le hw0 hw1 hwp (a := 8 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (tailRatio8_le_retune hw0 hwc)
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (8 + j)) (coeffW_nonneg hw0 (8 + j))))
  have hsum : fsum (edgeTail w) M ≤
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : retuneCube w * fsum (squareTail w) M ≈
      fsum (fun j => retuneCube w * squareTail w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail w) (retuneCube w) M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-! ## Uniformity in the Peter--Weyl cutoff -/

theorem eight_anchor_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) (N : Nat) :
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
    rcases Nat.le_total N 8 with hsmall | hlarge
    · have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨
          N = 6 ∨ N = 7 ∨ N = 8 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Q'.mul_nonneg _ _
          (qpow_nonneg _
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.zero_le_add _ _ (by decide) hw0)) 3)
          (coordNormSq_nonneg hw0 0)
      · exact short_one_head hw0 hwc
      · exact short_two_head hw0 hwc
      · exact short_three_head hw0 hwc
      · exact short_four_head hw0 hwc
      · exact short_five_head hw0 hwc
      · exact short_six_head hw0 hwc
      · have hA78 : adjCorr w 7 ≤ adjCorr w 8 := by
          unfold adjCorr
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (i + 1))) (by omega)
        exact Q'.le_trans' _ _ _ hA78 (strengthened_eight_anchor_head hw0 hwc)
      · have hD78 : coordNormSq w 7 ≤ coordNormSq w 8 := by
          unfold coordNormSq
          exact AFRateCalibration.fsum_le_of_le
            (fun i => Q'.mul_nonneg _ _
              (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)) (by omega)
        have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.zero_le_add _ _ (by decide) hw0)) 3
        exact Q'.le_trans' _ _ _ (strengthened_eight_anchor_head hw0 hwc)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hD78 hr0)
    · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
      have hA : adjCorr w (8 + M) ≈ adjCorr w 8 + fsum (edgeTail w) M := by
        unfold adjCorr edgeTail
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w (a + 1)) 8 M
      have hD : coordNormSq w (8 + M) ≈
          coordNormSq w 7 + fsum (squareTail w) (M + 1) := by
        unfold coordNormSq squareTail
        rw [show 8 + M + 1 = 8 + (M + 1) by omega]
        exact FusionCoreStepRoundH.fsum_split_at
          (fun a => coeffW w a * coeffW w a) 8 (M + 1)
      have hsquare0 : ∀ j, (0 : Q') ≤ squareTail w j := by
        intro j
        unfold squareTail
        exact Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (8 + j)) (coeffW_nonneg hw0 (8 + j))
      have htailPrefix : fsum (squareTail w) M ≤ fsum (squareTail w) (M + 1) :=
        AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
      have hprefix : coordNormSq w 7 + fsum (squareTail w) M ≤
          coordNormSq w (8 + M) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_left (coordNormSq w 7) _ _ htailPrefix)
          (Q'.ge_of_eqv hD)
      have hr0 : (0 : Q') ≤ retuneCube w := qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) hw0)) 3
      have hpaid : adjCorr w 8 + fsum (edgeTail w) M ≤
          retuneCube w * coordNormSq w 7 +
            retuneCube w * fsum (squareTail w) M :=
        AFRateCalibration.q_add_le_add
          (strengthened_eight_anchor_head hw0 hwc)
          (tail_sum_le hw0 hw1 hwp hwc M)
      have hcollect : retuneCube w * coordNormSq w 7 +
          retuneCube w * fsum (squareTail w) M ≈
          retuneCube w * (coordNormSq w 7 + fsum (squareTail w) M) :=
        Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
        (Q'.le_trans' _ _ _ hpaid
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

theorem eight_anchor_ratio_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) (N : Nat) :
    Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) ≤
      retuneCube w :=
  Q'.divPos_le_of_le_mul _ _ _ (eight_anchor_retune_all_cutoffs hw0 hwc N)

theorem eight_anchor_lamPW_le_retune {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwc : w ≤ eightAnchorCap) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwc (by decide)
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N) (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _ (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (eight_anchor_ratio_all_cutoffs hw0 hwc N)

/-! ## Harmonic prefix and growing-anchor record -/

theorem harmW_seventeen_mem_window : harmW 17 ≤ eightAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit eightAnchorCap
  decide
theorem harmW_eighteen_mem_window : harmW 18 ≤ eightAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit eightAnchorCap
  decide
theorem harmW_nineteen_mem_window : harmW 19 ≤ eightAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit eightAnchorCap
  decide
theorem harmW_twenty_mem_window : harmW 20 ≤ eightAnchorCap := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit eightAnchorCap
  decide

theorem harmonicMass_k17_retune_floor :
    (1 : Q') - retuneCube (harmW 17) ≤ harmonicMass 17 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg
    (eight_anchor_lamPW_le_retune (harmW_nonneg 17) harmW_seventeen_mem_window (Ncut 17)))
theorem harmonicMass_k18_retune_floor :
    (1 : Q') - retuneCube (harmW 18) ≤ harmonicMass 18 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg
    (eight_anchor_lamPW_le_retune (harmW_nonneg 18) harmW_eighteen_mem_window (Ncut 18)))
theorem harmonicMass_k19_retune_floor :
    (1 : Q') - retuneCube (harmW 19) ≤ harmonicMass 19 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg
    (eight_anchor_lamPW_le_retune (harmW_nonneg 19) harmW_nineteen_mem_window (Ncut 19)))
theorem harmonicMass_k20_retune_floor :
    (1 : Q') - retuneCube (harmW 20) ≤ harmonicMass 20 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg
    (eight_anchor_lamPW_le_retune (harmW_nonneg 20) harmW_twenty_mem_window (Ncut 20)))

theorem initial_twenty_one_retune {k : Nat} (hk : k ≤ 20) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  by_cases hk16 : k ≤ 16
  · exact SevenAnchorWindowRetune.initial_seventeen_retune hk16
  · have cases : k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact eight_anchor_retune_all_cutoffs
        (harmW_nonneg 17) harmW_seventeen_mem_window (Ncut 17)
    · exact eight_anchor_retune_all_cutoffs
        (harmW_nonneg 18) harmW_eighteen_mem_window (Ncut 18)
    · exact eight_anchor_retune_all_cutoffs
        (harmW_nonneg 19) harmW_nineteen_mem_window (Ncut 19)
    · exact eight_anchor_retune_all_cutoffs
        (harmW_nonneg 20) harmW_twenty_mem_window (Ncut 20)

def certifiedAnchorPattern : List (Nat × Nat × Nat × Nat) :=
  SevenAnchorWindowRetune.certifiedAnchorPattern ++ [(8, 143, 21, 22)]

theorem eight_native_head_degree_formula :
    2 * 8 * 8 + 2 * 8 - 1 = 143 := by decide

theorem eight_anchor_ratio_exponent_formula : 2 * 8 + 1 = 17 := by decide

end YMGap.Continuum.EightAnchorWindowRetune

#print axioms YMGap.Continuum.EightAnchorWindowRetune.strengthened_eight_anchor_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_one_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_two_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_three_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_four_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_five_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.short_six_head
#print axioms YMGap.Continuum.EightAnchorWindowRetune.tailRatio8_le_retune
#print axioms YMGap.Continuum.EightAnchorWindowRetune.coeffW_eight_eq_tailRatio8_mul_seven
#print axioms YMGap.Continuum.EightAnchorWindowRetune.adjacent_tail8_le
#print axioms YMGap.Continuum.EightAnchorWindowRetune.eight_anchor_retune_all_cutoffs
#print axioms YMGap.Continuum.EightAnchorWindowRetune.eight_anchor_ratio_all_cutoffs
#print axioms YMGap.Continuum.EightAnchorWindowRetune.eight_anchor_lamPW_le_retune
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmW_seventeen_mem_window
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmW_eighteen_mem_window
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmW_nineteen_mem_window
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmW_twenty_mem_window
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmonicMass_k17_retune_floor
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmonicMass_k18_retune_floor
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmonicMass_k19_retune_floor
#print axioms YMGap.Continuum.EightAnchorWindowRetune.harmonicMass_k20_retune_floor
#print axioms YMGap.Continuum.EightAnchorWindowRetune.initial_twenty_one_retune
#print axioms YMGap.Continuum.EightAnchorWindowRetune.eight_native_head_degree_formula
#print axioms YMGap.Continuum.EightAnchorWindowRetune.eight_anchor_ratio_exponent_formula
