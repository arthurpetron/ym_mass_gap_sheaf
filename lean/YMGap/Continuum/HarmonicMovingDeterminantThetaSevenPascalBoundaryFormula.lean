/-
Exact formulas for the first seven coefficients of the seven-unit theta gap.

The minimal Bernstein row is written in deficit order.  A common factor
`5670` clears every denominator in deficits zero through six.  The one-scale
Pascal recurrence is then verified simultaneously after a further clearing by
`720 = 6!`; the remaining statement is a kernel-decided integer polynomial
identity.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaCertificates

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.ThetaResidualPascalTelescope

private theorem cases_le_six {r : Nat} (hr : r ≤ 6) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by
  omega

private theorem int_add_congr {a b c d : Int} (hab : a = b) (hcd : c = d) :
    a + c = b + d := by
  rw [hab, hcd]

private theorem cell_split_algebra (m a x y z w t : Int) :
    7 * m * m * a - m * m * (x + 3 * y + 3 * z + w) +
        8 * m * (m + 1) * t =
      7 * (m * (m * a)) + 8 * (m * ((m + 1) * t)) +
        (-(m * (m * (x + 3 * y))) + -(m * (m * (3 * z + w)))) := by
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_add]
  ac_rfl

private theorem cell_individual_split_algebra (m a x y z w t : Int) :
    7 * m * m * a - m * m * (x + 3 * y + 3 * z + w) +
        8 * m * (m + 1) * t =
      7 * (m * (m * a)) + 8 * (m * ((m + 1) * t)) +
        ((-(m * (m * x)) + -(m * (m * (3 * y)))) +
          (-(m * (m * (3 * z))) + -(m * (m * w)))) := by
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_add]
  ac_rfl

private theorem cases_le_three {r : Nat} (hr : r ≤ 3) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega

private theorem pStep_normal (r : Nat) (hr : r ≤ 3) :
    RingNormaliser.normalize (pStep pv r) =
      RingNormaliser.normalize
        (pm (pc 720) (pFormula r (pa pv (pc 1)))) := by
  rcases cases_le_three hr with h | h | h | h <;>
    subst r
  · exact pStep_zero_normal
  · exact pStep_one_normal
  · exact pStep_two_normal
  · exact pStep_three_normal

private theorem horner_eval_congr (rho : Nat → Int) (x : PE) (a : Int)
    {u v : PE} (h : IntRingNormaliser.eval rho u =
      IntRingNormaliser.eval rho v) :
    IntRingNormaliser.eval rho (pa (pc a) (pm x u)) =
      IntRingNormaliser.eval rho (pa (pc a) (pm x v)) := by
  simp only [pa, pc, pm, IntRingNormaliser.eval]
  rw [h]

private theorem pIntPoly_eval_congr (rho : Nat → Int) {x y : PE}
    (hxy : IntRingNormaliser.eval rho x = IntRingNormaliser.eval rho y) :
    ∀ as : List Int,
      IntRingNormaliser.eval rho (pIntPoly x as) =
        IntRingNormaliser.eval rho (pIntPoly y as)
  | [] => rfl
  | a :: as => by
      simp only [pIntPoly, pa, pc, pm, IntRingNormaliser.eval]
      rw [hxy, pIntPoly_eval_congr rho hxy as]

private theorem pChoose_six_LL_eval (m : Int) :
    IntRingNormaliser.eval (fun _ => m)
        (pChoose720 (pa (pa (pm (pc 4) pv) (pc 2)) (pc 3)) 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096]) := by
  let rho : Nat → Int := fun _ => m
  let x : PE := pa (pm (pc 4) pv) (pc 5)
  have h0 : IntRingNormaliser.eval rho (pIntPoly x [1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [1]) := by
    simp [rho, x, pIntPoly, pc, pv, pa, pm, IntRingNormaliser.eval]
  have h1c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-15)) (pm x (pIntPoly pv [1])))
    (pIntPoly pv [-10, 4]) pChoose_six_LL_step1_normal rho
  have h1 : IntRingNormaliser.eval rho (pIntPoly x [-15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-10, 4]) :=
    (horner_eval_congr rho x (-15) h0).trans h1c
  have h2c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 85) (pm x (pIntPoly pv [-10, 4])))
    (pIntPoly pv [35, -20, 16]) pChoose_six_LL_step2_normal rho
  have h2 : IntRingNormaliser.eval rho (pIntPoly x [85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [35, -20, 16]) :=
    (horner_eval_congr rho x 85 h1).trans h2c
  have h3c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-225)) (pm x (pIntPoly pv [35, -20, 16])))
    (pIntPoly pv [-50, 40, 0, 64]) pChoose_six_LL_step3_normal rho
  have h3 : IntRingNormaliser.eval rho
        (pIntPoly x [-225, 85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-50, 40, 0, 64]) :=
    (horner_eval_congr rho x (-225) h2).trans h3c
  have h4c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 274) (pm x (pIntPoly pv [-50, 40, 0, 64])))
    (pIntPoly pv [24, 0, 160, 320, 256])
    pChoose_six_LL_step4_normal rho
  have h4 : IntRingNormaliser.eval rho
        (pIntPoly x [274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [24, 0, 160, 320, 256]) :=
    (horner_eval_congr rho x 274 h3).trans h4c
  have h5c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-120))
      (pm x (pIntPoly pv [24, 0, 160, 320, 256])))
    (pIntPoly pv [0, 96, 800, 2240, 2560, 1024])
    pChoose_six_LL_step5_normal rho
  have h5 : IntRingNormaliser.eval rho
        (pIntPoly x [-120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, 96, 800, 2240, 2560, 1024]) :=
    (horner_eval_congr rho x (-120) h4).trans h5c
  have h6c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 0)
      (pm x (pIntPoly pv [0, 96, 800, 2240, 2560, 1024])))
    (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096])
    pChoose_six_LL_step6_normal rho
  have h6 : IntRingNormaliser.eval rho
        (pIntPoly x [0, -120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096]) :=
    (horner_eval_congr rho x 0 h5).trans h6c
  have hx : IntRingNormaliser.eval rho
        (pa (pa (pm (pc 4) pv) (pc 2)) (pc 3)) =
      IntRingNormaliser.eval rho x := by
    simp [rho, x, pc, pv, pa, pm, IntRingNormaliser.eval]
    omega
  change IntRingNormaliser.eval rho
      (pIntPoly (pa (pa (pm (pc 4) pv) (pc 2)) (pc 3))
        [0, -120, 274, -225, 85, -15, 1]) = _
  exact (pIntPoly_eval_congr rho hx _).trans h6

private theorem pChoose_six_LR_eval (m : Int) :
    IntRingNormaliser.eval (fun _ => m)
        (pChoose720 (pa (pa (pm (pc 4) pv) (pc 2)) (pc 2)) 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096]) := by
  let rho : Nat → Int := fun _ => m
  let x : PE := pa (pm (pc 4) pv) (pc 4)
  have h0 : IntRingNormaliser.eval rho (pIntPoly x [1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [1]) := by
    simp [rho, x, pIntPoly, pc, pv, pa, pm, IntRingNormaliser.eval]
  have h1c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-15)) (pm x (pIntPoly pv [1])))
    (pIntPoly pv [-11, 4]) pChoose_six_LR_step1_normal rho
  have h1 : IntRingNormaliser.eval rho (pIntPoly x [-15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-11, 4]) :=
    (horner_eval_congr rho x (-15) h0).trans h1c
  have h2c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 85) (pm x (pIntPoly pv [-11, 4])))
    (pIntPoly pv [41, -28, 16]) pChoose_six_LR_step2_normal rho
  have h2 : IntRingNormaliser.eval rho (pIntPoly x [85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [41, -28, 16]) :=
    (horner_eval_congr rho x 85 h1).trans h2c
  have h3c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-225)) (pm x (pIntPoly pv [41, -28, 16])))
    (pIntPoly pv [-61, 52, -48, 64]) pChoose_six_LR_step3_normal rho
  have h3 : IntRingNormaliser.eval rho
        (pIntPoly x [-225, 85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-61, 52, -48, 64]) :=
    (horner_eval_congr rho x (-225) h2).trans h3c
  have h4c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 274) (pm x (pIntPoly pv [-61, 52, -48, 64])))
    (pIntPoly pv [30, -36, 16, 64, 256])
    pChoose_six_LR_step4_normal rho
  have h4 : IntRingNormaliser.eval rho
        (pIntPoly x [274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [30, -36, 16, 64, 256]) :=
    (horner_eval_congr rho x 274 h3).trans h4c
  have h5c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-120))
      (pm x (pIntPoly pv [30, -36, 16, 64, 256])))
    (pIntPoly pv [0, -24, -80, 320, 1280, 1024])
    pChoose_six_LR_step5_normal rho
  have h5 : IntRingNormaliser.eval rho
        (pIntPoly x [-120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, -24, -80, 320, 1280, 1024]) :=
    (horner_eval_congr rho x (-120) h4).trans h5c
  have h6c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 0)
      (pm x (pIntPoly pv [0, -24, -80, 320, 1280, 1024])))
    (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096])
    pChoose_six_LR_step6_normal rho
  have h6 : IntRingNormaliser.eval rho
        (pIntPoly x [0, -120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096]) :=
    (horner_eval_congr rho x 0 h5).trans h6c
  have hx : IntRingNormaliser.eval rho
        (pa (pa (pm (pc 4) pv) (pc 2)) (pc 2)) =
      IntRingNormaliser.eval rho x := by
    simp [rho, x, pc, pv, pa, pm, IntRingNormaliser.eval]
    omega
  change IntRingNormaliser.eval rho
      (pIntPoly (pa (pa (pm (pc 4) pv) (pc 2)) (pc 2))
        [0, -120, 274, -225, 85, -15, 1]) = _
  exact (pIntPoly_eval_congr rho hx _).trans h6

private theorem pChoose_six_RL_eval (m : Int) :
    IntRingNormaliser.eval (fun _ => m)
        (pChoose720 (pa (pa (pm (pc 4) pv) (pc 2)) (pc 1)) 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096]) := by
  let rho : Nat → Int := fun _ => m
  let x : PE := pa (pm (pc 4) pv) (pc 3)
  have h0 : IntRingNormaliser.eval rho (pIntPoly x [1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [1]) := by
    simp [rho, x, pIntPoly, pc, pv, pa, pm, IntRingNormaliser.eval]
  have h1c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-15)) (pm x (pIntPoly pv [1])))
    (pIntPoly pv [-12, 4]) pChoose_six_RL_step1_normal rho
  have h1 : IntRingNormaliser.eval rho (pIntPoly x [-15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-12, 4]) :=
    (horner_eval_congr rho x (-15) h0).trans h1c
  have h2c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 85) (pm x (pIntPoly pv [-12, 4])))
    (pIntPoly pv [49, -36, 16]) pChoose_six_RL_step2_normal rho
  have h2 : IntRingNormaliser.eval rho (pIntPoly x [85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [49, -36, 16]) :=
    (horner_eval_congr rho x 85 h1).trans h2c
  have h3c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-225)) (pm x (pIntPoly pv [49, -36, 16])))
    (pIntPoly pv [-78, 88, -96, 64]) pChoose_six_RL_step3_normal rho
  have h3 : IntRingNormaliser.eval rho
        (pIntPoly x [-225, 85, -15, 1]) =
      IntRingNormaliser.eval rho (pIntPoly pv [-78, 88, -96, 64]) :=
    (horner_eval_congr rho x (-225) h2).trans h3c
  have h4c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 274) (pm x (pIntPoly pv [-78, 88, -96, 64])))
    (pIntPoly pv [40, -48, 64, -192, 256])
    pChoose_six_RL_step4_normal rho
  have h4 : IntRingNormaliser.eval rho
        (pIntPoly x [274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [40, -48, 64, -192, 256]) :=
    (horner_eval_congr rho x 274 h3).trans h4c
  have h5c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc (-120))
      (pm x (pIntPoly pv [40, -48, 64, -192, 256])))
    (pIntPoly pv [0, 16, 0, -320, 0, 1024])
    pChoose_six_RL_step5_normal rho
  have h5 : IntRingNormaliser.eval rho
        (pIntPoly x [-120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, 16, 0, -320, 0, 1024]) :=
    (horner_eval_congr rho x (-120) h4).trans h5c
  have h6c := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (pc 0)
      (pm x (pIntPoly pv [0, 16, 0, -320, 0, 1024])))
    (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096])
    pChoose_six_RL_step6_normal rho
  have h6 : IntRingNormaliser.eval rho
        (pIntPoly x [0, -120, 274, -225, 85, -15, 1]) =
      IntRingNormaliser.eval rho
        (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096]) :=
    (horner_eval_congr rho x 0 h5).trans h6c
  have hx : IntRingNormaliser.eval rho
        (pa (pa (pm (pc 4) pv) (pc 2)) (pc 1)) =
      IntRingNormaliser.eval rho x := by
    simp [rho, x, pc, pv, pa, pm, IntRingNormaliser.eval]
    omega
  change IntRingNormaliser.eval rho
      (pIntPoly (pa (pa (pm (pc 4) pv) (pc 2)) (pc 1))
        [0, -120, 274, -225, 85, -15, 1]) = _
  exact (pIntPoly_eval_congr rho hx _).trans h6

private theorem cleared_old_four_identity (m : Int) :
    clearedOldPrefix m 4 =
      intPolyEval m [0, -51438240, -300056400, -504176400, -24494400,
        553573440, 326592000] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldFourA pv)
    (pIntPoly pv [0, 0, -48988800, -288489600, -315705600,
      304819200, 348364800]) pOld_four_A_normal (fun _ => m)
  have hB := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldFourB pv)
    (pIntPoly pv [0, -51438240, -251067600, -215686800, 291211200,
      248754240, -21772800]) pOld_four_B_normal (fun _ => m)
  have hAB := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, -48988800, -288489600, -315705600,
        304819200, 348364800])
      (pIntPoly pv [0, -51438240, -251067600, -215686800, 291211200,
        248754240, -21772800]))
    (pIntPoly pv [0, -51438240, -300056400, -504176400, -24494400,
      553573440, 326592000]) pOld_four_expanded_normal (fun _ => m)
  simp [clearedOldPrefix, sevenBoundaryScaledFormula, choose720Poly,
    intPolyEval, pOldFourA, pOldFourB, pChoose720, pFormula, pIntPoly,
    pc, pv, pa, pm, IntRingNormaliser.eval] at hA hB hAB ⊢
  have h := (int_add_congr hA hB).trans hAB
  simpa only [Int.add_assoc, Int.mul_assoc] using h

private theorem cleared_cell_four_identity (m : Int) :
    clearedCell m 4 =
      intPolyEval m [0, 5760, 39120, 69600, -6720, -99840, -57600] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellA pv 4) (pIntPoly pv [0, 0, 15120, 50400, 40320])
    pCell_four_A_normal (fun _ => m)
  have hC := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellC pv 4)
    (pIntPoly pv [0, 5760, 29760, 57600, 52800, 23040, 3840])
    pCell_four_C_normal (fun _ => m)
  have hP := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 15120, 50400, 40320])
      (pIntPoly pv [0, 5760, 29760, 57600, 52800, 23040, 3840]))
    (pIntPoly pv [0, 5760, 44880, 108000, 93120, 23040, 3840])
    pCell_four_pos_expanded_normal (fun _ => m)
  have hL := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellNegLeft pv 4)
    (pIntPoly pv [0, 0, -5760, -36480, -84480, -84480, -30720])
    pCell_four_left_normal (fun _ => m)
  have hR := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellNegRight pv 4)
    (pIntPoly pv [0, 0, 0, -1920, -15360, -38400, -30720])
    pCell_four_right_normal (fun _ => m)
  have hE := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 5760, 44880, 108000, 93120, 23040, 3840])
      (pa
        (pIntPoly pv [0, 0, -5760, -36480, -84480, -84480, -30720])
        (pIntPoly pv [0, 0, 0, -1920, -15360, -38400, -30720])))
    (pIntPoly pv [0, 5760, 39120, 69600, -6720, -99840, -57600])
    pCell_four_expanded_normal (fun _ => m)
  have hsplit :
      clearedCell m 4 =
        IntRingNormaliser.eval (fun _ => m) (pCellA pv 4) +
          IntRingNormaliser.eval (fun _ => m) (pCellC pv 4) +
          (IntRingNormaliser.eval (fun _ => m) (pCellNegLeft pv 4) +
            IntRingNormaliser.eval (fun _ => m) (pCellNegRight pv 4)) := by
    simp [clearedCell, choose720Poly, pCellA, pCellC,
      pCellNegLeft, pCellNegRight, pChoose720, pIntPoly, intPolyEval,
      pc, pv, pa, pm, pn, IntRingNormaliser.eval]
    apply cell_split_algebra
  rw [hsplit]
  have hAC := (int_add_congr hA hC).trans hP
  have hLR := int_add_congr hL hR
  have h := (int_add_congr hAC hLR).trans hE
  simpa [intPolyEval, pIntPoly, pc, pv, pa, pm,
    IntRingNormaliser.eval] using h

private theorem cleared_step_four_identity (m : Int) :
    clearedStep m 4 = 720 * sevenBoundaryScaledFormula 4 (m + 1) := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, -51438240, -300056400, -504176400, -24494400,
        553573440, 326592000])
      (pm (pc 5670)
        (pIntPoly pv [0, 5760, 39120, 69600, -6720, -99840, -57600])))
    (pm (pc 720) (pFormula 4 (pa pv (pc 1))))
    pExpanded_four_step_normal (fun _ => m)
  rw [clearedStep, cleared_old_four_identity, cleared_cell_four_identity]
  simpa [sevenBoundaryScaledFormula, intPolyEval, pFormula, pIntPoly,
    pc, pv, pa, pm, IntRingNormaliser.eval] using h

private theorem cleared_old_five_identity (m : Int) :
    clearedOldPrefix m 5 =
      intPolyEval m [0, -18118080, -104963040, -299829600, -388281600,
        49351680, 489162240, 272678400] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldFiveA pv)
    (pIntPoly pv [0, 0, -31207680, -237323520, -508032000,
      -108864000, 571898880, 313528320]) pOld_five_A_normal (fun _ => m)
  have hB := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldFiveB pv)
    (pIntPoly pv [0, -18118080, -73755360, -62506080, 119750400,
      158215680, -82736640, -40849920]) pOld_five_B_normal (fun _ => m)
  have hAB := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, -31207680, -237323520, -508032000,
        -108864000, 571898880, 313528320])
      (pIntPoly pv [0, -18118080, -73755360, -62506080, 119750400,
        158215680, -82736640, -40849920]))
    (pIntPoly pv [0, -18118080, -104963040, -299829600, -388281600,
      49351680, 489162240, 272678400]) pOld_five_expanded_normal
      (fun _ => m)
  simp [clearedOldPrefix, sevenBoundaryScaledFormula, choose720Poly,
    intPolyEval, pOldFiveA, pOldFiveB, pChoose720, pFormula, pIntPoly,
    pc, pv, pa, pm, IntRingNormaliser.eval] at hA hB hAB ⊢
  have h := (int_add_congr hA hB).trans hAB
  simpa only [Int.add_assoc, Int.mul_assoc] using h

private theorem cleared_cell_five_identity (m : Int) :
    clearedCell m 5 =
      intPolyEval m [0, 0, 6624, 40896, 69120, -1920, -82944,
        -47616] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellA pv 5) (pIntPoly pv [0, 0, 5040, 36960, 80640, 53760])
    pCell_five_A_normal (fun _ => m)
  have hC := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellC pv 5)
    (pIntPoly pv [0, 0, 2304, 11904, 23040, 21120, 9216, 1536])
    pCell_five_C_normal (fun _ => m)
  have hP := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 5040, 36960, 80640, 53760])
      (pIntPoly pv [0, 0, 2304, 11904, 23040, 21120, 9216,
        1536]))
    (pIntPoly pv [0, 0, 7344, 48864, 103680, 74880, 9216, 1536])
    pCell_five_pos_expanded_normal (fun _ => m)
  have hL := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellNegLeft pv 5)
    (pIntPoly pv [0, 0, -720, -8304, -36000, -72960, -69120,
      -24576]) pCell_five_left_normal (fun _ => m)
  have hR := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellNegRight pv 5)
    (pIntPoly pv [0, 0, 0, 336, 1440, -3840, -23040, -24576])
    pCell_five_right_normal (fun _ => m)
  have hE := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 7344, 48864, 103680, 74880, 9216, 1536])
      (pa
        (pIntPoly pv [0, 0, -720, -8304, -36000, -72960, -69120,
          -24576])
        (pIntPoly pv [0, 0, 0, 336, 1440, -3840, -23040, -24576])))
    (pIntPoly pv [0, 0, 6624, 40896, 69120, -1920, -82944,
      -47616]) pCell_five_expanded_normal (fun _ => m)
  have hsplit :
      clearedCell m 5 =
        IntRingNormaliser.eval (fun _ => m) (pCellA pv 5) +
          IntRingNormaliser.eval (fun _ => m) (pCellC pv 5) +
          (IntRingNormaliser.eval (fun _ => m) (pCellNegLeft pv 5) +
            IntRingNormaliser.eval (fun _ => m) (pCellNegRight pv 5)) := by
    simp [clearedCell, choose720Poly, pCellA, pCellC,
      pCellNegLeft, pCellNegRight, pChoose720, pIntPoly, intPolyEval,
      pc, pv, pa, pm, pn, IntRingNormaliser.eval]
    apply cell_split_algebra
  rw [hsplit]
  have hAC := (int_add_congr hA hC).trans hP
  have hLR := int_add_congr hL hR
  have h := (int_add_congr hAC hLR).trans hE
  simpa [intPolyEval, pIntPoly, pc, pv, pa, pm,
    IntRingNormaliser.eval] using h

private theorem cleared_step_five_identity (m : Int) :
    clearedStep m 5 = 720 * sevenBoundaryScaledFormula 5 (m + 1) := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, -18118080, -104963040, -299829600, -388281600,
        49351680, 489162240, 272678400])
      (pm (pc 5670)
        (pIntPoly pv [0, 0, 6624, 40896, 69120, -1920, -82944,
          -47616])))
    (pm (pc 720) (pFormula 5 (pa pv (pc 1))))
    pExpanded_five_step_normal (fun _ => m)
  rw [clearedStep, cleared_old_five_identity, cleared_cell_five_identity]
  simpa [sevenBoundaryScaledFormula, intPolyEval, pFormula, pIntPoly,
    pc, pv, pa, pm, IntRingNormaliser.eval] using h

private theorem cleared_old_six_identity (m : Int) :
    clearedOldPrefix m 6 =
      intPolyEval m [0, -14605920, -38134800, -7986960, -69945120,
        -260880480, -70761600, 277119360, 184965120, 230400] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldSixA pv)
    (pIntPoly pv [0, 0, 6305040, 22725360, -89812800, -389188800,
      -191600640, 409328640, 232243200])
    pOld_six_A_normal (fun _ => m)
  have hB := IntRingNormaliser.poly_identity_of_normal_eq
    (pOldSixB pv)
    (pIntPoly pv [0, -14605920, -44439840, -30712320, 19867680,
      128308320, 120839040, -132209280, -47278080, 230400])
    pOld_six_B_normal (fun _ => m)
  have hAB := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 6305040, 22725360, -89812800, -389188800,
        -191600640, 409328640, 232243200])
      (pIntPoly pv [0, -14605920, -44439840, -30712320, 19867680,
        128308320, 120839040, -132209280, -47278080, 230400]))
    (pIntPoly pv [0, -14605920, -38134800, -7986960, -69945120,
      -260880480, -70761600, 277119360, 184965120, 230400])
    pOld_six_expanded_normal (fun _ => m)
  simp only [sevenBoundaryScaledFormula] at hA hB hAB ⊢
  simp [clearedOldPrefix, sevenBoundaryScaledFormula, choose720Poly,
    intPolyEval, pOldSixA, pOldSixB,
    pChoose720, pFormula, pIntPoly, pc, pv, pa, pm,
    IntRingNormaliser.eval] at hA hB hAB ⊢
  have h := (int_add_congr hA hB).trans hAB
  simpa only [Int.add_assoc, Int.mul_assoc] using h

private theorem cleared_cell_six_identity (m : Int) :
    clearedCell m 6 =
      intPolyEval m [0, 0, -384, 3536, 33696, 69440, 23424, -46336,
        -32256] := by
  have hA := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellA pv 6)
    (pIntPoly pv [0, 0, 0, 5040, 36960, 80640, 53760])
    pCell_six_A_normal (fun _ => m)
  have hC := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellC pv 6)
    (pIntPoly pv [0, 0, -384, -1216, 128, 4160, 5504, 2816, 512])
    pCell_six_C_normal (fun _ => m)
  have hP := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 0, 5040, 36960, 80640, 53760])
      (pIntPoly pv [0, 0, -384, -1216, 128, 4160, 5504, 2816,
        512]))
    (pIntPoly pv [0, 0, -384, 3824, 37088, 84800, 59264, 2816, 512])
    pCell_six_pos_expanded_normal (fun _ => m)
  have hLLc := pChoose_six_LL_eval m
  have hLLm : IntRingNormaliser.eval (fun _ => m) (pCellNegLL pv 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pn (pm pv (pm pv
          (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096])))) := by
    simpa [pCellNegLL, pc, pv, pa, pm, pn, IntRingNormaliser.eval] using
      congrArg (fun z : Int => -(m * (m * z))) hLLc
  have hLLp := IntRingNormaliser.poly_identity_of_normal_eq
    (pn (pm pv (pm pv
      (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096]))))
    (pIntPoly pv [0, 0, 0, -480, -4384, -14400, -21760, -15360,
      -4096]) pCell_six_LL_expanded_normal (fun _ => m)
  have hLL := hLLm.trans hLLp
  have hLRc := pChoose_six_LR_eval m
  have hLRm : IntRingNormaliser.eval (fun _ => m) (pCellNegLR pv 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pn (pm pv (pm pv (pm (pc 3)
          (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096]))))) := by
    simpa [pCellNegLR, pc, pv, pa, pm, pn, IntRingNormaliser.eval] using
      congrArg (fun z : Int => -(m * (m * (3 * z)))) hLRc
  have hLRp := IntRingNormaliser.poly_identity_of_normal_eq
    (pn (pm pv (pm pv (pm (pc 3)
      (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096])))))
    (pIntPoly pv [0, 0, 0, 288, 1248, -2880, -19200, -27648,
      -12288]) pCell_six_LR_expanded_normal (fun _ => m)
  have hLR := hLRm.trans hLRp
  have hRLc := pChoose_six_RL_eval m
  have hRLm : IntRingNormaliser.eval (fun _ => m) (pCellNegRL pv 6) =
      IntRingNormaliser.eval (fun _ => m)
        (pn (pm pv (pm pv (pm (pc 3)
          (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096]))))) := by
    simpa [pCellNegRL, pc, pv, pa, pm, pn, IntRingNormaliser.eval] using
      congrArg (fun z : Int => -(m * (m * (3 * z)))) hRLc
  have hRLp := IntRingNormaliser.poly_identity_of_normal_eq
    (pn (pm pv (pm pv (pm (pc 3)
      (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096])))))
    (pIntPoly pv [0, 0, 0, -144, -192, 2880, 3840, -9216,
      -12288]) pCell_six_RL_expanded_normal (fun _ => m)
  have hRL := hRLm.trans hRLp
  have hRR := IntRingNormaliser.poly_identity_of_normal_eq
    (pCellNegRR pv 6)
    (pIntPoly pv [0, 0, 0, 48, -64, -960, 1280, 3072, -4096])
    pCell_six_RR_normal (fun _ => m)
  have hL := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 0, -480, -4384, -14400, -21760, -15360,
        -4096])
      (pIntPoly pv [0, 0, 0, 288, 1248, -2880, -19200, -27648,
        -12288]))
    (pIntPoly pv [0, 0, 0, -192, -3136, -17280, -40960, -43008,
      -16384]) pCell_six_left_expanded_normal (fun _ => m)
  have hR := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, 0, -144, -192, 2880, 3840, -9216,
        -12288])
      (pIntPoly pv [0, 0, 0, 48, -64, -960, 1280, 3072, -4096]))
    (pIntPoly pv [0, 0, 0, -96, -256, 1920, 5120, -6144,
      -16384]) pCell_six_right_expanded_normal (fun _ => m)
  have hE := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, 0, -384, 3824, 37088, 84800, 59264, 2816, 512])
      (pa
        (pIntPoly pv [0, 0, 0, -192, -3136, -17280, -40960, -43008,
          -16384])
        (pIntPoly pv [0, 0, 0, -96, -256, 1920, 5120, -6144,
          -16384])))
    (pIntPoly pv [0, 0, -384, 3536, 33696, 69440, 23424, -46336,
      -32256]) pCell_six_expanded_normal (fun _ => m)
  have hsplit :
      clearedCell m 6 =
        IntRingNormaliser.eval (fun _ => m) (pCellA pv 6) +
          IntRingNormaliser.eval (fun _ => m) (pCellC pv 6) +
          ((IntRingNormaliser.eval (fun _ => m) (pCellNegLL pv 6) +
              IntRingNormaliser.eval (fun _ => m) (pCellNegLR pv 6)) +
            (IntRingNormaliser.eval (fun _ => m) (pCellNegRL pv 6) +
              IntRingNormaliser.eval (fun _ => m) (pCellNegRR pv 6))) := by
    simp [clearedCell, choose720Poly, pCellA, pCellC,
      pCellNegLL, pCellNegLR, pCellNegRL, pCellNegRR,
      pChoose720, pIntPoly, intPolyEval,
      pc, pv, pa, pm, pn, IntRingNormaliser.eval]
    apply cell_individual_split_algebra
  rw [hsplit]
  have hAC := (int_add_congr hA hC).trans hP
  have hLeft := (int_add_congr hLL hLR).trans hL
  have hRight := (int_add_congr hRL hRR).trans hR
  have hNeg := int_add_congr hLeft hRight
  have h := (int_add_congr hAC hNeg).trans hE
  simpa [intPolyEval, pIntPoly, pc, pv, pa, pm,
    IntRingNormaliser.eval] using h

private theorem cleared_step_six_identity (m : Int) :
    clearedStep m 6 = 720 * sevenBoundaryScaledFormula 6 (m + 1) := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pa
      (pIntPoly pv [0, -14605920, -38134800, -7986960, -69945120,
        -260880480, -70761600, 277119360, 184965120, 230400])
      (pm (pc 5670)
        (pIntPoly pv [0, 0, -384, 3536, 33696, 69440, 23424, -46336,
          -32256])))
    (pm (pc 720) (pFormula 6 (pa pv (pc 1))))
    pExpanded_six_step_normal (fun _ => m)
  rw [clearedStep, cleared_old_six_identity, cleared_cell_six_identity]
  simpa [sevenBoundaryScaledFormula, intPolyEval, pFormula, pIntPoly,
    pc, pv, pa, pm, IntRingNormaliser.eval] using h

private theorem cleared_step_identity (m : Int) (r : Nat) (hr : r ≤ 6) :
    clearedStep m r = 720 * sevenBoundaryScaledFormula r (m + 1) := by
  by_cases h6 : r = 6
  · subst r
    exact cleared_step_six_identity m
  by_cases h5 : r = 5
  · subst r
    exact cleared_step_five_identity m
  by_cases h4 : r = 4
  · subst r
    exact cleared_step_four_identity m
  have hr3 : r ≤ 3 := by omega
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pStep pv r) (pm (pc 720) (pFormula r (pa pv (pc 1))))
    (pStep_normal r hr3) (fun _ => m)
  rcases cases_le_three hr3 with h0 | h1 | h2 | h3 <;>
    subst r <;>
    simp [clearedStep, clearedOldPrefix, clearedCell,
      sevenBoundaryScaledFormula, choose720Poly, intPolyEval,
      pStep, pOldPrefix, pClearedCell, pFormula, pIntPoly,
      pChoose720, pFalling, pc, pv, pa, pm, pn, ps, pp,
      IntRingNormaliser.eval, IntRingNormaliser.intPow,
      Int.sub_eq_add_neg] at h ⊢ <;>
    simp only [Int.neg_add, Int.mul_assoc, Int.add_assoc] at h ⊢ <;>
    exact h

private theorem choose_zero : ∀ n : Nat, PNPaths.choose n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

private theorem choose_one : ∀ n : Nat, PNPaths.choose n 1 = n
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose, choose_one n, choose_zero n]
      omega

private def factNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factNat k

private def fallingNat (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => fallingNat n k * (n - k)

private theorem choose_factorial : ∀ k n : Nat, k ≤ 6 → k ≤ n →
    factNat k * PNPaths.choose n k = fallingNat n k
  | 0, n, _, _ => by simp [factNat, fallingNat, choose_zero]
  | k + 1, n, hk6, hkn => by
      have hklt : k < n := by omega
      have hadj := choose_adjacent_cross n k hklt
      have ih := choose_factorial k n (by omega) (by omega)
      simp only [factNat, fallingNat]
      calc
        (k + 1) * factNat k * PNPaths.choose n (k + 1) =
            factNat k * ((k + 1) * PNPaths.choose n (k + 1)) := by ac_rfl
        _ = factNat k * ((n - k) * PNPaths.choose n k) := by rw [hadj]
        _ = (factNat k * PNPaths.choose n k) * (n - k) := by ac_rfl
        _ = fallingNat n k * (n - k) := by rw [ih]

private def fallingInt (n : Int) : Nat → Int
  | 0 => 1
  | k + 1 => fallingInt n k * (n - k)

private def choose720Falling (n : Int) : Nat → Int
  | 0 => 720
  | 1 => 720 * n
  | 2 => 360 * fallingInt n 2
  | 3 => 120 * fallingInt n 3
  | 4 => 30 * fallingInt n 4
  | 5 => 6 * fallingInt n 5
  | 6 => fallingInt n 6
  | _ => 0

private def pChoose720Falling (n : PE) : Nat → PE
  | 0 => pc 720
  | 1 => pm (pc 720) n
  | 2 => pm (pc 360) (pFalling n 2)
  | 3 => pm (pc 120) (pFalling n 3)
  | 4 => pm (pc 30) (pFalling n 4)
  | 5 => pm (pc 6) (pFalling n 5)
  | 6 => pFalling n 6
  | _ => pc 0

private theorem pChoose720_falling_normal (k : Nat) (hk : k ≤ 6) :
    RingNormaliser.normalize (pChoose720Falling pv k) =
      RingNormaliser.normalize (pChoose720 pv k) := by
  rcases cases_le_six hk with h | h | h | h | h | h | h <;>
    subst k <;> decide

private theorem choose720Falling_eq (n : Int) (k : Nat) (hk : k ≤ 6) :
    choose720Falling n k = choose720Poly n k := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pChoose720Falling pv k) (pChoose720 pv k)
    (pChoose720_falling_normal k hk) (fun _ => n)
  rcases cases_le_six hk with h0 | h1 | h2 | h3 | h4 | h5 | h6 <;>
    subst k <;>
    simpa [choose720Falling, choose720Poly, fallingInt, intPolyEval,
      pChoose720Falling, pChoose720, pFalling, pIntPoly, pc, pv, pa, pm,
      pn, ps, pp, IntRingNormaliser.eval, IntRingNormaliser.intPow,
      Int.sub_eq_add_neg] using h

private theorem choose720_eq (n k : Nat) (hn : 6 ≤ n) (hk : k ≤ 6) :
    720 * (PNPaths.choose n k : Int) = choose720Poly (n : Int) k := by
  rcases cases_le_six hk with h | h | h | h | h | h | h <;> subst k
  · simp [choose720Poly, choose_zero]
  · simp [choose720Poly, choose_one]
  · have h := congrArg Int.ofNat (choose_factorial 2 n (by omega) (by omega))
    simp [factNat, fallingNat] at h
    calc
      720 * (PNPaths.choose n 2 : Int) =
          360 * (2 * (PNPaths.choose n 2 : Int)) := by
            rw [show (720 : Int) = 360 * 2 by decide]; ac_rfl
      _ = 360 * ((n : Int) * ((n : Int) - 1)) := by
        simpa only [Int.ofNat_eq_natCast, Int.natCast_mul,
          show (((n - 1 : Nat) : Int)) = (n : Int) - 1 by omega] using
            congrArg (fun z : Int => 360 * z) h
      _ = choose720Poly (n : Int) 2 :=
        by simpa [choose720Falling, fallingInt] using
          choose720Falling_eq (n : Int) 2 (by omega)
  · have h := congrArg Int.ofNat (choose_factorial 3 n (by omega) (by omega))
    simp [factNat, fallingNat] at h
    calc
      720 * (PNPaths.choose n 3 : Int) =
          120 * (6 * (PNPaths.choose n 3 : Int)) := by
            rw [show (720 : Int) = 120 * 6 by decide]; ac_rfl
      _ = 120 * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) := by
        simpa only [Int.ofNat_eq_natCast, Int.natCast_mul,
          show (((n - 1 : Nat) : Int)) = (n : Int) - 1 by omega,
          show (((n - 2 : Nat) : Int)) = (n : Int) - 2 by omega] using
            congrArg (fun z : Int => 120 * z) h
      _ = choose720Poly (n : Int) 3 :=
        by simpa [choose720Falling, fallingInt] using
          choose720Falling_eq (n : Int) 3 (by omega)
  · have h := congrArg Int.ofNat (choose_factorial 4 n (by omega) (by omega))
    simp [factNat, fallingNat] at h
    calc
      720 * (PNPaths.choose n 4 : Int) =
          30 * (24 * (PNPaths.choose n 4 : Int)) := by
            rw [show (720 : Int) = 30 * 24 by decide]; ac_rfl
      _ = 30 * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2) *
          ((n : Int) - 3)) := by
        simpa only [Int.ofNat_eq_natCast, Int.natCast_mul,
          show (((n - 1 : Nat) : Int)) = (n : Int) - 1 by omega,
          show (((n - 2 : Nat) : Int)) = (n : Int) - 2 by omega,
          show (((n - 3 : Nat) : Int)) = (n : Int) - 3 by omega] using
            congrArg (fun z : Int => 30 * z) h
      _ = choose720Poly (n : Int) 4 :=
        by simpa [choose720Falling, fallingInt] using
          choose720Falling_eq (n : Int) 4 (by omega)
  · have h := congrArg Int.ofNat (choose_factorial 5 n (by omega) (by omega))
    simp [factNat, fallingNat] at h
    calc
      720 * (PNPaths.choose n 5 : Int) =
          6 * (120 * (PNPaths.choose n 5 : Int)) := by
            rw [show (720 : Int) = 6 * 120 by decide]; ac_rfl
      _ = 6 * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2) *
          ((n : Int) - 3) * ((n : Int) - 4)) := by
        simpa only [Int.ofNat_eq_natCast, Int.natCast_mul,
          show (((n - 1 : Nat) : Int)) = (n : Int) - 1 by omega,
          show (((n - 2 : Nat) : Int)) = (n : Int) - 2 by omega,
          show (((n - 3 : Nat) : Int)) = (n : Int) - 3 by omega,
          show (((n - 4 : Nat) : Int)) = (n : Int) - 4 by omega] using
            congrArg (fun z : Int => 6 * z) h
      _ = choose720Poly (n : Int) 5 :=
        by simpa [choose720Falling, fallingInt] using
          choose720Falling_eq (n : Int) 5 (by omega)
  · have h := congrArg Int.ofNat (choose_factorial 6 n (by omega) (by omega))
    simp [factNat, fallingNat] at h
    have hf : choose720Falling (n : Int) 6 = choose720Poly (n : Int) 6 :=
      choose720Falling_eq (n : Int) 6 (by omega)
    rw [← hf]
    have hn1 : (((n - 1 : Nat) : Int)) = (n : Int) - 1 := by omega
    have hn2 : (((n - 2 : Nat) : Int)) = (n : Int) - 2 := by omega
    have hn3 : (((n - 3 : Nat) : Int)) = (n : Int) - 3 := by omega
    have hn4 : (((n - 4 : Nat) : Int)) = (n : Int) - 4 := by omega
    have hn5 : (((n - 5 : Nat) : Int)) = (n : Int) - 5 := by omega
    rw [hn1, hn2, hn3, hn4, hn5] at h
    simpa [choose720Falling, fallingInt] using h

private def actualCell (m r : Nat) : Int :=
  let S := 4 * m + 2
  Int.ofNat (7 * m * m) *
      (if 2 ≤ r then Int.ofNat (PNPaths.choose (S + 1) (r - 2)) else 0) -
    Int.ofNat (m * m) *
      (Int.ofNat (PNPaths.choose (S + 3) r) +
        3 * Int.ofNat (PNPaths.choose (S + 2) r) +
        3 * Int.ofNat (PNPaths.choose (S + 1) r) +
        Int.ofNat (PNPaths.choose S r)) +
    Int.ofNat (8 * m * (m + 1)) *
      Int.ofNat (PNPaths.choose (2 * m + 4) r)

private def actualOldPrefix (m : Nat) : Nat → Int
  | 0 => (PNPaths.choose (4 * m + 2) 0 : Int) *
      sevenBoundaryScaledFormula 0 m
  | 1 => (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 1 m
  | 2 => (PNPaths.choose (4 * m + 2) 2 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 1 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 2 m
  | 3 => (PNPaths.choose (4 * m + 2) 3 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 2 : Int) *
        sevenBoundaryScaledFormula 1 m +
      (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 2 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 3 m
  | 4 => (PNPaths.choose (4 * m + 2) 4 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 3 : Int) *
        sevenBoundaryScaledFormula 1 m +
      (PNPaths.choose (4 * m + 2) 2 : Int) *
        sevenBoundaryScaledFormula 2 m +
      (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 3 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 4 m
  | 5 => (PNPaths.choose (4 * m + 2) 5 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 4 : Int) *
        sevenBoundaryScaledFormula 1 m +
      (PNPaths.choose (4 * m + 2) 3 : Int) *
        sevenBoundaryScaledFormula 2 m +
      (PNPaths.choose (4 * m + 2) 2 : Int) *
        sevenBoundaryScaledFormula 3 m +
      (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 4 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 5 m
  | 6 => (PNPaths.choose (4 * m + 2) 6 : Int) *
        sevenBoundaryScaledFormula 0 m +
      (PNPaths.choose (4 * m + 2) 5 : Int) *
        sevenBoundaryScaledFormula 1 m +
      (PNPaths.choose (4 * m + 2) 4 : Int) *
        sevenBoundaryScaledFormula 2 m +
      (PNPaths.choose (4 * m + 2) 3 : Int) *
        sevenBoundaryScaledFormula 3 m +
      (PNPaths.choose (4 * m + 2) 2 : Int) *
        sevenBoundaryScaledFormula 4 m +
      (PNPaths.choose (4 * m + 2) 1 : Int) *
        sevenBoundaryScaledFormula 5 m +
      (PNPaths.choose (4 * m + 2) 0 : Int) *
        sevenBoundaryScaledFormula 6 m
  | _ => 0

private theorem actual_step (m r : Nat) (hm : 1 ≤ m) (hr : r ≤ 6) :
    actualOldPrefix m r + 5670 * actualCell m r =
      sevenBoundaryScaledFormula r (m + 1) := by
  have hnD : 6 ≤ 4 * m + 2 := by omega
  have hnS1 : 6 ≤ 4 * m + 3 := by omega
  have hnS2 : 6 ≤ 4 * m + 4 := by omega
  have hnS3 : 6 ≤ 4 * m + 5 := by omega
  have hnT : 6 ≤ 2 * m + 4 := by omega
  have hp := cleared_step_identity (m : Int) r hr
  have hOld : 720 * actualOldPrefix m r = clearedOldPrefix (m : Int) r := by
    have h0 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 0 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 0 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 0 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 0 * a := by
          rw [choose720_eq (4 * m + 2) 0 hnD (by omega)]
        _ = _ := by simp
    have h1 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 1 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 1 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 1 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 1 * a := by
          rw [choose720_eq (4 * m + 2) 1 hnD (by omega)]
        _ = _ := by simp
    have h2 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 2 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 2 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 2 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 2 * a := by
          rw [choose720_eq (4 * m + 2) 2 hnD (by omega)]
        _ = _ := by simp
    have h3 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 3 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 3 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 3 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 3 * a := by
          rw [choose720_eq (4 * m + 2) 3 hnD (by omega)]
        _ = _ := by simp
    have h4 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 4 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 4 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 4 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 4 * a := by
          rw [choose720_eq (4 * m + 2) 4 hnD (by omega)]
        _ = _ := by simp
    have h5 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 5 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 5 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 5 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 5 * a := by
          rw [choose720_eq (4 * m + 2) 5 hnD (by omega)]
        _ = _ := by simp
    have h6 (a : Int) :
        720 * ((PNPaths.choose (4 * m + 2) 6 : Int) * a) =
          choose720Poly (4 * (m : Int) + 2) 6 * a := by
      calc
        _ = (720 * (PNPaths.choose (4 * m + 2) 6 : Int)) * a := by ac_rfl
        _ = choose720Poly ((4 * m + 2 : Nat) : Int) 6 * a := by
          rw [choose720_eq (4 * m + 2) 6 hnD (by omega)]
        _ = _ := by simp
    rcases cases_le_six hr with e | e | e | e | e | e | e <;>
      subst r <;>
      simp only [actualOldPrefix, clearedOldPrefix, Int.mul_add,
        h0, h1, h2, h3, h4, h5, h6]
  have hCellScale :
      720 * actualCell m r =
        let S := 4 * m + 2
        Int.ofNat (7 * m * m) *
            (if 2 ≤ r then
              720 * Int.ofNat (PNPaths.choose (S + 1) (r - 2)) else 0) -
          Int.ofNat (m * m) *
            (720 * Int.ofNat (PNPaths.choose (S + 3) r) +
              3 * (720 * Int.ofNat (PNPaths.choose (S + 2) r)) +
              3 * (720 * Int.ofNat (PNPaths.choose (S + 1) r)) +
              720 * Int.ofNat (PNPaths.choose S r)) +
          Int.ofNat (8 * m * (m + 1)) *
            (720 * Int.ofNat (PNPaths.choose (2 * m + 4) r)) := by
    unfold actualCell
    dsimp only
    by_cases h2r : 2 ≤ r
    · rw [if_pos h2r, if_pos h2r]
      simp only [Int.mul_add, Int.mul_sub]
      ac_rfl
    · rw [if_neg h2r, if_neg h2r]
      simp only [Int.mul_add, Int.mul_sub]
      ac_rfl
  have hCell : 720 * actualCell m r = clearedCell (m : Int) r := by
    rw [hCellScale]
    simp only [Int.ofNat_eq_natCast]
    have hcD : (((4 * m + 2 : Nat) : Int)) = 4 * (m : Int) + 2 := by omega
    have hcS1 : (((4 * m + 2 + 1 : Nat) : Int)) = 4 * (m : Int) + 2 + 1 := by omega
    have hcS2 : (((4 * m + 2 + 2 : Nat) : Int)) = 4 * (m : Int) + 2 + 2 := by omega
    have hcS3 : (((4 * m + 2 + 3 : Nat) : Int)) = 4 * (m : Int) + 2 + 3 := by omega
    have hcT : (((2 * m + 4 : Nat) : Int)) = 2 * (m : Int) + 4 := by omega
    rcases cases_le_six hr with e | e | e | e | e | e | e <;> subst r
    · simp only [clearedCell]
      rw [if_neg (by decide : ¬ 2 ≤ 0)]
      rw [choose720_eq (4*m+2+3) 0 (by omega) (by omega),
        choose720_eq (4*m+2+2) 0 (by omega) (by omega),
        choose720_eq (4*m+2+1) 0 (by omega) (by omega),
        choose720_eq (4*m+2) 0 hnD (by omega),
        choose720_eq (2*m+4) 0 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_neg (by decide : ¬ 2 ≤ 1)]
      rw [choose720_eq (4*m+2+3) 1 (by omega) (by omega),
        choose720_eq (4*m+2+2) 1 (by omega) (by omega),
        choose720_eq (4*m+2+1) 1 (by omega) (by omega),
        choose720_eq (4*m+2) 1 hnD (by omega),
        choose720_eq (2*m+4) 1 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_pos (by decide : 2 ≤ 2), show 2 - 2 = 0 by decide]
      rw [choose720_eq (4*m+2+1) 0 (by omega) (by omega),
        choose720_eq (4*m+2+3) 2 (by omega) (by omega),
        choose720_eq (4*m+2+2) 2 (by omega) (by omega),
        choose720_eq (4*m+2+1) 2 (by omega) (by omega),
        choose720_eq (4*m+2) 2 hnD (by omega),
        choose720_eq (2*m+4) 2 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_pos (by decide : 2 ≤ 3), show 3 - 2 = 1 by decide]
      rw [choose720_eq (4*m+2+1) 1 (by omega) (by omega),
        choose720_eq (4*m+2+3) 3 (by omega) (by omega),
        choose720_eq (4*m+2+2) 3 (by omega) (by omega),
        choose720_eq (4*m+2+1) 3 (by omega) (by omega),
        choose720_eq (4*m+2) 3 hnD (by omega),
        choose720_eq (2*m+4) 3 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_pos (by decide : 2 ≤ 4), show 4 - 2 = 2 by decide]
      rw [choose720_eq (4*m+2+1) 2 (by omega) (by omega),
        choose720_eq (4*m+2+3) 4 (by omega) (by omega),
        choose720_eq (4*m+2+2) 4 (by omega) (by omega),
        choose720_eq (4*m+2+1) 4 (by omega) (by omega),
        choose720_eq (4*m+2) 4 hnD (by omega),
        choose720_eq (2*m+4) 4 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_pos (by decide : 2 ≤ 5), show 5 - 2 = 3 by decide]
      rw [choose720_eq (4*m+2+1) 3 (by omega) (by omega),
        choose720_eq (4*m+2+3) 5 (by omega) (by omega),
        choose720_eq (4*m+2+2) 5 (by omega) (by omega),
        choose720_eq (4*m+2+1) 5 (by omega) (by omega),
        choose720_eq (4*m+2) 5 hnD (by omega),
        choose720_eq (2*m+4) 5 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
    · simp only [clearedCell]
      rw [if_pos (by decide : 2 ≤ 6), show 6 - 2 = 4 by decide]
      rw [choose720_eq (4*m+2+1) 4 (by omega) (by omega),
        choose720_eq (4*m+2+3) 6 (by omega) (by omega),
        choose720_eq (4*m+2+2) 6 (by omega) (by omega),
        choose720_eq (4*m+2+1) 6 (by omega) (by omega),
        choose720_eq (4*m+2) 6 hnD (by omega),
        choose720_eq (2*m+4) 6 hnT (by omega)]
      rw [hcD, hcS1, hcS2, hcS3, hcT]
      push_cast
      rfl
  have hscaled :
      720 * (actualOldPrefix m r + 5670 * actualCell m r) =
        clearedStep (m : Int) r := by
    unfold clearedStep
    rw [Int.mul_add, hOld]
    rw [show 720 * (5670 * actualCell m r) = 5670 *
        (720 * actualCell m r) by ac_rfl, hCell]
  omega

private theorem sevenGapDeficit_one (r : Nat) (hr : r ≤ 6) :
    sevenGapDeficit 1 r = 0 := by
  rcases cases_le_six hr with h | h | h | h | h | h | h <;>
    subst r <;> decide

private theorem sevenBoundaryScaledFormula_one (r : Nat) (hr : r ≤ 6) :
    sevenBoundaryScaledFormula r 1 = 0 := by
  rcases cases_le_six hr with h | h | h | h | h | h | h <;>
    subst r <;> decide

/-- Exact simultaneous closed formula for all seven boundary deficits.  The
factor `5670` is the common denominator clearing used by the downstream
projective boundary consumer. -/
theorem sevenGapDeficit_boundary_scaled
    (m r : Nat) (hm : 1 ≤ m) (hr : r ≤ 6) :
    5670 * sevenGapDeficit m r =
      sevenBoundaryScaledFormula r (m : Int) := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        rw [sevenGapDeficit_one r hr]
        simpa using (sevenBoundaryScaledFormula_one r hr).symm
      · have hmpos : 1 ≤ m := by omega
        have hrdeg : r ≤ sevenGapDegree (m + 1) := by
          have htwo : 2 ≤ m + 1 := by omega
          have hsq := Nat.mul_le_mul htwo htwo
          have htwosq : 8 ≤ 2 * ((m + 1) * (m + 1)) := by
            simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsq
          unfold sevenGapDegree
          rw [Nat.mul_assoc]
          omega
        have hPrefix :
            5670 * sevenPascalElevate (4 * m + 2) (sevenGapDeficit m) r =
              actualOldPrefix m r := by
          rw [sevenPascalElevate_prefix_formula (4 * m + 2)
            (sevenGapDeficit m) r hr]
          have h0 (c : Int) :
              5670 * (c * sevenGapDeficit m 0) =
                c * sevenBoundaryScaledFormula 0 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 0) := by ac_rfl
              _ = _ := by rw [ih 0 hmpos (by omega)]
          have h1 (c : Int) :
              5670 * (c * sevenGapDeficit m 1) =
                c * sevenBoundaryScaledFormula 1 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 1) := by ac_rfl
              _ = _ := by rw [ih 1 hmpos (by omega)]
          have h2 (c : Int) :
              5670 * (c * sevenGapDeficit m 2) =
                c * sevenBoundaryScaledFormula 2 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 2) := by ac_rfl
              _ = _ := by rw [ih 2 hmpos (by omega)]
          have h3 (c : Int) :
              5670 * (c * sevenGapDeficit m 3) =
                c * sevenBoundaryScaledFormula 3 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 3) := by ac_rfl
              _ = _ := by rw [ih 3 hmpos (by omega)]
          have h4 (c : Int) :
              5670 * (c * sevenGapDeficit m 4) =
                c * sevenBoundaryScaledFormula 4 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 4) := by ac_rfl
              _ = _ := by rw [ih 4 hmpos (by omega)]
          have h5 (c : Int) :
              5670 * (c * sevenGapDeficit m 5) =
                c * sevenBoundaryScaledFormula 5 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 5) := by ac_rfl
              _ = _ := by rw [ih 5 hmpos (by omega)]
          have h6 (c : Int) :
              5670 * (c * sevenGapDeficit m 6) =
                c * sevenBoundaryScaledFormula 6 (m : Int) := by
            calc
              _ = c * (5670 * sevenGapDeficit m 6) := by ac_rfl
              _ = _ := by rw [ih 6 hmpos (by omega)]
          rcases cases_le_six hr with e | e | e | e | e | e | e <;>
            subst r <;>
            simp [actualOldPrefix, Int.mul_add, h0, h1, h2, h3, h4,
              h5, h6]
        have hCell := sevenGapCellBernCoeff_next_deficit m r hmpos hrdeg
        dsimp only at hCell
        rw [sevenGapDeficit_succ m r hmpos hrdeg]
        rw [Int.mul_add, hPrefix, hCell]
        exact actual_step m r hmpos hr

#print axioms sevenBoundaryScaledFormula
#print axioms sevenGapDeficit_boundary_scaled

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
