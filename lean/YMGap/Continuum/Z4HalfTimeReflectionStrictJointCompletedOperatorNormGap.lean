/-
# From the completed form gap to an operator-norm gap

The strong-coupling clustering campaign has already produced the strict
quadratic-form estimate

  <Sx,x> <= q <x,x>,   q = 1/16,

on the full completed vacuum complement, for the concrete physical transfer
`S = T^2`.  This file strengthens that statement intrinsically on the same
completion.  The oriented doubled-time covariance first supplies the midpoint
identity

  <T^s x,T^s y> = <x,T^(2s)y>.

Consequently the positive `S`-form satisfies Cauchy--Schwarz.  Applying that
inequality to `x` and `Sx`, followed by constructive nonnegative-factor
cancellation, gives the square-form estimate and hence

  ||Sx||^2 <= q^2 ||x||^2.

No spectral theorem, real scalar action on the carrier, exact dense-kernel
replacement, or additional logical assumption is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredCompletedGap

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredCompletedGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The midpoint identity -/

/-- Simultaneously translating two staged cylinders by `shift` is the same
reflection pairing as translating only the right cylinder by `2 * shift`.
Both comparisons are made in explicit maximum-common-base boxes. -/
theorem strictJointCylinderStageTimeTranslate_midpoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (left.timeTranslate shift) (right.timeTranslate shift))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        left (right.timeTranslate (shift + shift))) := by
  let outer := max left.base right.base
  let evenShift := shift + shift
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have houterFirst : outer <= outer + shift := Nat.le_add_right _ _
  have houterFinal : outer <= outer + evenShift := Nat.le_add_right _ _
  have hleftFinal : left.base <= outer + evenShift :=
    Nat.le_trans hleft houterFinal
  have hrightFinal : right.base <= outer + evenShift :=
    Nat.le_trans hright houterFinal
  let L := boxTransportStrictJointCylinderVector hleft left.vector
  let R := boxTransportStrictJointCylinderVector hright right.vector
  have hfirst := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (left.timeTranslate shift) (right.timeTranslate shift)
      (Nat.add_le_add_right hleft shift)
      (Nat.add_le_add_right hright shift)
  have hsecond := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left (right.timeTranslate evenShift)
      hleftFinal (Nat.add_le_add_right hright evenShift)
  have htranslatedLeft :
      boxTransportStrictJointCylinderVector
          (Nat.add_le_add_right hleft shift)
          (timeTranslateStrictJointCylinderVector shift left.vector) =
        timeTranslateStrictJointCylinderVector shift L :=
    (timeTranslate_boxTransportStrictJointCylinderVector
      hleft shift left.vector).symm
  have htranslatedRight :
      boxTransportStrictJointCylinderVector
          (Nat.add_le_add_right hright shift)
          (timeTranslateStrictJointCylinderVector shift right.vector) =
        timeTranslateStrictJointCylinderVector shift R :=
    (timeTranslate_boxTransportStrictJointCylinderVector
      hright shift right.vector).symm
  have htransportLeft :
      boxTransportStrictJointCylinderVector hleftFinal left.vector =
        boxTransportStrictJointCylinderVector houterFinal L :=
    (boxTransportStrictJointCylinderVector_trans
      hleft houterFinal left.vector).symm
  have htranslatedFinalRight :
      boxTransportStrictJointCylinderVector
          (Nat.add_le_add_right hright evenShift)
          (timeTranslateStrictJointCylinderVector evenShift right.vector) =
        timeTranslateStrictJointCylinderVector evenShift R :=
    (timeTranslate_boxTransportStrictJointCylinderVector
      hright evenShift right.vector).symm
  dsimp only [StrictJointCylinderStage.timeTranslate] at hfirst hsecond
  rw [htranslatedLeft, htranslatedRight] at hfirst
  rw [htransportLeft, htranslatedFinalRight] at hsecond
  have hfixed := orientedDoubledTimeCovariance
    hcoupling hle shift L R
  exact CReal.Equiv.trans (CReal.Equiv.symm hfirst)
    (CReal.Equiv.trans hfixed hsecond)

/-- The midpoint identity passes through the choice-free pairing limit for
arbitrary Cauchy representatives. -/
theorem cauchyPairingLimit_timeTranslate_midpoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle shift).mapCauchy X)
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle shift).mapCauchy Y))
      (cauchyPairingLimit hcoupling hle X
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (shift + shift)).mapCauchy Y)) := by
  let TX := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle shift).mapCauchy X
  let TY := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle shift).mapCauchy Y
  let TTY := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (shift + shift)).mapCauchy Y
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle TX TY)
    (bSeq := cauchyPairingSeq hcoupling hle X TTY)
  · intro n
    exact strictJointCylinderStageTimeTranslate_midpoint
      hcoupling hle shift (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle TX TY
  · exact cauchyPairingSeq_converges hcoupling hle X TTY

/-- Completed midpoint identity for every lattice-time shift. -/
theorem strictJointCylinderCompletedTimeTranslate_midpoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle shift left)
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle shift right) =
      strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (cauchyPairingLimit_timeTranslate_midpoint
      hcoupling hle shift X Y)

/-- The one-step midpoint identity written for the physical transfer
`S = T^2`. -/
theorem strictJointCylinderCompletedInner_twoStep_midpoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left)
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right) =
      strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer
          hcoupling hle left) right := by
  calc
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left)
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right) =
      strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (1 + 1) right) :=
      strictJointCylinderCompletedTimeTranslate_midpoint
        hcoupling hle 1 left right
    _ = strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle left) right := by
      exact (strictJointCylinderCompletedTwoStepTransfer_self_adjoint
        hcoupling hle left right).symm

/-! ## 2. Cauchy--Schwarz for the positive two-step form -/

/-- Cauchy--Schwarz for the positive form `(x,y) |-> <Sx,y>`, obtained by
representing it as the ordinary inner form of the common midpoint translates. -/
theorem strictJointCylinderCompletedTwoStepForm_cauchy_schwarz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (CReal.RCmul
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle left) right)
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle left) right))
      (CReal.RCmul
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle left) left)
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle right) right)) := by
  rw [<- strictJointCylinderCompletedInner_twoStep_midpoint
        hcoupling hle left right,
      <- strictJointCylinderCompletedInner_twoStep_midpoint
        hcoupling hle left left,
      <- strictJointCylinderCompletedInner_twoStep_midpoint
        hcoupling hle right right]
  exact strictJointCylinderCompletedInner_cauchy_schwarz
    hcoupling hle
      (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left)
      (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right)

/-! ## 3. Constructive cancellation in the real quotient -/

private theorem q_half_mul_lt_self_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    HalfPow.half * value < value := by
  have hscaled :=
    YMGap.Continuum.ClusteringImpliesGap.mul_lt_mul_of_pos_right
      hvalue (show HalfPow.half < (1 : Q') by decide)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hscaled
    (Q'.le_of_eqv (Q'.one_mul_eqv value))

private theorem q_sub_add_regroup_local (a b e : Q') :
    ((a + -b) + (b + e)).eqv (a + e) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) (b + e)) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-b) b e)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-b) + b) 0 e
      (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' e)

/-- A positive difference `A-B`, together with eventual nonnegativity of `B`,
forces eventual strict positivity of `A`. -/
private theorem posEv_of_sub_pos_of_nonnegative
    {A B : CReal} (hdifference : PosEv (CReal.sub A B))
    (hB : CReal.leEv CReal.czero B) : PosEv A := by
  obtain ⟨d, hd, Nd, hNd⟩ := eventually_ge_of_posEv hdifference
  let e := HalfPow.half * d
  have he : (0 : Q') < e := ExpNeg.half_mul_pos d hd
  obtain ⟨NB, hNB⟩ := hB e he
  refine posEv_of_eventually he ⟨max Nd NB, fun n hn => ?_⟩
  have hnd : Nd <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnb : NB <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hdiff : d <= A.approx n + -(B.approx n) := hNd n hnd
  have hnonnegative : (0 : Q') <= B.approx n + e := hNB n hnb
  have hadd := Q'.add_le_add hdiff hnonnegative
  have hde : d <= A.approx n + e := by
    refine Q'.le_trans' _ (d + 0) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' d)))
    · exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv
          (q_sub_add_regroup_local (A.approx n) (B.approx n) e))
  apply YMGap.Continuum.MeanExpConvexProgress.le_of_add_le_add_right
    (c := e)
  exact Q'.le_trans' _ d _
    (Q'.le_of_eqv (ExpNeg.two_halves d)) hde

/-- A positive witness for `A-B` contradicts an eventual proof of `A <= B`.
This is the strict branch used by nonnegative-factor cancellation. -/
private theorem posEv_sub_false_of_leEv {A B : CReal}
    (hdifference : PosEv (CReal.sub A B))
    (hle : CReal.leEv A B) : False := by
  obtain ⟨d, hd, Nd, hNd⟩ := eventually_ge_of_posEv hdifference
  let e := HalfPow.half * d
  have he : (0 : Q') < e := ExpNeg.half_mul_pos d hd
  obtain ⟨Nle, hNle⟩ := hle e he
  let n := max Nd Nle
  have hnd : Nd <= n := Nat.le_max_left _ _
  have hnle : Nle <= n := Nat.le_max_right _ _
  have hlower : d <= A.approx n + -(B.approx n) := hNd n hnd
  have hupper : A.approx n + -(B.approx n) <= e :=
    Q'.sub_le_of_le_add (hNle n hnle)
  have hde : d <= e := Q'.le_trans' _ _ _ hlower hupper
  have hcontr : d < d := Q'.lt_of_le_of_lt hde
    (q_half_mul_lt_self_local hd)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' d hcontr

/-- If `0 <= F`, `0 <= B`, and `F^2 <= B F`, then `F <= B` in the
constructive real quotient.  The proof never divides by `F`: a hypothetical
positive excess makes `F` strictly positive, at which point the existing
positive-factor cancellation applies. -/
theorem CReal.RCle_of_mul_self_le_mul_right_nonnegative
    {F B : CReal.RC} (hF : CReal.RCnonneg F)
    (hB : CReal.RCnonneg B)
    (hproduct : CReal.RCle (CReal.RCmul F F) (CReal.RCmul B F)) :
    CReal.RCle F B := by
  revert hF hB hproduct
  refine Quotient.inductionOn₂ F B ?_
  intro f b hf hb hproduct
  apply leEv_of_no_posEv_sub
  intro hexcess
  have hfpositive : PosEv f :=
    posEv_of_sub_pos_of_nonnegative hexcess hb
  have hcancelled : CReal.leEv f b :=
    leEv_cancel_mul_right_posEv hfpositive hproduct
  exact posEv_sub_false_of_leEv hexcess hcancelled

/-- Multiplication in `RC` is monotone in its right argument when the left
factor is nonnegative. -/
theorem CReal.RCmul_mono_nonnegative_left_local {F A B : CReal.RC}
    (hF : CReal.RCnonneg F) (hAB : CReal.RCle A B) :
    CReal.RCle (CReal.RCmul F A) (CReal.RCmul F B) := by
  revert hF hAB
  refine Quotient.inductionOn₃ F A B ?_
  intro f a b hf hab
  exact CReal.leEv_mul_nonneg_left hf hab

/-- Move a rational scale between the two factors of an `RC` product. -/
private theorem RCmul_scale_right_eq_scale_left
    (scalar : Q') (left right : CReal.RC) :
    CReal.RCmul left (CReal.RCscale scalar right) =
      CReal.RCmul (CReal.RCscale scalar left) right := by
  refine Quotient.inductionOn₂ left right ?_
  intro L R
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change (L.approx n * (scalar * R.approx n)).eqv
          ((scalar * L.approx n) * R.approx n)
        ring_qeqv))

/-! ## 4. Square-form and operator-norm gaps -/

/-- Any nonnegative strict form gap for the concrete positive transfer `S`
automatically supplies the corresponding square-form estimate. -/
theorem strictJointCylinderCompletedTwoStepTransfer_square_form_gap_of_form_gap
    {coupling separator : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (gap : StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle separator)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector))
      (CReal.RCscale separator
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
          vector)) := by
  let Svector := strictJointCylinderCompletedTwoStepTransfer
    hcoupling hle vector
  let normS := strictJointCylinderCompletedInner
    hcoupling hle Svector Svector
  let form := strictJointCylinderCompletedInner
    hcoupling hle Svector vector
  let nextForm := strictJointCylinderCompletedInner hcoupling hle
    (strictJointCylinderCompletedTwoStepTransfer hcoupling hle Svector) Svector
  have hSorthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle Svector :=
    strictJointCylinderCompletedTwoStepTransfer_preserves_vacuumOrthogonal
      hcoupling hle vector horthogonal
  have hcs : CReal.RCle
      (CReal.RCmul normS normS)
      (CReal.RCmul form nextForm) := by
    exact strictJointCylinderCompletedTwoStepForm_cauchy_schwarz
      hcoupling hle vector Svector
  have hnext : CReal.RCle nextForm
      (CReal.RCscale separator normS) :=
    gap.2.2 Svector hSorthogonal
  have hformNonnegative : CReal.RCnonneg form :=
    strictJointCylinderCompletedTwoStepTransfer_positive
      hcoupling hle vector
  have hproductScaled : CReal.RCle
      (CReal.RCmul form nextForm)
      (CReal.RCmul form (CReal.RCscale separator normS)) :=
    CReal.RCmul_mono_nonnegative_left_local hformNonnegative hnext
  rw [RCmul_scale_right_eq_scale_left] at hproductScaled
  have hnormNonnegative : CReal.RCnonneg normS :=
    strictJointCylinderCompletedInner_self_nonneg hcoupling hle Svector
  have hscaledFormNonnegative :
      CReal.RCnonneg (CReal.RCscale separator form) := by
    have hscaled := CReal.RCscale_mono gap.1 hformNonnegative
    rwa [CReal.RCscale_RCzero] at hscaled
  exact CReal.RCle_of_mul_self_le_mul_right_nonnegative
    hnormNonnegative hscaledFormNonnegative
      (CReal.RCle_trans hcs hproductScaled)

/-- A completed strict form gap `q` upgrades to the genuine operator-norm
estimate `||Sx||^2 <= q^2 ||x||^2` on the same vacuum complement. -/
theorem strictJointCylinderCompletedTwoStepTransfer_norm_gap_of_form_gap
    {coupling separator : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (gap : StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle separator)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector))
      (CReal.RCscale (separator * separator)
        (strictJointCylinderCompletedInner hcoupling hle vector vector)) := by
  refine CReal.RCle_trans
    (strictJointCylinderCompletedTwoStepTransfer_square_form_gap_of_form_gap
      hcoupling hle gap vector horthogonal) ?_
  have hform := gap.2.2 vector horthogonal
  have hscaled := CReal.RCscale_mono gap.1 hform
  refine CReal.RCle_trans hscaled ?_
  rw [CReal.RCscale_RCscale]
  exact CReal.RCle_refl _

/-- The concrete strong-coupling endpoint has operator norm at most `1/16` on
the completed vacuum complement. -/
theorem anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate * anchorDecoratedDoubledTimeRate)
        (strictJointCylinderCompletedInner hcoupling hle vector vector)) :=
  strictJointCylinderCompletedTwoStepTransfer_norm_gap_of_form_gap
    hcoupling hle
      (anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap hcoupling hle)
      vector horthogonal

/-! ## 5. Iterated geometric decay on the completed vacuum complement -/

/-- The operator-norm estimate iterates along the concrete semigroup powers
`S^n = T^(2n)`. -/
theorem strictJointCylinderCompletedTwoStepPower_norm_gap_of_form_gap
    {coupling separator : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (gap : StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle separator)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector)
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector))
      (CReal.RCscale ((separator * separator) ^ n)
        (strictJointCylinderCompletedInner hcoupling hle vector vector)) := by
  induction n with
  | zero =>
      rw [strictJointCylinderCompletedTwoStepPower_zero,
        Q'.pow_zero, CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [strictJointCylinderCompletedTwoStepPower_succ]
      have hpowerOrthogonal :=
        strictJointCylinderCompletedTwoStepPower_preserves_vacuumOrthogonal
          hcoupling hle k vector horthogonal
      have hstep :=
        strictJointCylinderCompletedTwoStepTransfer_norm_gap_of_form_gap
          hcoupling hle gap
            (strictJointCylinderCompletedTwoStepPower hcoupling hle k vector)
            hpowerOrthogonal
      refine CReal.RCle_trans hstep ?_
      have hseparatorSqNonnegative :
          (0 : Q') <= separator * separator :=
        Q'.mul_nonneg separator separator gap.1 gap.1
      have hscaled :=
        CReal.RCscale_mono hseparatorSqNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-- The strong-coupling completed transfer powers decay geometrically on the
vacuum complement with squared-norm rate `(1/16)^2` per physical two-step. -/
theorem anchorDecoratedDoubledTimeRate_completed_power_norm_decay
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector)
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector))
      (CReal.RCscale
        ((anchorDecoratedDoubledTimeRate *
          anchorDecoratedDoubledTimeRate) ^ n)
        (strictJointCylinderCompletedInner hcoupling hle vector vector)) :=
  strictJointCylinderCompletedTwoStepPower_norm_gap_of_form_gap
    hcoupling hle
      (anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap hcoupling hle)
      n vector horthogonal

/-- Squared matrix coefficients inherit the iterated norm decay.  Only the
propagated vector must be vacuum-orthogonal; the test vector is arbitrary. -/
theorem strictJointCylinderCompletedTwoStepPower_matrixCoefficientSq_decay_of_form_gap
    {coupling separator : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (gap : StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle separator)
    (n : Nat)
    (vector test : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    CReal.RCle
      (CReal.RCmul
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector) test)
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector) test))
      (CReal.RCmul
        (CReal.RCscale ((separator * separator) ^ n)
          (strictJointCylinderCompletedInner hcoupling hle vector vector))
        (strictJointCylinderCompletedInner hcoupling hle test test)) := by
  let propagated :=
    strictJointCylinderCompletedTwoStepPower hcoupling hle n vector
  have hcs := strictJointCylinderCompletedInner_cauchy_schwarz
    hcoupling hle propagated test
  have hnorm :=
    strictJointCylinderCompletedTwoStepPower_norm_gap_of_form_gap
      hcoupling hle gap n vector horthogonal
  have htestNonnegative :=
    strictJointCylinderCompletedInner_self_nonneg hcoupling hle test
  have hmul := CReal.RCmul_mono_nonnegative_left_local
    htestNonnegative hnorm
  rw [CReal.RCmul_comm
        (strictJointCylinderCompletedInner hcoupling hle test test),
      CReal.RCmul_comm
        (strictJointCylinderCompletedInner hcoupling hle test test)] at hmul
  exact CReal.RCle_trans hcs hmul

#print axioms strictJointCylinderStageTimeTranslate_midpoint
#print axioms cauchyPairingLimit_timeTranslate_midpoint
#print axioms strictJointCylinderCompletedTimeTranslate_midpoint
#print axioms strictJointCylinderCompletedInner_twoStep_midpoint
#print axioms strictJointCylinderCompletedTwoStepForm_cauchy_schwarz
#print axioms CReal.RCle_of_mul_self_le_mul_right_nonnegative
#print axioms CReal.RCmul_mono_nonnegative_left_local
#print axioms strictJointCylinderCompletedTwoStepTransfer_square_form_gap_of_form_gap
#print axioms strictJointCylinderCompletedTwoStepTransfer_norm_gap_of_form_gap
#print axioms anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
#print axioms strictJointCylinderCompletedTwoStepPower_norm_gap_of_form_gap
#print axioms anchorDecoratedDoubledTimeRate_completed_power_norm_decay
#print axioms strictJointCylinderCompletedTwoStepPower_matrixCoefficientSq_decay_of_form_gap

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
