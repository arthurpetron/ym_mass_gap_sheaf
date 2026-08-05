/-
`FrontierCoreBPhysicalDischarge` -- inhabit the canonical finite-`s`
Core-B atom on the complete closed physical coupling interval.

`FusionUTuranFiniteS.finiteSMargin_of_trunc` already proves the genuinely
analytic part for every `0 < w <= 1/2`.  The only missing endpoint in that
family is `w = 0`.  There the upper off-centre autoconvolution vanishes term
by term, so the theta-margin inequality has zero left side and nonnegative
right side.  Splitting a nonnegative rational into its positive and
zero-equivalent cases therefore gives one uniform physical family

    forall w, 0 <= w -> w <= 1/2 -> FiniteSMargin w.

This physically discharges the `FrontierDAG.coreB` field type.  It does not
inhabit the other fields of `FrontierDAG`, and it does not prove the separate
forward cross-list bridge `FiniteSMargin w -> CrossRatioMonotone w`.
-/

import YMGap.Continuum.FusionUTuranFiniteS
import YMGap.Continuum.R1EvenCentreBound

namespace YMGap.Continuum.FrontierCoreBPhysicalDischarge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionUTuranFiniteS

/-! ## 1. The zero-equivalent endpoint -/

/-- If the coupling is rationally equivalent to zero, the upper off-centre
autoconvolution in every Core-B row vanishes exactly up to `Q'.eqv`. -/
theorem acN_upper_eqv_zero_of_eqv_zero
    {w : Q'} (hw : w.eqv 0) (s : Nat) :
    (acN w (s + 1) (s + 2)).eqv 0 := by
  unfold acN
  apply fsum_zero_below
  intro p hp
  have hk : 1 <= s + 2 - p := by omega
  have hc : (coeffW w (s + 2 - p)).eqv 0 :=
    R1EvenCentreBound.coeffW_zero hw (s + 2 - p) hk
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (coeffW w p) _ _ hc) ?_
  exact Q'.mul_zero_eqv _

/-- The finite-`s` theta margin at a nonnegative coupling equivalent to zero.
The adverse product vanishes, while the middle square is nonnegative. -/
def finiteSMargin_of_eqv_zero
    {w : Q'} (hw0 : (0 : Q') <= w) (hw : w.eqv 0) :
    FiniteSMargin w where
  margin := fun s => by
    have hupper : (acN w (s + 1) (s + 2)).eqv 0 :=
      acN_upper_eqv_zero_of_eqv_zero hw s
    have hadverse :
        (acN w (s + 1) s * acN w (s + 1) (s + 2)).eqv 0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (acN w (s + 1) s) _ _ hupper) ?_
      exact Q'.mul_zero_eqv _
    have hleft :
        (Q'.ofNat 40000 *
          (acN w (s + 1) s * acN w (s + 1) (s + 2))).eqv 0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 40000) _ _ hadverse) ?_
      exact Q'.mul_zero_eqv _
    have hmiddle : (0 : Q') <= acN w (s + 1) (s + 1) :=
      acN_nonneg hw0 (s + 1) (s + 1)
    have hright : (0 : Q') <=
        Q'.ofNat 22801 *
          (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)) :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ hmiddle hmiddle)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hright

/-! ## 2. Closed-interval physical family -/

/-- The canonical finite-`s` Core-B atom is inhabited at every coupling in
the complete physical interval `0 <= w <= 1/2`. -/
def finiteSMargin_physical
    {w : Q'} (hw0 : (0 : Q') <= w) (hwH : w <= wH) :
    FiniteSMargin w where
  margin := fun s => by
    rcases R1EvenCentreBound.pos_or_zero hw0 with hpos | hzero
    · exact (finiteSMargin_of_trunc hpos hwH).margin s
    · exact (finiteSMargin_of_eqv_zero hw0 hzero).margin s

/-- The same result exposed as the dependent family matching the physical
coupling quantifiers used by the guarded frontier bridges. -/
def finiteSMargin_physical_family :
    forall w : Q', (0 : Q') <= w -> w <= wH -> FiniteSMargin w :=
  fun _ hw0 hwH => finiteSMargin_physical hw0 hwH

#print axioms acN_upper_eqv_zero_of_eqv_zero
#print axioms finiteSMargin_of_eqv_zero
#print axioms finiteSMargin_physical
#print axioms finiteSMargin_physical_family

end YMGap.Continuum.FrontierCoreBPhysicalDischarge
