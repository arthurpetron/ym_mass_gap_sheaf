/-
# Endpoint lift for the first positive inner order

When the original inner order is one, peeling produces order zero.  There is
then no reduced lower neighbour: using the ordinary three-carrier formula
would make natural subtraction alias that missing neighbour with order zero.
This module gives the exact two-carrier endpoint proposition and lifts a
coordinate family of such rows through the split Omega recurrence.
-/

import YMGap.Continuum.SU2OrderedRacahRightJacobiLift

namespace YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift

local infix:50 " ≈ " => Q'.eqv

/-- The two-carrier transpose-Jacobi row at inner order zero.  This separate
type is necessary because the generic expression `p - 1` would alias the
missing lower neighbour with order zero. -/
def RightEndpointTransposeJacobiAt {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Prop :=
  firstPairExchange3 a b
      (fun u v w => triRight a b c d q.intermediate
        (mono u) (mono v) (mono w) s) i j l ≈
    jacobiDiagonal a b c d q.p *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s +
      jacobiBackward a b c d (q.p + 1) *
        triRight a b c d qp.intermediate
          (mono i) (mono j) (mono l) s

private theorem insert_zero_lower (X Y Z : Q') :
    Y + Z ≈ (0 : Q') * X + Y + Z := by
  have hzero : (0 : Q') * X + Y ≈ Y :=
    Q'.eqv_trans _ (0 + Y) _
      (Q'.add_eqv_congr' (Q'.zero_mul_eqv X) (Q'.eqv_refl Y))
      (Q'.eqv_of_eq (Q'.zero_add' Y))
  exact Q'.eqv_symm
    (Q'.add_eqv_congr' hzero (Q'.eqv_refl Z))

private theorem zero_carrier_change (X Y : Q') :
    (0 : Q') * X ≈ 0 * Y :=
  Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv X)
    (Q'.eqv_symm (Q'.zero_mul_eqv Y))

/-- At original inner order one, a coordinate family of exact reduced
endpoint rows lifts to the three-slot reduced-coefficient row.  The original
lower carrier is present only syntactically and its coefficient is proved
zero, so no positivity or peeling hypothesis is imposed on it. -/
theorem liftedReducedRightTransposeJacobiAt_of_endpoint_family
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hpp : 0 < qp.p) (hp1 : q.p = 1)
    (i j l s : Nat)
    (hendpoint : ∀ u v w,
      RightEndpointTransposeJacobiAt
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp hpp) u v w s) :
    LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hrowTwo : ∀ u v w,
      firstPairExchange3 a (b - 1) (peeledRightCoefficient q s) u v w ≈
        jacobiDiagonal a (b - 1) (c - 1) d 0 *
            peeledRightCoefficient q s u v w +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            peeledRightCoefficient qp s u v w := by
    intro u v w
    have h := hendpoint u v w
    unfold RightEndpointTransposeJacobiAt at h
    simpa only [peeledRightCoefficient, reduced_intermediate_eq,
      reduced_inner_order_eq, hp1, Nat.reduceSubDiff, Nat.zero_add] using h
  have hrow : ∀ u v w,
      firstPairExchange3 a (b - 1) (peeledRightCoefficient q s) u v w ≈
        (0 : Q') * peeledRightCoefficient qm s u v w +
          jacobiDiagonal a (b - 1) (c - 1) d 0 *
            peeledRightCoefficient q s u v w +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            peeledRightCoefficient qp s u v w := by
    intro u v w
    exact Q'.eqv_trans _ _ _ (hrowTwo u v w)
      (insert_zero_lower
        (peeledRightCoefficient qm s u v w)
        (jacobiDiagonal a (b - 1) (c - 1) d 0 *
          peeledRightCoefficient q s u v w)
        (jacobiBackward a (b - 1) (c - 1) d 1 *
          peeledRightCoefficient qp s u v w))
  have hlift := omegaLiftSplit_congr b c
    (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s))
    (fun u v w =>
      (0 : Q') * peeledRightCoefficient qm s u v w +
        jacobiDiagonal a (b - 1) (c - 1) d 0 *
          peeledRightCoefficient q s u v w +
        jacobiBackward a (b - 1) (c - 1) d 1 *
          peeledRightCoefficient qp s u v w)
    hrow i j l
  have hlinear := omegaLiftSplit_three_term b c
    (0 : Q') (jacobiDiagonal a (b - 1) (c - 1) d 0)
    (jacobiBackward a (b - 1) (c - 1) d 1)
    (peeledRightCoefficient qm s) (peeledRightCoefficient q s)
    (peeledRightCoefficient qp s) i j l
  have hcarriers :
      (0 : Q') * omegaLiftSplit b c (peeledRightCoefficient qm s) i j l +
          jacobiDiagonal a (b - 1) (c - 1) d 0 *
            omegaLiftSplit b c (peeledRightCoefficient q s) i j l +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            omegaLiftSplit b c (peeledRightCoefficient qp s) i j l ≈
        (0 : Q') *
            triRight a b c d qm.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiDiagonal a (b - 1) (c - 1) d 0 *
            triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiBackward a (b - 1) (c - 1) d 1 *
            triRight a b c d qp.intermediate
              (mono i) (mono j) (mono l) s := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (zero_carrier_change _ _)
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight q hp i j l s)))
      (Q'.mul_eqv_congr_left _ _ _
        (peeled_omegaLiftSplit_eq_triRight qp hpp i j l s))
  unfold LiftedReducedRightTransposeJacobiAt
  simp only [hp1, reducedLowerCoefficient, Nat.reduceLT, if_false,
    Nat.reduceSubDiff]
  exact Q'.eqv_trans _ _ _ hlift
    (Q'.eqv_trans _ _ _ hlinear hcarriers)

end YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift

#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift.RightEndpointTransposeJacobiAt
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift.liftedReducedRightTransposeJacobiAt_of_endpoint_family
