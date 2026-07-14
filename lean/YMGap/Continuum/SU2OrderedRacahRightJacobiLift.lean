/-
# Lifting the reduced right Jacobi row through one inner contraction

The positive-inner-order induction step requires more than the reduced row at
one coordinate: `omegaLiftSplit` samples the reduced row at two neighbouring
coordinates.  This module records the exact coordinate-family hypothesis and
uses the linearity of the split Omega lift to recover the three original
carrier slots.
-/

import YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
import YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahRightJacobiLift

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
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def liftThreeLHS : PolyExpr :=
  .add
    (.mul (.var 0)
      (.add
        (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 6)))
        (.mul (.var 4) (.var 7))))
    (.neg
      (.mul (.var 1)
        (.add
          (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 9)))
          (.mul (.var 4) (.var 10)))))

private def liftThreeRHS : PolyExpr :=
  .add
    (.add
      (.mul (.var 2)
        (.add (.mul (.var 0) (.var 5))
          (.neg (.mul (.var 1) (.var 8)))))
      (.mul (.var 3)
        (.add (.mul (.var 0) (.var 6))
          (.neg (.mul (.var 1) (.var 9))))))
    (.mul (.var 4)
      (.add (.mul (.var 0) (.var 7))
        (.neg (.mul (.var 1) (.var 10)))))

private theorem liftThree_normal :
    normalize liftThreeLHS = normalize liftThreeRHS := by
  decide

/-- The split Omega lift preserves a three-term linear combination. -/
theorem omegaLiftSplit_three_term (b c : Nat)
    (A B C : Q') (x y z : Nat → Nat → Nat → Q')
    (i j l : Nat) :
    omegaLiftSplit b c
        (fun u v w => A * x u v w + B * y u v w + C * z u v w)
        i j l ≈
      A * omegaLiftSplit b c x i j l +
        B * omegaLiftSplit b c y i j l +
        C * omegaLiftSplit b c z i j l := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then Q'.ofNat j * Q'.ofNat (c - l) else
    if r = 1 then Q'.ofNat (b - j) * Q'.ofNat l else
    if r = 2 then A else if r = 3 then B else if r = 4 then C else
    if r = 5 then x i (j - 1) l else
    if r = 6 then y i (j - 1) l else
    if r = 7 then z i (j - 1) l else
    if r = 8 then x i j (l - 1) else
    if r = 9 then y i j (l - 1) else z i j (l - 1)
  have h := poly_identity_of_normal_eq liftThreeLHS liftThreeRHS
    liftThree_normal ρ
  simpa [liftThreeLHS, liftThreeRHS, eval, ρ, omegaLiftSplit] using h

/-- Pointwise equivalent arrays have equivalent split Omega lifts. -/
theorem omegaLiftSplit_congr (b c : Nat)
    (x y : Nat → Nat → Nat → Q')
    (hxy : ∀ u v w, x u v w ≈ y u v w) (i j l : Nat) :
    omegaLiftSplit b c x i j l ≈ omegaLiftSplit b c y i j l := by
  unfold omegaLiftSplit
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ (hxy i (j - 1) l))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ (hxy i j (l - 1))))

/-- A coordinate family of reduced-label Jacobi rows lifts through one common
inner contraction to the reduced-coefficient row in the three original
carrier slots.  The strict inequality `1 < q.p` is exactly the branch on
which the reduced row has a lower neighbour. -/
theorem liftedReducedRightTransposeJacobiAt_of_reduced_family
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p) (i j l s : Nat)
    (hreduced : ∀ u v w,
      RightTransposeJacobiAt
        (reducePositiveInnerRightChannel qm hm)
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp hpp) u v w s) :
    LiftedReducedRightTransposeJacobiAt qm q qp i j l s := by
  have hrow : ∀ u v w,
      firstPairExchange3 a (b - 1) (peeledRightCoefficient q s) u v w ≈
        reducedLowerCoefficient a b c d q.p *
            peeledRightCoefficient qm s u v w +
          jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
            peeledRightCoefficient q s u v w +
          jacobiBackward a (b - 1) (c - 1) d q.p *
            peeledRightCoefficient qp s u v w := by
    intro u v w
    have h := hreduced u v w
    unfold RightTransposeJacobiAt at h
    have hsub : (q.p - 1) - 1 = q.p - 2 := by omega
    have hsucc : q.p - 1 + 1 = q.p := by omega
    simpa only [peeledRightCoefficient, reduced_intermediate_eq,
      reduced_inner_order_eq, hsub, hsucc, reducedLowerCoefficient,
      if_pos hp2] using h
  have hlift := omegaLiftSplit_congr b c
    (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s))
    (fun u v w =>
      reducedLowerCoefficient a b c d q.p *
          peeledRightCoefficient qm s u v w +
        jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
          peeledRightCoefficient q s u v w +
        jacobiBackward a (b - 1) (c - 1) d q.p *
          peeledRightCoefficient qp s u v w)
    hrow i j l
  have hlinear := omegaLiftSplit_three_term b c
    (reducedLowerCoefficient a b c d q.p)
    (jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1))
    (jacobiBackward a (b - 1) (c - 1) d q.p)
    (peeledRightCoefficient qm s) (peeledRightCoefficient q s)
    (peeledRightCoefficient qp s) i j l
  have hcarriers :
      reducedLowerCoefficient a b c d q.p *
            omegaLiftSplit b c (peeledRightCoefficient qm s) i j l +
          jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
            omegaLiftSplit b c (peeledRightCoefficient q s) i j l +
          jacobiBackward a (b - 1) (c - 1) d q.p *
            omegaLiftSplit b c (peeledRightCoefficient qp s) i j l ≈
        reducedLowerCoefficient a b c d q.p *
            triRight a b c d qm.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
            triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s +
          jacobiBackward a (b - 1) (c - 1) d q.p *
            triRight a b c d qp.intermediate
              (mono i) (mono j) (mono l) s := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight qm hm i j l s))
        (Q'.mul_eqv_congr_left _ _ _
          (peeled_omegaLiftSplit_eq_triRight q hp i j l s)))
      (Q'.mul_eqv_congr_left _ _ _
        (peeled_omegaLiftSplit_eq_triRight qp hpp i j l s))
  unfold LiftedReducedRightTransposeJacobiAt
  exact Q'.eqv_trans _ _ _ hlift
    (Q'.eqv_trans _ _ _ hlinear hcarriers)

end YMGap.Continuum.SU2OrderedRacahRightJacobiLift

#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiLift.omegaLiftSplit_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiLift.omegaLiftSplit_congr
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiLift.liftedReducedRightTransposeJacobiAt_of_reduced_family
