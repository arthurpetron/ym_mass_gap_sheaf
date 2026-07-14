/-
# Recovering the Omega correction from two Jacobi rows

The standard induction theorem adds the lifted peeled Jacobi row to the
Omega correction and obtains the original Jacobi row.  Since all identities
live in exact rational equivalence, the implication is reversible: an
original row together with its lifted peeled row determines the correction.
This is the bridge from coordinate-family induction hypotheses to the
coupled correction family exposed by the outer-height recurrence fence.
-/

import YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahCorrectionConverse

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift
open YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def cancelLHS : PolyExpr :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 0))

private def cancelRHS : PolyExpr := .var 1

private theorem cancel_normal :
    normalize cancelLHS = normalize cancelRHS := by
  decide

private theorem add_add_neg_cancel (R C : Q') : (R + C) + -R ≈ C := by
  let ρ : Nat → Q' := fun r => if r = 0 then R else C
  have h := poly_identity_of_normal_eq cancelLHS cancelRHS cancel_normal ρ
  simpa [cancelLHS, cancelRHS, eval, ρ] using h

/-- Additive cancellation modulo rational equivalence, stated without any
choice of normalized representatives. -/
private theorem correction_eqv_of_recombined
    (R C R' C' : Q') (hsum : R + C ≈ R' + C') (hR : R ≈ R') :
    C ≈ C' := by
  have hshift : (R + C) + -R ≈ (R' + C') + -R' :=
    Q'.add_eqv_congr' hsum (Q'.neg_eqv_congr _ _ hR)
  refine Q'.eqv_trans _ ((R + C) + -R) _
    (Q'.eqv_symm (add_add_neg_cancel R C)) ?_
  refine Q'.eqv_trans _ ((R' + C') + -R') _ hshift ?_
  exact add_add_neg_cancel R' C'

private def recombineLHS : PolyExpr :=
  .add
    (.add (.add (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 7)))
      (.mul (.var 2) (.var 8)))
    (.add
      (.add
        (.mul (.add (.var 3) (.neg (.var 0))) (.var 6))
        (.mul (.add (.var 4) (.neg (.var 1))) (.var 7)))
      (.mul (.add (.var 5) (.neg (.var 2))) (.var 8)))

private def recombineRHS : PolyExpr :=
  .add (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 7)))
    (.mul (.var 5) (.var 8))

private theorem recombine_normal :
    normalize recombineLHS = normalize recombineRHS := by
  decide

private theorem three_slot_difference_recombine
    (RL RD RU OL OD OU M C P : Q') :
    ((RL * M + RD * C + RU * P) +
        ((OL + -RL) * M + (OD + -RD) * C + (OU + -RU) * P)) ≈
      OL * M + OD * C + OU * P := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then RL else if r = 1 then RD else if r = 2 then RU else
    if r = 3 then OL else if r = 4 then OD else if r = 5 then OU else
    if r = 6 then M else if r = 7 then C else P
  have h := poly_identity_of_normal_eq recombineLHS recombineRHS
    recombine_normal ρ
  simpa [recombineLHS, recombineRHS, eval, ρ] using h

/-- Reduced coefficients plus their defining correction differences are the
original Jacobi coefficients in all three carrier slots. -/
private theorem reduced_plus_correction_recombine
    (a b c d p : Nat) (M C P : Q') :
    (reducedLowerCoefficient a b c d p * M +
          jacobiDiagonal a (b - 1) (c - 1) d (p - 1) * C +
          jacobiBackward a (b - 1) (c - 1) d p * P) +
        (omegaCorrectionLowerCoefficient a b c d p * M +
          omegaCorrectionDiagonalCoefficient a b c d p * C +
          omegaCorrectionUpperCoefficient a b c d p * P) ≈
      jacobiForward a b c d (p - 1) * M +
        jacobiDiagonal a b c d p * C +
        jacobiBackward a b c d (p + 1) * P := by
  simpa only [omegaCorrectionLowerCoefficient,
    omegaCorrectionDiagonalCoefficient, omegaCorrectionUpperCoefficient] using
      three_slot_difference_recombine
        (reducedLowerCoefficient a b c d p)
        (jacobiDiagonal a (b - 1) (c - 1) d (p - 1))
        (jacobiBackward a (b - 1) (c - 1) d p)
        (jacobiForward a b c d (p - 1))
        (jacobiDiagonal a b c d p)
        (jacobiBackward a b c d (p + 1)) M C P

/-- **Converse Jacobi induction.**  If the original transpose-Jacobi row and
the lifted peeled row are both known, their exact difference is the required
three-carrier Omega correction. -/
theorem omegaCorrectionThreeCarrierAt_of_right_and_lifted_reduced
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat) (hjb : j ≤ b)
    (hright : RightTransposeJacobiAt qm q qp i j l s)
    (hreduced : LiftedReducedRightTransposeJacobiAt qm q qp i j l s) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s := by
  let M := triRight a b c d qm.intermediate
    (mono i) (mono j) (mono l) s
  let C := triRight a b c d q.intermediate
    (mono i) (mono j) (mono l) s
  let P := triRight a b c d qp.intermediate
    (mono i) (mono j) (mono l) s
  let R := reducedLowerCoefficient a b c d q.p * M +
      jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) * C +
      jacobiBackward a (b - 1) (c - 1) d q.p * P
  let K := omegaCorrectionLowerCoefficient a b c d q.p * M +
      omegaCorrectionDiagonalCoefficient a b c d q.p * C +
      omegaCorrectionUpperCoefficient a b c d q.p * P
  let O := jacobiForward a b c d (q.p - 1) * M +
      jacobiDiagonal a b c d q.p * C +
      jacobiBackward a b c d (q.p + 1) * P
  let L := firstPairExchange3 a b
    (fun u v w => triRight a b c d q.intermediate
      (mono u) (mono v) (mono w) s) i j l
  let D := omegaLiftSplit b c
    (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s)) i j l
  let E := triRightOmegaCorrection q i j l s
  have hstep : L ≈ D + E := by
    simpa only [L, D, E] using
      triRight_firstPairExchange_induction_step q hp i j l s hjb
  have hright' : L ≈ O := by
    simpa only [RightTransposeJacobiAt, L, O, M, C, P] using hright
  have hreduced' : D ≈ R := by
    simpa only [LiftedReducedRightTransposeJacobiAt, D, R, M, C, P] using
      hreduced
  have hrecombine : R + K ≈ O := by
    simpa only [R, K, O] using
      reduced_plus_correction_recombine a b c d q.p M C P
  have hsum : R + E ≈ R + K :=
    Q'.eqv_trans _ (D + E) _
      (Q'.add_eqv_congr_right _ _ E (Q'.eqv_symm hreduced'))
      (Q'.eqv_trans _ L _ (Q'.eqv_symm hstep)
        (Q'.eqv_trans _ O _ hright' (Q'.eqv_symm hrecombine)))
  have hcorrection : E ≈ K :=
    correction_eqv_of_recombined R E R K hsum (Q'.eqv_refl R)
  simpa only [OmegaCorrectionThreeCarrierAt, E, K, M, C, P] using hcorrection

/-- Family form of the converse.  This is the mutually inductive closure
needed by the shifted-label mechanism: a full original Jacobi family and its
peeled lifted family provide the entire higher-height correction family. -/
theorem omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_and_lifted
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (hright : RightTransposeJacobiFullCoordinateFamily qm q qp)
    (hlifted : ∀ i j l s, j ≤ b →
      LiftedReducedRightTransposeJacobiAt qm q qp i j l s) :
    OmegaCorrectionHigherHeightCoordinateFamily qm q qp := by
  intro i j l s _ _ hjb
  exact omegaCorrectionThreeCarrierAt_of_right_and_lifted_reduced
    qm q qp hp i j l s hjb (hright i j l s) (hlifted i j l s hjb)

/-- Closed mutually inductive form: the lifted premise itself follows from a
full coordinate family after the common inner peel.  Thus correction descent
needs only full Jacobi families at the outer-shifted labels and at their
strictly smaller inner peels. -/
theorem omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_families
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p)
    (hright : RightTransposeJacobiFullCoordinateFamily qm q qp)
    (hreduced : RightTransposeJacobiFullCoordinateFamily
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp)) :
    OmegaCorrectionHigherHeightCoordinateFamily qm q qp := by
  apply omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_and_lifted
    qm q qp hp hright
  intro i j l s _
  apply liftedReducedRightTransposeJacobiAt_of_reduced_family
    qm q qp hm hp hpp hp2 i j l s
  intro u v w
  exact hreduced u v w s

end YMGap.Continuum.SU2OrderedRacahCorrectionConverse

#print axioms YMGap.Continuum.SU2OrderedRacahCorrectionConverse.omegaCorrectionThreeCarrierAt_of_right_and_lifted_reduced
#print axioms YMGap.Continuum.SU2OrderedRacahCorrectionConverse.omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_and_lifted
#print axioms YMGap.Continuum.SU2OrderedRacahCorrectionConverse.omegaCorrectionHigherHeightCoordinateFamily_of_jacobi_families
