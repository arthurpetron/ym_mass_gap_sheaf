/-
# Height-one coordinate-family closure and the higher-height residual

The transpose-Jacobi induction consumes a complete coordinate family on the
three peeled channels.  This module packages the strict height-one theorem as
a family and records the exact reusable induction step for higher correction
heights.  Its sole new mathematical input is explicitly named as the
higher-height Omega correction family.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation

namespace YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift
open YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation

/-- The coordinate-family invariant required by the split-Omega lift. -/
def RightTransposeJacobiFullCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s, RightTransposeJacobiAt qm q qp i j l s

/-- The complete strict-bulk height-one subfamily, with precisely the
hypotheses of the normalized residual certificate. -/
def RightTransposeJacobiStrictHeightOneFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s,
    s + q.r + q.p = i + j + l →
    3 ≤ j → 3 ≤ l →
    j + l = q.p + 1 →
    q.p + 2 ≤ b → q.p + 2 ≤ c →
    4 ≤ q.r → q.r + 1 ≤ i →
    i + 1 ≤ a → q.r + 2 ≤ q.intermediate →
    RightTransposeJacobiAt qm q qp i j l s

/-- A full coordinate family on the three peeled channels propagates to the
entire strict height-one subfamily on the original labels. -/
theorem strictHeightOneFamily_of_reduced_fullCoordinateFamily
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (hreduced : ∀ (hm : 0 < qm.p) (hpp : 0 < qp.p),
      RightTransposeJacobiFullCoordinateFamily
        (reducePositiveInnerRightChannel qm hm)
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp hpp)) :
    RightTransposeJacobiStrictHeightOneFamily qm q qp := by
  intro i j l s hshell hj hl hheight hpb hpc hr hri hia hrn
  have hm : 0 < qm.p := by omega
  have hpp : 0 < qp.p := by omega
  apply rightTransposeJacobiAt_height_one_strict_bulk_of_reduced_family
    qm q qp hp hprev hnext i j l s hshell hj hl hheight hpb hpc
      hr hri hia hrn
  intro u v w
  exact hreduced hm hpp u v w s

/-- The genuinely missing correction input beyond the now-closed height-one
layer.  It contains exactly the on-shell coordinates of correction height at
least two that the denominator-free induction algebra can consume. -/
def OmegaCorrectionHigherHeightCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s,
    s + q.r + q.p = i + j + l →
    q.p + 2 ≤ j + l →
    j ≤ b →
    OmegaCorrectionThreeCarrierAt qm q qp i j l s

/-- The corresponding higher-height portion of the original transpose-Jacobi
coordinate family. -/
def RightTransposeJacobiHigherHeightCoordinateFamily {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop :=
  ∀ i j l s,
    s + q.r + q.p = i + j + l →
    q.p + 2 ≤ j + l →
    j ≤ b →
    RightTransposeJacobiAt qm q qp i j l s

/-- Reusable higher-height induction step.  Once the peeled full-coordinate
invariant and the named higher-height correction family are available, every
higher-height original row follows without any further normalization lemma. -/
theorem higherHeightFamily_of_reduced_fullCoordinateFamily_and_correction
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hm : 0 < qm.p) (hp : 0 < q.p) (hpp : 0 < qp.p)
    (hp2 : 1 < q.p)
    (hreduced : RightTransposeJacobiFullCoordinateFamily
      (reducePositiveInnerRightChannel qm hm)
      (reducePositiveInnerRightChannel q hp)
      (reducePositiveInnerRightChannel qp hpp))
    (hcorrection : OmegaCorrectionHigherHeightCoordinateFamily qm q qp) :
    RightTransposeJacobiHigherHeightCoordinateFamily qm q qp := by
  intro i j l s hshell hheight hjb
  have hlift := liftedReducedRightTransposeJacobiAt_of_reduced_family
    qm q qp hm hp hpp hp2 i j l s (by
      intro u v w
      exact hreduced u v w s)
  apply rightTransposeJacobiAt_of_lifted_reduced_and_correction
    qm q qp hp i j l s hjb hlift
  exact hcorrection i j l s hshell hheight hjb

end YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily.strictHeightOneFamily_of_reduced_fullCoordinateFamily
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCoordinateFamily.higherHeightFamily_of_reduced_fullCoordinateFamily_and_correction
