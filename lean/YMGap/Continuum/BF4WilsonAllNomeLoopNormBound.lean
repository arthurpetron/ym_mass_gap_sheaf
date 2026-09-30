/-
# A parameter-independent norm cap for fundamental Wilson loops

On the SAME literal-width all-nome completion, orthogonal centering cannot
increase the norm. The fundamental time-zero multiplier has squared-norm
cap 4 and creates the existing loop state from the normalized unit. Hence
every such centered loop has squared norm at most 4, independently of nome,
width, loop length and position. No lower bound or scaling survival follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeLoopNormBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
open YMGap.Continuum.BF4WilsonAllNomeCenteringPin (centeredPart_embed)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedInner_multiplier_bound)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum (completedMultiply_unitState)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem sub_le_self (a b : RC) (hb : RCnonneg b) :
    RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl a) (RCSignedPairBudget.neg_mono hb)
  have hzero : RCneg RCzero = RCzero :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => (by decide : Q'.eqv (-(0 : Q')) 0)))
  have hadd : RCadd a RCzero = a := by
    refine Quotient.inductionOn a ?_
    exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => QPoly.q_add_zero_eqv (A.approx n)))
  rw [hzero, hadd] at h
  exact h

/-- The already constructed orthogonal centering contracts squared norm. -/
theorem centeredPart_norm_le (x : V) :
    RCle (B (centeredPart hw0 hw1 x) (centeredPart hw0 hw1 x)) (B x x) := by
  rw [centeredPart_pairing_both,
    ← unitProjection_inner hw0 hw1 x x]
  exact sub_le_self _ _
    (completedInner_nonnegative hw0 hw1 (unitProjection hw0 hw1 x))

/-- No nome, width, or loop-size factor appears in this ceiling. -/
theorem loop_norm_le_four (L : SourceLoop width) :
    RCle (B (embed hw0 hw1 (loopState L)) (embed hw0 hw1 (loopState L)))
      (Rq 4) := by
  have h := completedInner_multiplier_bound hw0 hw1 L 1 (unitState hw0 hw1 width)
  rw [completedMultiply_unitState, unitState_norm_one] at h
  have hcap : RCmul
      (Rq (QuaternionHaarPolynomialSquareBound.characterBound 1)) (Rq 1) = Rq 4 := by
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => (by decide : Q'.eqv
        (QuaternionHaarPolynomialSquareBound.characterBound 1 * 1) 4)))
  rw [hcap] at h
  exact h

/-- Uniform for ALL admitted nomes and widths and ALL fundamental source loops,
including changing-size square loops. This is an upper bound, not survival. -/
theorem centered_loop_norm_le_four (L : SourceLoop width) :
    RCle (B (centeredVector hw0 hw1 (loopState L))
      (centeredVector hw0 hw1 (loopState L))) (Rq 4) := by
  have h := centeredPart_norm_le hw0 hw1 (embed hw0 hw1 (loopState L))
  rw [centeredPart_embed] at h
  exact RCle_trans h (loop_norm_le_four hw0 hw1 L)

#print axioms centeredPart_norm_le
#print axioms loop_norm_le_four
#print axioms centered_loop_norm_le_four

end YMGap.Continuum.BF4WilsonAllNomeLoopNormBound
