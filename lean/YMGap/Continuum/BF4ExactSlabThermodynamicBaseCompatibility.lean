/-
# Base-box compatibility of ORIGINAL thermodynamic plaquette means

The zero-lag bulk embedding changes the base presentation, not the centered
physical observable. At every later margin its polynomial is literally the
old polynomial at a later margin. The expectation sequence is therefore a
tail of the SAME sequence, so its constructed thermodynamic limit agrees.
No boundary-insensitivity or state-compatibility hypothesis is added.
-/

import YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def enlarge {base : Nat} (padding : Nat) (e : PlaquetteExpression base) : PlaquetteExpression (base+padding) :=
  bulkAtTime padding ⟨0, Nat.zero_lt_succ _⟩ e

theorem shiftedExpression_enlarge {base : Nat} (padding margin : Nat) (e : PlaquetteExpression base) :
    shiftedExpression margin (enlarge padding e) = shiftedExpression (padding+margin) e := by
  unfold shiftedExpression enlarge
  rw [evaluate_bulkAtTime]
  apply evaluate_congr
  intro id hi spin
  simp only [shiftedCharacter, bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1,
    Nat.sub_zero, shiftFace_comp, Nat.add_assoc]

theorem expressionMean_enlarge (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (padding margin : Nat) (e : PlaquetteExpression base) :
    expressionMean w hw0 hw1 (enlarge padding e) margin = expressionMean w hw0 hw1 e (padding+margin) := by
  unfold expressionMean
  rw [shiftedExpression_enlarge, Nat.add_assoc]

theorem meanSequence_enlarge {base : Nat} (padding margin : Nat) (e : PlaquetteExpression base) :
    meanSequence (enlarge padding e) margin = meanSequence e (padding+margin) :=
  expressionMean_enlarge nome nome_pos nome_lt_one padding margin e

theorem meanSequence_tail_converges {base : Nat} (padding : Nat) (e : PlaquetteExpression base) :
    ConvergesTo (fun margin => meanSequence e (padding+margin)) (meanLimit e) := by
  intro epsilon he
  obtain ⟨N, hN⟩ := meanLimit_converges e epsilon he
  exact ⟨N, fun margin hm => hN (padding+margin) (Nat.le_trans hm (Nat.le_add_left _ _))⟩

/-- Exact invariance under a changed base box; both limit objects were constructed. -/
theorem meanLimit_enlarge {base : Nat} (padding : Nat) (e : PlaquetteExpression base) :
    Equiv (meanLimit (enlarge padding e)) (meanLimit e) :=
  Equiv_of_limit_of_equal (fun margin => (meanSequence_enlarge padding margin e) ▸ Equiv.refl _)
    (meanLimit_converges (enlarge padding e)) (meanSequence_tail_converges padding e)

end YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.shiftedExpression_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.expressionMean_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.meanSequence_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.meanSequence_tail_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility.meanLimit_enlarge
