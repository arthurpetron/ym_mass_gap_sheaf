/-
# The scalar dual test on the EXISTING thermodynamic OS quotient

Lower-observable carrier equality already implies equality of every original
OS pairing. The previously proved finite null descent therefore compares
scalar tests without a new upper-reflection recoding. Common-volume tails
then prove independence of the thermodynamic presentation. The limiting test
descends through the existing semantic observable and OS null quotients.

The coefficient-one difference bound supplies explicit scalar continuity in
the original squared distance. No representative is selected. This is one
bounded test, not a separating family or an actual time-transfer identity.
-/

import YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest
import YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity

namespace YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit
open YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The existing finite OS radical avoids any new reflection recoding. -/
theorem finite_lower_congr {half : Nat} {e f : PlaquetteExpression half}
    (h : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (lower e) (lower f)) :
    Equiv (testLimit nome nome_pos nome_lt_one (bulkScalar half) e)
      (testLimit nome nome_pos nome_lt_one (bulkScalar half) f) := by
  apply bulkScalar_null_congr nome nome_pos nome_lt_one
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
  apply (BF4ExactSlabPlaquetteNullQuotient.null_iff_pairing nome nome_pos nome_lt_one e f).mpr
  intro g
  exact Quotient.sound (form_lower_congr nome nome_pos nome_lt_one h (HaarCarrierEqv.refl _ (lower g)))

def testAt (p : Presentation) (volume : Nat) (hp : p.base ≤ volume) : CReal :=
  testLimit nome nome_pos nome_lt_one (bulkScalar volume) (atBase p volume hp)

theorem testAt_sequence_pin (p : Presentation) (margin : Nat) :
    Equiv (testAt p (p.base+margin) (Nat.le_add_right _ _)) (meanSequence p.expression margin) := by
  apply finite_lower_congr
  rw [lower_atBase, lower_enlarge]
  unfold polynomial
  rw [Nat.add_sub_cancel_left]
  exact HaarCarrierEqv.refl _ _

theorem testAt_tail_pin (p : Presentation) (cutoff : Nat) (hp : p.base ≤ cutoff) (margin : Nat) :
    Equiv (testAt p (cutoff+margin) (by omega)) (meanSequence p.expression ((cutoff-p.base)+margin)) := by
  have h := testAt_sequence_pin p ((cutoff-p.base)+margin)
  have hv : p.base+((cutoff-p.base)+margin) = cutoff+margin := by omega
  simpa only [hv] using h

theorem testAt_converges (p : Presentation) (cutoff : Nat) (hp : p.base ≤ cutoff) :
    ConvergesTo (fun margin => testAt p (cutoff+margin) (by omega)) (meanLimit p.expression) := by
  apply TrigAddCReal.convergesTo_congr_seq (fun m => (testAt_tail_pin p cutoff hp m).symm)
  intro epsilon he
  obtain ⟨N, hN⟩ := meanLimit_converges p.expression epsilon he
  exact ⟨N, fun n hn => hN ((cutoff-p.base)+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩

theorem meanLimit_same {p q : Presentation} (h : SameObservable p q) :
    Equiv (meanLimit p.expression) (meanLimit q.expression) := by
  apply Equiv_of_limit_of_equal
    (aSeq := fun m => testAt p (h.cutoff+m) (by have := h.left_le; omega))
    (bSeq := fun m => testAt q (h.cutoff+m) (by have := h.right_le; omega))
  · intro m
    apply finite_lower_congr
    rw [lower_atBase, lower_atBase]
    exact h.equal (h.cutoff+m) (Nat.le_add_right _ _)
  · exact testAt_converges p h.cutoff h.left_le
  · exact testAt_converges q h.cutoff h.right_le

theorem meanLimit_atBase (p : Presentation) (base : Nat) (hp : p.base ≤ base) :
    Equiv (meanLimit (atBase p base hp)) (meanLimit p.expression) :=
  meanLimit_same (p := ⟨base, atBase p base hp⟩) (q := p) (SameObservable.rebase p base hp)

/-- The existing state-independent observable quotient, not a new test algebra. -/
def observableTest : Observable → RC :=
  Quotient.lift (fun p => Quotient.mk crealSetoid (meanLimit p.expression))
    (fun _ _ ⟨h⟩ => Quotient.sound (meanLimit_same h))

theorem observableTest_embed (p : Presentation) :
    observableTest (embed p) = Quotient.mk crealSetoid (meanLimit p.expression) := rfl

def observableTestRepresentative (p : Presentation) :
    Σ' r : CReal, QCauchy r.approx ×' (observableTest (embed p) = Quotient.mk crealSetoid r) :=
  ⟨meanLimit p.expression, meanLimitCauchy p.expression, rfl⟩

theorem observableTest_add (x y : Observable) :
    observableTest (qadd x y) = RCadd (observableTest x) (observableTest y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply Quotient.sound
  exact (meanLimit_add (atBase p (p.base+q.base) (Nat.le_add_right _ _))
    (atBase q (p.base+q.base) (Nat.le_add_left _ _))).trans
    ((CReal.add_congr_left (meanLimit_atBase p _ _)).trans (CReal.add_congr_right (meanLimit_atBase q _ _)))

theorem observableTest_smul (c : Q') (x : Observable) :
    observableTest (qsmul c x) = RCmul (Quotient.mk crealSetoid (ofQ' c)) (observableTest x) := by
  refine Quotient.inductionOn x ?_
  intro p
  exact Quotient.sound (meanLimit_smul c p.expression)

theorem observableTest_bound (x : Observable) :
    RCle (RCmul (observableTest x) (observableTest x)) (pairing x x) := by
  refine Quotient.inductionOn x ?_
  intro p
  change RCle (RCmul (observableTest (embed p)) (observableTest (embed p))) (pairing (embed p) (embed p))
  rw [observableTest_embed, pairing_sameBase]
  exact meanLimit_bound p.expression

private theorem rc_minusOne_mul (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' (-1))) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

theorem observableTest_sub (x y : Observable) :
    observableTest (subtract x y) = RCsub (observableTest x) (observableTest y) := by
  unfold subtract
  rw [observableTest_add, observableTest_smul, rc_minusOne_mul]
  rfl

theorem observableTest_distance_bound (x y : Observable) :
    RCle (RCmul (RCsub (observableTest x) (observableTest y)) (RCsub (observableTest x) (observableTest y)))
      (pairing (subtract x y) (subtract x y)) := by
  have h := observableTest_bound (subtract x y)
  rwa [observableTest_sub] at h

private theorem rc_square_zero (a : RC) (h : RCle (RCmul a a) RCzero) : a = RCzero := by
  revert h
  refine Quotient.inductionOn a ?_
  intro A h
  apply Quotient.sound
  intro epsilon he
  obtain ⟨N, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨N, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

theorem observableTest_null {x y : Observable} (h : Null x y) : observableTest x = observableTest y := by
  have hb := observableTest_distance_bound x y
  change pairing (subtract x y) (subtract x y) = RCzero at h
  rw [h] at hb
  have hz := rc_square_zero _ hb
  revert hz
  refine Quotient.inductionOn₂ (observableTest x) (observableTest y) ?_
  intro A B hz
  exact Quotient.sound (CReal.Equiv_of_sub_eqv_zero (Quotient.exact hz))

/-- A constructed scalar test on the EXISTING positive-definite OS quotient. -/
def osTest : Carrier → RC := Quotient.lift observableTest (fun _ _ h => observableTest_null h)

theorem osTest_project (x : Observable) : osTest (project x) = observableTest x := rfl

theorem osTest_bound (x : Carrier) : RCle (RCmul (osTest x) (osTest x)) (inner x x) := by
  refine Quotient.inductionOn x ?_
  exact observableTest_bound

theorem presentedTest_distance_bound (p q : Presentation) :
    leEv (CReal.mul (CReal.sub (meanLimit p.expression) (meanLimit q.expression))
      (CReal.sub (meanLimit p.expression) (meanLimit q.expression))) (distSq p q) := by
  have h := observableTest_distance_bound (embed p) (embed q)
  rw [← distSq_pin, observableTest_embed, observableTest_embed] at h
  exact h

/-- Squared-distance tolerance for scalar accuracy epsilon; no root oracle. -/
def testTolerance (epsilon : Q') : Q' := HalfPow.half * (epsilon*epsilon)

theorem testTolerance_pos {epsilon : Q'} (he : (0 : Q') < epsilon) : (0 : Q') < testTolerance epsilon :=
  ExpNeg.half_mul_pos _ (Q'.mul_pos he he)

theorem presentedTest_close (p q : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon)
    (h : leEv (distSq p q) (ofQ' (testTolerance epsilon))) :
    leRat (CReal.sub (meanLimit p.expression) (meanLimit q.expression)) epsilon ∧
    leRat (CReal.sub (meanLimit q.expression) (meanLimit p.expression)) epsilon := by
  have hb := BF4ExactSlabPlaquettePairingContinuity.signed_small_of_square _ epsilon he
    (leEv_trans (presentedTest_distance_bound p q) h)
  exact ⟨hb.1, CReal.leRat_of_equiv
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.neg_sub_eqv _ _))) hb.2⟩

end YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.finite_lower_congr
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testAt
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testAt_sequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testAt_tail_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testAt_converges
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.meanLimit_same
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.meanLimit_atBase
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_embed
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTestRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_add
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_smul
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_sub
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.observableTest_null
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.osTest
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.osTest_project
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.osTest_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.presentedTest_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testTolerance
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.testTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest.presentedTest_close
