/-
# Constructive closure of the doubled-time mixed OS identity

The direct polarized Osterwalder--Schrader bilinear and the projected
ordinary joint centered quadratic have rational approximants differing by an
explicit half-power modulus.  The projected centered entries are, in turn,
the mixed signed entries of the translated reflection quadratic.  Finite
quadratic assembly therefore closes the doubled-time identity without adding
an axiom or a comparison hypothesis.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSQuadratic

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointSignedEntry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The projected ordinary-joint centered quadratic -/

/-- Finite CReal quadratic formed from the ordinary concatenated-root joint
centered limits that approximate the direct oriented OS entries. -/
def strictJointDoubledTimeMixedJointCenteredQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun left => listCRealSum
      (fun right => CReal.mul
        (CReal.ofQ'
          (vector.coefficient left * vector.coefficient right))
        (couplingParametricStrictJointCenteredLimit
          coupling hcoupling hle
          (strictJointDoubledTimeMixedJointPredicate
            vector.roots.length left right)
          (strictJointDoubledTimeMixedJointRoots_canonical shift vector)))
      (strictJointFingerprintSpace vector.roots.length))
    (strictJointFingerprintSpace vector.roots.length)

/-- Every approximation of the centered CReal quadratic is its literal
finite joint quadratic at the same stage. -/
theorem strictJointDoubledTimeMixedJointCenteredQuadratic_approx_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat}
    (vector : StrictJointCylinderVector base) :
    (strictJointDoubledTimeMixedJointCenteredQuadratic
        coupling hcoupling hle shift vector).approx stage ≈
      finiteJointQuadratic
        (strictJointFingerprintSpace vector.roots.length)
        vector.coefficient
        (fun left right =>
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + (shift + shift))
            (strictJointDoubledTimeMixedJointRoots shift vector)
            (strictJointDoubledTimeMixedJointPredicate
              vector.roots.length left right) stage) := by
  unfold strictJointDoubledTimeMixedJointCenteredQuadratic
    finiteJointQuadratic
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro left
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro right
  exact Q'.eqv_refl _

/-! ## 2. A derived global half-power comparison modulus -/

/-- Exact rational coefficient multiplying the common half-power entry
modulus after finite quadratic assembly. -/
def strictJointDoubledTimeMixedOSComparisonCoefficient
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : Q' :=
  coefficientPairL1
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient *
    strictJointConditionalCenteredCoefficient
      ((strictJointDoubledTimeMixedJointRoots shift vector).length +
        (strictJointDoubledTimeMixedJointRoots shift vector).length)

private theorem coefficientPairL1_nonnegative_local
    {State : Type} (states : List State) (coefficient : State → Q') :
    (0 : Q') ≤ coefficientPairL1 states coefficient := by
  unfold coefficientPairL1
  apply listQSum_nonnegative_on
  intro left hleft
  apply listQSum_nonnegative_on
  intro right hright
  exact Q'.abs_nonneg _

theorem strictJointDoubledTimeMixedOSComparisonCoefficient_nonnegative
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    (0 : Q') ≤
      strictJointDoubledTimeMixedOSComparisonCoefficient shift vector := by
  unfold strictJointDoubledTimeMixedOSComparisonCoefficient
  exact Q'.mul_nonneg _ _
    (coefficientPairL1_nonnegative_local
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient)
    (strictJointConditionalCenteredCoefficient_nonnegative
      ((strictJointDoubledTimeMixedJointRoots shift vector).length +
        (strictJointDoubledTimeMixedJointRoots shift vector).length))

/-- The direct mixed OS bilinear and the projected centered quadratic differ
by the finite coefficient norm times the derived entrywise half-power
modulus. -/
theorem strictJointDoubledTimeMixedOSBilinear_abs_sub_jointCentered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs
        ((strictJointDoubledTimeMixedOSBilinear
              hcoupling hle shift vector).approx stage -
          (strictJointDoubledTimeMixedJointCenteredQuadratic
              coupling hcoupling hle shift vector).approx stage) ≤
      strictJointDoubledTimeMixedOSComparisonCoefficient shift vector *
        HalfPow.half ^ stage := by
  let states := strictJointFingerprintSpace vector.roots.length
  let jointRoots := strictJointDoubledTimeMixedJointRoots shift vector
  let entryCoefficient := strictJointConditionalCenteredCoefficient
    (jointRoots.length + jointRoots.length)
  let orientedLaw : List Bool → List Bool → Q' := fun left right =>
    strictJointDoubledTimeMixedOSOrientedEntrySequence
      coupling hcoupling shift vector left right stage
  let centeredLaw : List Bool → List Bool → Q' := fun left right =>
    couplingParametricStrictJointCenteredSequence
      coupling hcoupling (base + (shift + shift)) jointRoots
      (strictJointDoubledTimeMixedJointPredicate
        vector.roots.length left right) stage
  have hbilinear :
      (strictJointDoubledTimeMixedOSBilinear
          hcoupling hle shift vector).approx stage ≈
        strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (strictJointDoubledTimeMixedSource shift vector)
          (strictJointDoubledTimeMixedTarget shift vector) stage := by
    simpa only [strictJointDoubledTimeMixedOSBilinear] using
      (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
        hcoupling hle
        (strictJointDoubledTimeMixedSource shift vector)
        (strictJointDoubledTimeMixedTarget shift vector)
        (stage := stage))
  have hentries :
      strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (strictJointDoubledTimeMixedSource shift vector)
          (strictJointDoubledTimeMixedTarget shift vector) stage ≈
        finiteJointQuadratic states vector.coefficient orientedLaw := by
    simpa only [states, orientedLaw] using
      (strictJointDoubledTimeMixedOSBilinearSequence_eqv_entries
        hcoupling hle shift vector stage)
  have hleft :
      (strictJointDoubledTimeMixedOSBilinear
          hcoupling hle shift vector).approx stage ≈
        finiteJointQuadratic states vector.coefficient orientedLaw :=
    Q'.eqv_trans _ _ _ hbilinear hentries
  have hright :
      (strictJointDoubledTimeMixedJointCenteredQuadratic
          coupling hcoupling hle shift vector).approx stage ≈
        finiteJointQuadratic states vector.coefficient centeredLaw := by
    simpa only [states, jointRoots, centeredLaw] using
      (strictJointDoubledTimeMixedJointCenteredQuadratic_approx_eqv
        hcoupling hle vector (shift := shift) (stage := stage))
  have hentry : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (orientedLaw left right + (-centeredLaw left right)) ≤
        entryCoefficient * HalfPow.half ^ stage := by
    intro left right hleftMem hrightMem
    simpa only [states, jointRoots, entryCoefficient, orientedLaw,
      centeredLaw] using
      (strictJointDoubledTimeMixedOSOrientedEntrySequence_abs_sub_jointCentered_le
        hcoupling hle shift vector left right stage)
  have hfinite :
      Q'.abs
          (finiteJointQuadratic states vector.coefficient orientedLaw +
            (-finiteJointQuadratic states vector.coefficient centeredLaw)) ≤
        coefficientPairL1 states vector.coefficient *
          (entryCoefficient * HalfPow.half ^ stage) :=
    finiteJointQuadratic_abs_sub_le_pairL1
      states vector.coefficient orientedLaw centeredLaw
      (entryCoefficient * HalfPow.half ^ stage) hentry
  have hdifference :
      (strictJointDoubledTimeMixedOSBilinear
            hcoupling hle shift vector).approx stage +
          (-(strictJointDoubledTimeMixedJointCenteredQuadratic
            coupling hcoupling hle shift vector).approx stage) ≈
        finiteJointQuadratic states vector.coefficient orientedLaw +
          (-finiteJointQuadratic states vector.coefficient centeredLaw) :=
    Q'.add_eqv_congr' hleft
      (Q'.neg_eqv_congr _ _ hright)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hfinite ?_)
  apply Q'.le_of_eqv
  simpa only [strictJointDoubledTimeMixedOSComparisonCoefficient,
    states, jointRoots, entryCoefficient] using
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficientPairL1 states vector.coefficient)
        entryCoefficient (HalfPow.half ^ stage)))

/-! ## 3. Constructive-real closure from the dyadic modulus -/

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

private theorem creal_equiv_of_abs_sub_le_half_pow
    (left right : CReal) (bound : Q')
    (hbound : (0 : Q') ≤ bound)
    (hpointwise : ∀ stage : Nat,
      Q'.abs (left.approx stage - right.approx stage) ≤
        bound * HalfPow.half ^ stage) :
    CReal.Equiv left right := by
  intro epsilon hepsilon
  let scaledTolerance :=
    epsilon * Q'.invSucc bound.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos bound.num.toNat)
  have hscaledFinal : bound * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat bound epsilon
      hbound (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled : bound * HalfPow.half ^ stage ≤
      bound * scaledTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hbound
  have habs :
      Q'.abs (left.approx stage - right.approx stage) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hpointwise stage)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

/-- The direct mixed OS bilinear is constructively equal to the projected
ordinary-joint centered quadratic. -/
theorem strictJointDoubledTimeMixedOSBilinear_equiv_jointCenteredQuadratic
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift vector)
      (strictJointDoubledTimeMixedJointCenteredQuadratic
        coupling hcoupling hle shift vector) :=
  creal_equiv_of_abs_sub_le_half_pow
    (strictJointDoubledTimeMixedOSBilinear hcoupling hle shift vector)
    (strictJointDoubledTimeMixedJointCenteredQuadratic
      coupling hcoupling hle shift vector)
    (strictJointDoubledTimeMixedOSComparisonCoefficient shift vector)
    (strictJointDoubledTimeMixedOSComparisonCoefficient_nonnegative
      shift vector)
    (strictJointDoubledTimeMixedOSBilinear_abs_sub_jointCentered_le
      hcoupling hle shift vector)

/-! ## 4. Entrywise signed recoding and terminal OS identity -/

private theorem creal_equiv_refl_local (value : CReal) :
    CReal.Equiv value value := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨Q'.add_le_self_of_nonneg _ _ hnonnegative,
    Q'.add_le_self_of_nonneg _ _ hnonnegative⟩

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  (CRealAlg.cmul_comm scalar left).trans
    ((CReal.mul_congr_left h).trans (CRealAlg.cmul_comm right scalar))

private theorem listCRealSum_congr_on_local
    {State : Type} {left right : State → CReal} :
    ∀ states : List State,
      (∀ state, state ∈ states → CReal.Equiv (left state) (right state)) →
      CReal.Equiv (listCRealSum left states) (listCRealSum right states)
  | [], _ => creal_equiv_refl_local CReal.czero
  | head :: tail, h => by
      have hhead : CReal.Equiv (left head) (right head) :=
        h head List.mem_cons_self
      have htail : CReal.Equiv
          (listCRealSum left tail) (listCRealSum right tail) :=
        listCRealSum_congr_on_local tail
          (fun state hstate => h state (List.mem_cons_of_mem head hstate))
      exact CReal.Equiv.trans
        (CReal.add_congr_left hhead)
        (CReal.add_congr_right htail)

/-- The projected ordinary-joint centered quadratic is exactly the mixed
signed quadratic already identified with the translated reflection
quadratic. -/
theorem strictJointDoubledTimeMixedJointCenteredQuadratic_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointDoubledTimeMixedJointCenteredQuadratic
        coupling hcoupling hle shift vector)
      (strictJointDoubledTimeMixedSignedQuadratic
        coupling hcoupling hle shift fixedStage hstage vector) := by
  unfold strictJointDoubledTimeMixedJointCenteredQuadratic
    strictJointDoubledTimeMixedSignedQuadratic
  apply listCRealSum_congr_on_local
  intro left hleft
  apply listCRealSum_congr_on_local
  intro right hright
  apply creal_mul_congr_right_local
  exact couplingParametricMixedJointCenteredLimit_equiv_mixedSigned
    hcoupling hle hstage vector left right

/-- The mixed signed quadratic equals the direct doubled-time OS bilinear. -/
theorem strictJointDoubledTimeMixedSignedQuadratic_equiv_OSBilinear
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointDoubledTimeMixedSignedQuadratic
        coupling hcoupling hle shift fixedStage hstage vector)
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift vector) :=
  CReal.Equiv.symm
    (CReal.Equiv.trans
      (strictJointDoubledTimeMixedOSBilinear_equiv_jointCenteredQuadratic
        hcoupling hle shift vector)
      (strictJointDoubledTimeMixedJointCenteredQuadratic_equiv_mixedSigned
        hcoupling hle hstage vector))

/-- Constructive inhabitant of the previously exposed doubled-time mixed OS
identity frontier. -/
theorem strictJointDoubledTimeMixedOSIdentity_derived
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    StrictJointDoubledTimeMixedOSIdentity
      hcoupling hle shift vector :=
  CReal.Equiv.trans
    (timeTranslatedStrictJointReflectionQuadratic_equiv_mixedSigned
      hcoupling hle hstage vector)
    (strictJointDoubledTimeMixedSignedQuadratic_equiv_OSBilinear
      hcoupling hle hstage vector)

#print axioms strictJointDoubledTimeMixedJointCenteredQuadratic_approx_eqv
#print axioms strictJointDoubledTimeMixedOSComparisonCoefficient_nonnegative
#print axioms strictJointDoubledTimeMixedOSBilinear_abs_sub_jointCentered_le
#print axioms strictJointDoubledTimeMixedOSBilinear_equiv_jointCenteredQuadratic
#print axioms strictJointDoubledTimeMixedJointCenteredQuadratic_equiv_mixedSigned
#print axioms strictJointDoubledTimeMixedSignedQuadratic_equiv_OSBilinear
#print axioms strictJointDoubledTimeMixedOSIdentity_derived

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
