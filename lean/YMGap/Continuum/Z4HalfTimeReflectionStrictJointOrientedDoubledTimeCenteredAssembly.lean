/-
# Heterogeneous finite assembly for the oriented doubled-time form

The oriented doubled-time reflection coefficient may use unrelated strict
cylinder presentations on its left and right.  This file assembles the
entrywise corrected-slab comparison in that genuinely rectangular finite
coefficient space.  The result identifies the direct constructive-real
bilinear with one ordinary joint centered limit, without assuming covariance,
self-adjointness, or symmetry of the two presentations.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeEntryCenteredBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeEntryCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Rectangular centered CReal assembly -/

/-- The direct oriented reflection bilinear in the common doubled-time box. -/
def orientedDoubledTimeReflectionBilinear
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (orientedDoubledTimeSource shift left)
    (orientedDoubledTimeTarget shift right)

/-- The finite CReal cross form formed from the projected ordinary-joint
centered limits. -/
def orientedDoubledTimeJointCenteredBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun leftBits => listCRealSum
      (fun rightBits => CReal.mul
        (CReal.ofQ' (left.coefficient leftBits * right.coefficient rightBits))
        (couplingParametricStrictJointCenteredLimit
          coupling hcoupling hle
          (orientedDoubledTimeJointPredicate
            left.roots.length right.roots.length leftBits rightBits)
          (orientedDoubledTimeJointRoots_canonical shift left right)))
      (strictJointFingerprintSpace right.roots.length))
    (strictJointFingerprintSpace left.roots.length)

theorem orientedDoubledTimeJointCenteredBilinear_approx_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat}
    (left right : StrictJointCylinderVector base) :
    (orientedDoubledTimeJointCenteredBilinear
        coupling hcoupling hle shift left right).approx stage ≈
      finiteHeterogeneousCrossBilinear
        (strictJointFingerprintSpace left.roots.length)
        (strictJointFingerprintSpace right.roots.length)
        left.coefficient right.coefficient
        (fun leftBits rightBits =>
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + (shift + shift))
            (orientedDoubledTimeJointRoots shift left right)
            (orientedDoubledTimeJointPredicate
              left.roots.length right.roots.length leftBits rightBits)
            stage) := by
  unfold orientedDoubledTimeJointCenteredBilinear
    finiteHeterogeneousCrossBilinear
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro leftBits
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro rightBits
  exact Q'.eqv_refl _

/-! ## 2. Rectangular finite stability -/

/-- Literal double-list coefficient norm for a rectangular cross form. -/
def heterogeneousCoefficientPairL1
    {LeftState RightState : Type}
    (leftStates : List LeftState) (rightStates : List RightState)
    (leftCoefficient : LeftState → Q')
    (rightCoefficient : RightState → Q') : Q' :=
  listQSum (fun left => listQSum (fun right =>
    Q'.abs (leftCoefficient left * rightCoefficient right)) rightStates)
    leftStates

theorem heterogeneousCoefficientPairL1_nonnegative
    {LeftState RightState : Type}
    (leftStates : List LeftState) (rightStates : List RightState)
    (leftCoefficient : LeftState → Q')
    (rightCoefficient : RightState → Q') :
    (0 : Q') ≤ heterogeneousCoefficientPairL1
      leftStates rightStates leftCoefficient rightCoefficient := by
  unfold heterogeneousCoefficientPairL1
  apply listQSum_nonnegative_on
  intro leftBits hleft
  apply listQSum_nonnegative_on
  intro rightBits hright
  exact Q'.abs_nonneg _

/-- A uniform entry error controls a rectangular finite cross form by its
literal double-list coefficient norm. -/
theorem finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    {LeftState RightState : Type}
    (leftStates : List LeftState) (rightStates : List RightState)
    (leftCoefficient : LeftState → Q')
    (rightCoefficient : RightState → Q')
    (leftLaw rightLaw : LeftState → RightState → Q')
    (epsilon : Q')
    (herror : ∀ left right, left ∈ leftStates → right ∈ rightStates →
      Q'.abs (leftLaw left right + (-rightLaw left right)) ≤ epsilon) :
    Q'.abs
        (finiteHeterogeneousCrossBilinear
            leftStates rightStates leftCoefficient rightCoefficient leftLaw +
          (-finiteHeterogeneousCrossBilinear
            leftStates rightStates leftCoefficient rightCoefficient rightLaw)) ≤
      heterogeneousCoefficientPairL1
        leftStates rightStates leftCoefficient rightCoefficient * epsilon := by
  let leftRow : LeftState → Q' := fun left =>
    listQSum
      (fun right =>
        (leftCoefficient left * rightCoefficient right) * leftLaw left right)
      rightStates
  let rightRow : LeftState → Q' := fun left =>
    listQSum
      (fun right =>
        (leftCoefficient left * rightCoefficient right) * rightLaw left right)
      rightStates
  have houter := abs_listQSum_sub_le leftRow rightRow leftStates
  have hrows :
      listQSum (fun left => Q'.abs (leftRow left + (-rightRow left))) leftStates ≤
        listQSum
          (fun left => listQSum
            (fun right => Q'.abs
              (leftCoefficient left * rightCoefficient right))
            rightStates * epsilon)
          leftStates := by
    apply listQSum_mono
    intro left hleft
    have hinner := abs_listQSum_sub_le
      (fun right =>
        (leftCoefficient left * rightCoefficient right) * leftLaw left right)
      (fun right =>
        (leftCoefficient left * rightCoefficient right) * rightLaw left right)
      rightStates
    refine Q'.le_trans' _ _ _ hinner ?_
    have hterms :
        listQSum
            (fun right => Q'.abs
              ((leftCoefficient left * rightCoefficient right) * leftLaw left right +
                (-((leftCoefficient left * rightCoefficient right) *
                  rightLaw left right))))
            rightStates ≤
          listQSum
            (fun right =>
              Q'.abs (leftCoefficient left * rightCoefficient right) * epsilon)
            rightStates := by
      apply listQSum_mono
      intro right hright
      exact abs_common_mul_sub_le
        (leftCoefficient left * rightCoefficient right)
        (leftLaw left right) (rightLaw left right) epsilon
        (herror left right hleft hright)
    refine Q'.le_trans' _ _ _ hterms ?_
    exact Q'.le_of_eqv
      (listQSum_mul_right
        (fun right => Q'.abs
          (leftCoefficient left * rightCoefficient right))
        epsilon rightStates)
  unfold finiteHeterogeneousCrossBilinear
  change Q'.abs (listQSum leftRow leftStates +
    (-listQSum rightRow leftStates)) ≤ _
  refine Q'.le_trans' _ _ _ houter (Q'.le_trans' _ _ _ hrows ?_)
  exact Q'.le_of_eqv
    (listQSum_mul_right
      (fun left => listQSum
        (fun right => Q'.abs
          (leftCoefficient left * rightCoefficient right))
        rightStates)
      epsilon leftStates)

/-! ## 3. Dyadic finite assembly -/

def orientedDoubledTimeComparisonCoefficient
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : Q' :=
  heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient *
    strictJointConditionalCenteredCoefficient
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length)

theorem orientedDoubledTimeComparisonCoefficient_nonnegative
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    (0 : Q') ≤ orientedDoubledTimeComparisonCoefficient shift left right := by
  unfold orientedDoubledTimeComparisonCoefficient
  exact Q'.mul_nonneg _ _
    (heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient)
    (strictJointConditionalCenteredCoefficient_nonnegative
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length))

theorem orientedDoubledTimeReflectionBilinear_abs_sub_jointCentered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs
        ((orientedDoubledTimeReflectionBilinear
              hcoupling hle shift left right).approx stage -
          (orientedDoubledTimeJointCenteredBilinear
              coupling hcoupling hle shift left right).approx stage) ≤
      orientedDoubledTimeComparisonCoefficient shift left right *
        HalfPow.half ^ stage := by
  let leftStates := strictJointFingerprintSpace left.roots.length
  let rightStates := strictJointFingerprintSpace right.roots.length
  let jointRoots := orientedDoubledTimeJointRoots shift left right
  let entryCoefficient := strictJointConditionalCenteredCoefficient
    (jointRoots.length + jointRoots.length)
  let orientedLaw : List Bool → List Bool → Q' := fun leftBits rightBits =>
    orientedDoubledTimeEntrySequence
      coupling hcoupling shift left right leftBits rightBits stage
  let centeredLaw : List Bool → List Bool → Q' := fun leftBits rightBits =>
    couplingParametricStrictJointCenteredSequence
      coupling hcoupling (base + (shift + shift)) jointRoots
      (orientedDoubledTimeJointPredicate
        left.roots.length right.roots.length leftBits rightBits) stage
  have hbilinear :
      (orientedDoubledTimeReflectionBilinear
          hcoupling hle shift left right).approx stage ≈
        strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (orientedDoubledTimeSource shift left)
          (orientedDoubledTimeTarget shift right) stage := by
    simpa only [orientedDoubledTimeReflectionBilinear] using
      (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
        hcoupling hle
        (orientedDoubledTimeSource shift left)
        (orientedDoubledTimeTarget shift right)
        (stage := stage))
  have hentries :
      strictJointCylinderReflectionBilinearSequence
          coupling hcoupling
          (orientedDoubledTimeSource shift left)
          (orientedDoubledTimeTarget shift right) stage ≈
        finiteHeterogeneousCrossBilinear
          leftStates rightStates left.coefficient right.coefficient
          orientedLaw := by
    simpa only [leftStates, rightStates, orientedLaw] using
      (orientedDoubledTimeReflectionBilinearSequence_eqv_entries
        hcoupling shift left right stage)
  have hleft :
      (orientedDoubledTimeReflectionBilinear
          hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
          leftStates rightStates left.coefficient right.coefficient
          orientedLaw :=
    Q'.eqv_trans _ _ _ hbilinear hentries
  have hright :
      (orientedDoubledTimeJointCenteredBilinear
          coupling hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
          leftStates rightStates left.coefficient right.coefficient
          centeredLaw := by
    simpa only [leftStates, rightStates, jointRoots, centeredLaw] using
      (orientedDoubledTimeJointCenteredBilinear_approx_eqv
        hcoupling hle left right (shift := shift) (stage := stage))
  have hentry : ∀ leftBits rightBits,
      leftBits ∈ leftStates → rightBits ∈ rightStates →
      Q'.abs (orientedLaw leftBits rightBits +
        (-centeredLaw leftBits rightBits)) ≤
        entryCoefficient * HalfPow.half ^ stage := by
    intro leftBits rightBits hleftMem hrightMem
    simpa only [leftStates, rightStates, jointRoots, entryCoefficient,
      orientedLaw, centeredLaw] using
      (orientedDoubledTimeEntrySequence_abs_sub_jointCentered_le
        hcoupling hle shift left right leftBits rightBits stage)
  have hfinite :
      Q'.abs
          (finiteHeterogeneousCrossBilinear
              leftStates rightStates left.coefficient right.coefficient
              orientedLaw +
            (-finiteHeterogeneousCrossBilinear
              leftStates rightStates left.coefficient right.coefficient
              centeredLaw)) ≤
        heterogeneousCoefficientPairL1
            leftStates rightStates left.coefficient right.coefficient *
          (entryCoefficient * HalfPow.half ^ stage) :=
    finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
      leftStates rightStates left.coefficient right.coefficient
      orientedLaw centeredLaw
      (entryCoefficient * HalfPow.half ^ stage) hentry
  have hdifference :
      (orientedDoubledTimeReflectionBilinear
            hcoupling hle shift left right).approx stage +
          (-(orientedDoubledTimeJointCenteredBilinear
            coupling hcoupling hle shift left right).approx stage) ≈
        finiteHeterogeneousCrossBilinear
            leftStates rightStates left.coefficient right.coefficient
            orientedLaw +
          (-finiteHeterogeneousCrossBilinear
            leftStates rightStates left.coefficient right.coefficient
            centeredLaw) :=
    Q'.add_eqv_congr' hleft
      (Q'.neg_eqv_congr _ _ hright)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hfinite ?_)
  apply Q'.le_of_eqv
  simpa only [orientedDoubledTimeComparisonCoefficient,
    leftStates, rightStates, jointRoots, entryCoefficient] using
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (heterogeneousCoefficientPairL1
          leftStates rightStates left.coefficient right.coefficient)
        entryCoefficient (HalfPow.half ^ stage)))

/-! ## 4. Constructive-real closure -/

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
  let scaledTolerance := epsilon * Q'.invSucc bound.num.toNat
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
  have habs : Q'.abs (left.approx stage - right.approx stage) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hpointwise stage)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

theorem orientedDoubledTimeReflectionBilinear_equiv_jointCentered
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeReflectionBilinear
        hcoupling hle shift left right)
      (orientedDoubledTimeJointCenteredBilinear
        coupling hcoupling hle shift left right) :=
  creal_equiv_of_abs_sub_le_half_pow
    (orientedDoubledTimeReflectionBilinear hcoupling hle shift left right)
    (orientedDoubledTimeJointCenteredBilinear
      coupling hcoupling hle shift left right)
    (orientedDoubledTimeComparisonCoefficient shift left right)
    (orientedDoubledTimeComparisonCoefficient_nonnegative shift left right)
    (orientedDoubledTimeReflectionBilinear_abs_sub_jointCentered_le
      hcoupling hle shift left right)

#print axioms orientedDoubledTimeJointCenteredBilinear_approx_eqv
#print axioms heterogeneousCoefficientPairL1_nonnegative
#print axioms finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
#print axioms orientedDoubledTimeComparisonCoefficient_nonnegative
#print axioms orientedDoubledTimeReflectionBilinear_abs_sub_jointCentered_le
#print axioms orientedDoubledTimeReflectionBilinear_equiv_jointCentered

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
