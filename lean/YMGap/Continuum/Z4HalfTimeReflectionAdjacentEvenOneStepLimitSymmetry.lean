/-
# Exact swap symmetry of the adjacent-even one-step centered limit

The mixed centered chart used by the adjacent-even one-step EventLaw is the
first/fourth-block projection of an ordinary strict-joint centered chart at
base `base + 1`.  Consequently its constructive limit is supplied by the
existing strict-joint Cauchy machinery.  The explicit finite-stage
`half^stage` swap defect then vanishes constructively, giving exact symmetry
of the two `CReal` limits.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalCenteredComparison
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalCenteredComparison
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The mixed chart as a projected ordinary strict-joint chart -/

/-- Put the canonically transported lower sources and the one-step translated
upper sources into one ordinary strict-joint source list. -/
def adjacentEvenOneStepProjectedRoots
    (base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  transportedCylinderRoots base (base + 1) roots ++
    roots.map (timeShiftCanonicalRoot 1 base)

@[simp] theorem adjacentEvenOneStepProjectedRoots_length
    (base : Nat) (roots : List (List Nat)) :
    (adjacentEvenOneStepProjectedRoots base roots).length =
      roots.length + roots.length := by
  simp [adjacentEvenOneStepProjectedRoots, transportedCylinderRoots]

theorem adjacentEvenOneStepProjectedRoots_canonical
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ adjacentEvenOneStepProjectedRoots base roots →
      target ∈ canonicalSurfacePolymers (base + 1) := by
  intro target htarget
  rcases List.mem_append.mp htarget with htransported | htranslated
  · exact transportedCylinderRoots_canonical
      (Nat.le_add_right base 1) hroots target htransported
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp htranslated
    exact timeShiftCanonicalRoot_canonical (hroots root hroot)

/-- The first/fourth-block projection selects exactly the lower source at
stage `stage + 1` and the one-step translated upper source at stage `stage`.
Thus it is literally the mixed centered event used by the adjacent-even
finite-stage theorem. -/
theorem adjacentEvenOneStepProjectedCylinderEvent_eq
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    centralStrictJointCenteredCylinderEvent
        (base + 1) stage
        (adjacentEvenOneStepProjectedRoots base roots)
        (orientedDoubledTimeJointPredicate
          roots.length roots.length left right) =
      adjacentEvenOneStepCenteredPairEvent
        base stage roots left right := by
  let transported := transportedCylinderRoots base (base + 1) roots
  let translated := roots.map (timeShiftCanonicalRoot 1 base)
  let lower := centralStrictLowerCenteredStageRoot (base + 1) stage
  let upper := centralStrictUpperCenteredStageRoot (base + 1) stage
  have hlower : transported.map lower =
      roots.map (centralStrictLowerCenteredStageRoot base (stage + 1)) := by
    dsimp only [transported, lower, transportedCylinderRoots]
    rw [List.map_map]
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictLowerCenteredStageRoot_transportBase_aligned
      (padding := 1) (stage := stage) (hroots root hroot)
  have hupper : translated.map upper =
      roots.map (fun root =>
        centralStrictUpperCenteredStageRoot (base + 1) stage
          (timeShiftCanonicalRoot 1 base root)) := by
    dsimp only [translated, upper]
    rw [List.map_map]
    rfl
  unfold centralStrictJointCenteredCylinderEvent
  rw [centralStrictJointCenteredStageRoots_split]
  unfold adjacentEvenOneStepProjectedRoots
  rw [List.map_append, List.map_append]
  change sourceCylinderEvent
      ((transported.map lower ++ translated.map lower) ++
        (transported.map upper ++ translated.map upper))
      (orientedDoubledTimeJointPredicate
        roots.length roots.length left right) = _
  rw [hlower, hupper]
  simpa only [adjacentEvenOneStepCenteredPairEvent,
      adjacentEvenOneStepCenteredRoots] using
    (orientedProjectedFourBlockCylinderEvent_eq
      roots.length roots.length
      (roots.map
        (centralStrictLowerCenteredStageRoot base (stage + 1)))
      (translated.map lower)
      (transported.map upper)
      (roots.map (fun root =>
        centralStrictUpperCenteredStageRoot (base + 1) stage
          (timeShiftCanonicalRoot 1 base root)))
      (by simp)
      (by simp [translated])
      (by simp [transported, transportedCylinderRoots])
      left right)

/-! ## 2. Scheduled sequence and its existing constructive limit -/

def couplingParametricAdjacentEvenOneStepCenteredPairSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (left right : List Bool) (stage : Nat) : Q' :=
  couplingParametricStrictJointCenteredSequence
    coupling hcoupling (base + 1)
    (adjacentEvenOneStepProjectedRoots base roots)
    (orientedDoubledTimeJointPredicate
      roots.length roots.length left right) stage

theorem couplingParametricAdjacentEvenOneStepCenteredPairSequence_eq
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    couplingParametricAdjacentEvenOneStepCenteredPairSequence
        coupling hcoupling base roots left right stage =
      couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
        coupling hcoupling
        (centralStrictJointCenteredStageCutoff (base + 1) stage)
        base stage roots left right := by
  unfold couplingParametricAdjacentEvenOneStepCenteredPairSequence
    couplingParametricStrictJointCenteredSequence
    couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
  rw [adjacentEvenOneStepProjectedCylinderEvent_eq hroots left right]

def couplingParametricAdjacentEvenOneStepCenteredPairLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) : CReal :=
  couplingParametricStrictJointCenteredLimit
    coupling hcoupling hle
    (orientedDoubledTimeJointPredicate
      roots.length roots.length left right)
    (adjacentEvenOneStepProjectedRoots_canonical hroots)

@[simp] theorem couplingParametricAdjacentEvenOneStepCenteredPairLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    (couplingParametricAdjacentEvenOneStepCenteredPairLimit
      coupling hcoupling hle hroots left right).approx stage =
      couplingParametricAdjacentEvenOneStepCenteredPairSequence
        coupling hcoupling base roots left right stage := rfl

theorem couplingParametricAdjacentEvenOneStepCenteredPairSequence_swap_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingParametricAdjacentEvenOneStepCenteredPairSequence
            coupling hcoupling base roots left right stage -
          couplingParametricAdjacentEvenOneStepCenteredPairSequence
            coupling hcoupling base roots right left stage) ≤
      adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length) *
        HalfPow.half ^ stage := by
  rw [couplingParametricAdjacentEvenOneStepCenteredPairSequence_eq
      hcoupling hroots left right,
    couplingParametricAdjacentEvenOneStepCenteredPairSequence_eq
      hcoupling hroots right left]
  exact
    couplingParametricKCompatibleAdjacentEvenCenteredPair_swap_abs_le_half_pow
      hcoupling hle
      (centralStrictJointCenteredStageCutoff (base + 1) stage)
      hroots left right

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-! ## 3. The geometric defect vanishes in the constructive limit -/

theorem couplingParametricAdjacentEvenOneStepCenteredPairLimit_swap
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (couplingParametricAdjacentEvenOneStepCenteredPairLimit
        coupling hcoupling hle hroots left right)
      (couplingParametricAdjacentEvenOneStepCenteredPairLimit
        coupling hcoupling hle hroots right left) := by
  intro epsilon hepsilon
  let coefficient :=
    adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length)
  let scaledTolerance :=
    epsilon * Q'.invSucc coefficient.num.toNat
  have hcoefficient : (0 : Q') ≤ coefficient :=
    adjacentEvenOneStepCenteredSwapCoefficient_nonnegative
      (2 * roots.length)
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
  have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
      hcoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ stage) scaledTolerance coefficient
    (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
  have hpoint :=
    couplingParametricAdjacentEvenOneStepCenteredPairSequence_swap_abs_le
      (stage := stage) hcoupling hle hroots left right
  have habs : Q'.abs
      ((couplingParametricAdjacentEvenOneStepCenteredPairLimit
          coupling hcoupling hle hroots left right).approx stage -
        (couplingParametricAdjacentEvenOneStepCenteredPairLimit
          coupling hcoupling hle hroots right left).approx stage) ≤
      epsilon :=
    Q'.le_trans' _ _ _
      (by simpa only [
          couplingParametricAdjacentEvenOneStepCenteredPairLimit_approx,
          coefficient] using hpoint)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

#print axioms adjacentEvenOneStepProjectedRoots_canonical
#print axioms adjacentEvenOneStepProjectedCylinderEvent_eq
#print axioms couplingParametricAdjacentEvenOneStepCenteredPairSequence_eq
#print axioms couplingParametricAdjacentEvenOneStepCenteredPairLimit
#print axioms couplingParametricAdjacentEvenOneStepCenteredPairSequence_swap_abs_le
#print axioms couplingParametricAdjacentEvenOneStepCenteredPairLimit_swap

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry
