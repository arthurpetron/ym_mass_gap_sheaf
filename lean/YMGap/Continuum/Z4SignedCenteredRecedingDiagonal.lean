/-
# Rational receding-centered diagonal and its constructive limit interface

For a fixed canonical cylinder presentation, stage `s` uses the centered box
of radius `base + s`, the exact fixed-support recoding from
`Z4SignedCenteredFixedObservableRecoding`, and the already-derived joint
representation cutoff for that finite box.  Thus every approximation is an
existing physical finite-volume rational probability.

The one missing input is isolated as `CenteredRecedingVolumeModulus`: at a
common cutoff, the laws at two centered stages differ by the derived boundary
tail at the earlier protected distance.  From that input this file proves the
full common-cutoff three-term estimate and constructs a Bishop `CReal` with an
explicit dyadic modulus.  The input is a proposition to be proved by the
uniform-shift weight/probability bridge; it is not postulated here.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal
import YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding

namespace YMGap.Continuum.Z4SignedCenteredRecedingDiagonal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact rational stage law -/

def centeredRecedingStageRadius (base stage : Nat) : Nat :=
  base + stage

def centeredRecedingStageBase (base stage : Nat) : Nat :=
  centeredBoxBase (centeredRecedingStageRadius base stage)

def centeredRecedingStageRoots
    (base stage : Nat) (roots : List (List Nat)) : List (List Nat) :=
  centeredOffsetCylinderRoots
    (centeredRecedingStageRadius base stage) base roots

def centeredRecedingStageCutoff (base stage : Nat) : Nat :=
  spinSummedJointCutoff stage (centeredRecedingStageBase base stage)

def centeredRecedingCylinderEvent
    (base stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  cylinderEvent (centeredRecedingStageRoots base stage roots) predicate

def couplingParametricCenteredRecedingCylinderSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling (centeredRecedingStageCutoff base stage)
    (centeredRecedingStageBase base stage)
    (centeredRecedingCylinderEvent base stage roots predicate)

theorem centeredRecedingStageRadius_mono
    {base earlier later : Nat} (hstage : earlier ≤ later) :
    centeredRecedingStageRadius base earlier ≤
      centeredRecedingStageRadius base later := by
  unfold centeredRecedingStageRadius
  omega

theorem centeredRecedingStageBase_mono
    {base earlier later : Nat} (hstage : earlier ≤ later) :
    centeredRecedingStageBase base earlier ≤
      centeredRecedingStageBase base later := by
  unfold centeredRecedingStageBase centeredRecedingStageRadius
    centeredBoxBase
  omega

theorem centeredRecedingStageRoots_length
    (base stage : Nat) (roots : List (List Nat)) :
    (centeredRecedingStageRoots base stage roots).length = roots.length := by
  unfold centeredRecedingStageRoots
  exact centeredOffsetCylinderRoots_length _ _ _

theorem centeredRecedingStageRoots_canonical
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centeredRecedingStageRoots base stage roots →
      target ∈ canonicalSurfacePolymers
        (centeredRecedingStageBase base stage) := by
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
    centeredRecedingStageBase
  exact centeredOffsetCylinderRoots_canonical
    (Nat.le_add_right base stage) hroots

theorem centeredRecedingStageBase_eq_uniformPadded
    (base stage : Nat) :
    centeredRecedingStageBase base stage =
      uniformPaddedBase stage (centeredBoxBase base) := by
  unfold centeredRecedingStageBase centeredRecedingStageRadius
  exact (uniformPaddedBase_centeredBoxBase base stage).symm

theorem centeredRecedingStageRoots_eq_uniformShift
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centeredRecedingStageRoots base stage roots =
      (centeredRecedingStageRoots base 0 roots).map
        (uniformShiftCanonicalRoot stage (centeredBoxBase base)) := by
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
  simp only [Nat.add_zero]
  exact
    centeredOffsetCylinderRoots_eq_uniformShift_from_centeredBase hroots

theorem centeredRecedingCylinderEvent_eq_uniformShift
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    centeredRecedingCylinderEvent base stage roots predicate =
      cylinderEvent
        ((centeredRecedingStageRoots base 0 roots).map
          (uniformShiftCanonicalRoot stage (centeredBoxBase base)))
        predicate := by
  unfold centeredRecedingCylinderEvent
  rw [centeredRecedingStageRoots_eq_uniformShift hroots]

theorem couplingParametricCenteredRecedingCylinderSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    (0 : Q') ≤ couplingParametricCenteredRecedingCylinderSequence
      coupling hcoupling base roots predicate stage :=
  couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling (centeredRecedingStageCutoff base stage)
      (centeredRecedingStageBase base stage)
      (centeredRecedingCylinderEvent base stage roots predicate)

theorem couplingParametricCenteredRecedingCylinderSequence_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots predicate stage ≤ (1 : Q') :=
  couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling (centeredRecedingStageCutoff base stage)
      (centeredRecedingStageBase base stage)
      (centeredRecedingCylinderEvent base stage roots predicate)

/-! ## 2. The precise remaining uniform-shift probability input -/

def CenteredRecedingVolumeModulus
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : Prop :=
  (∀ root, root ∈ roots → root ∈ canonicalSurfacePolymers base) ∧
    ∀ (cutoff : Nat) {earlier later : Nat}, earlier ≤ later →
      Q'.abs
          (couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff
              (centeredRecedingStageBase base later)
              (centeredRecedingCylinderEvent base later roots predicate) -
            couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff
              (centeredRecedingStageBase base earlier)
              (centeredRecedingCylinderEvent base earlier roots predicate)) ≤
        spinSummedCylinderBoundaryCoefficient roots.length *
          HalfPow.half ^ earlier

theorem centeredRecedingVolumeModulus_stageRoots_canonical
    {coupling : Q'} {hcoupling : (0 : Q') ≤ coupling}
    {base : Nat} {roots : List (List Nat)}
    {predicate : List Bool → Bool}
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) :
    ∀ stage target,
      target ∈ centeredRecedingStageRoots base stage roots →
        target ∈ canonicalSurfacePolymers
          (centeredRecedingStageBase base stage) := by
  intro stage
  exact centeredRecedingStageRoots_canonical hvolume.1

/-! ## 3. Common-cutoff interpolation -/

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem four_point_abs_sub_le
    (a b c d epsilonAC epsilonCD epsilonDB : Q')
    (hAC : Q'.abs (a - c) ≤ epsilonAC)
    (hCD : Q'.abs (c - d) ≤ epsilonCD)
    (hDB : Q'.abs (d - b) ≤ epsilonDB) :
    Q'.abs (a - b) ≤ epsilonAC + (epsilonCD + epsilonDB) := by
  have hdecompose :
      a - b ≈ (a - c) + ((c - d) + (d - b)) := by
    change a + (-b) ≈
      (a + (-c)) + ((c + (-d)) + (d + (-b)))
    have hinner :
        (c + (-d)) + (d + (-b)) ≈ c + (-b) :=
      reassoc_cancel_local c d (-b)
    have hrhs :
        (a + (-c)) + ((c + (-d)) + (d + (-b))) ≈
          a + (-b) := by
      refine Q'.eqv_trans _ ((a + (-c)) + (c + (-b))) _ ?_
        (reassoc_cancel_local a c (-b))
      exact Q'.add_eqv_congr_left (a + (-c)) _ _ hinner
    exact Q'.eqv_symm hrhs
  have htriangleOuter :=
    Q'.abs_add_le' (a - c) ((c - d) + (d - b))
  have htriangleInner := Q'.abs_add_le' (c - d) (d - b)
  have hinner := Q'.add_le_add hCD hDB
  have houter := Q'.add_le_add hAC
    (Q'.le_trans' _ _ _ htriangleInner hinner)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangleOuter houter)

theorem couplingParametricCenteredRecedingCylinderSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)} (predicate : List Bool → Bool)
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) :
    Q'.abs
        (couplingParametricCenteredRecedingCylinderSequence
            coupling hcoupling base roots predicate later -
          couplingParametricCenteredRecedingCylinderSequence
            coupling hcoupling base roots predicate earlier) ≤
      spinSummedJointCylinderCoefficient roots.length *
        HalfPow.half ^ earlier := by
  let smallBase := centeredRecedingStageBase base earlier
  let largeBase := centeredRecedingStageBase base later
  let smallCutoff := centeredRecedingStageCutoff base earlier
  let largeCutoff := centeredRecedingStageCutoff base later
  let commonCutoff := smallCutoff + largeCutoff
  let smallEvent := centeredRecedingCylinderEvent
    base earlier roots predicate
  let largeEvent := centeredRecedingCylinderEvent
    base later roots predicate
  let a := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling largeCutoff largeBase largeEvent
  let b := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling smallCutoff smallBase smallEvent
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff largeBase largeEvent
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff smallBase smallEvent
  have hlargeCutoff : largeCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hsmallCutoff : smallCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlargeRaw : Q'.abs (c - a) ≤ HalfPow.half ^ later := by
    dsimp only [a, c, largeCutoff, largeBase]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle largeEvent hlargeCutoff
  have hlarge : Q'.abs (a - c) ≤ HalfPow.half ^ earlier := by
    have horiented : Q'.abs (a - c) ≤ HalfPow.half ^ later :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm a c))
        hlargeRaw
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    have hhalf : HalfPow.half ^ later ≤
        HalfPow.half ^ earlier := by
      rw [hoffset]
      exact ExpNeg.pow_half_antitone earlier offset
    exact Q'.le_trans' _ _ _ horiented hhalf
  have hmiddle : Q'.abs (c - d) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ earlier := by
    dsimp only [c, d, largeBase, smallBase, largeEvent, smallEvent]
    exact hvolume.2 commonCutoff hstage
  have hsmall : Q'.abs (d - b) ≤ HalfPow.half ^ earlier := by
    dsimp only [b, d, smallCutoff, smallBase]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle smallEvent hsmallCutoff
  have hthree := four_point_abs_sub_le a b c d
    (HalfPow.half ^ earlier)
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ earlier)
    (HalfPow.half ^ earlier) hlarge hmiddle hsmall
  have hreorder :
      HalfPow.half ^ earlier +
          (spinSummedCylinderBoundaryCoefficient roots.length *
              HalfPow.half ^ earlier + HalfPow.half ^ earlier) ≈
        spinSummedJointCylinderCoefficient roots.length *
          HalfPow.half ^ earlier := by
    let h := HalfPow.half ^ earlier
    let coefficient := spinSummedCylinderBoundaryCoefficient roots.length
    have hinner :
        (coefficient + (1 : Q')) * h ≈ coefficient * h + h :=
      Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv coefficient (1 : Q') h)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (coefficient * h)) (Q'.one_mul_eqv h))
    have hright :
        spinSummedJointCylinderCoefficient roots.length * h ≈
          h + (coefficient * h + h) := by
      unfold spinSummedJointCylinderCoefficient
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (1 : Q')
          (spinSummedCylinderBoundaryCoefficient roots.length + (1 : Q')) h)
        (Q'.add_eqv_congr' (Q'.one_mul_eqv h) hinner)
    exact Q'.eqv_symm hright
  change Q'.abs (a - b) ≤
    spinSummedJointCylinderCoefficient roots.length *
      HalfPow.half ^ earlier
  exact Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv hreorder)

/-! ## 4. Conditional constructive completion of the diagonal -/

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) : CReal where
  approx := couplingParametricCenteredRecedingCylinderSequence
    coupling hcoupling base roots predicate
  cauchy := by
    intro epsilon hepsilon
    let coefficient := spinSummedJointCylinderCoefficient roots.length
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      spinSummedJointCylinderCoefficient_nonnegative roots.length
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricCenteredRecedingCylinderSequence_pair_abs_le
          hcoupling hle hmn predicate hvolume
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricCenteredRecedingCylinderSequence
              coupling hcoupling base roots predicate n -
            couplingParametricCenteredRecedingCylinderSequence
              coupling hcoupling base roots predicate m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricCenteredRecedingCylinderSequence_pair_abs_le
          hcoupling hle hnm predicate hvolume
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricCenteredRecedingCylinderSequence
              coupling hcoupling base roots predicate m -
            couplingParametricCenteredRecedingCylinderSequence
              coupling hcoupling base roots predicate n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricCenteredRecedingCylinderLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) :
    (couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
      coupling hcoupling hle predicate hvolume).approx stage =
      couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots predicate stage := rfl

theorem couplingParametricCenteredRecedingCylinderLimit_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) :
    CReal.ofQ' 0 ≤
      couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
        coupling hcoupling hle predicate hvolume := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_nonnegative
    hcoupling base roots predicate stage

theorem couplingParametricCenteredRecedingCylinderLimit_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hvolume : CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate) :
    couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
        coupling hcoupling hle predicate hvolume ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_le_one
    hcoupling base roots predicate stage

#print axioms centeredRecedingStageRoots_canonical
#print axioms centeredRecedingStageRoots_eq_uniformShift
#print axioms centeredRecedingCylinderEvent_eq_uniformShift
#print axioms centeredRecedingVolumeModulus_stageRoots_canonical
#print axioms couplingParametricCenteredRecedingCylinderSequence_nonnegative
#print axioms couplingParametricCenteredRecedingCylinderSequence_le_one
#print axioms couplingParametricCenteredRecedingCylinderSequence_pair_abs_le
#print axioms couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
#print axioms couplingParametricCenteredRecedingCylinderLimit_nonnegative
#print axioms couplingParametricCenteredRecedingCylinderLimit_le_one

end YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
