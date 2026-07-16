/-
# Thermodynamic cylinder limits below the anchor coupling

The cross-volume modulus is independent of both the representation cutoff and
the target volume.  This module converts it to a dyadic Cauchy estimate and
constructs the thermodynamic-limit value of every finite canonical cylinder
event at every fixed cutoff and every rational coupling below the anchor.
-/

import YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
import YMGap.Continuum.Z4SpinSummedCylinderCofinal

namespace YMGap.Continuum.Z4CouplingParametricCylinderCofinal

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Pairwise cofinal modulus -/

theorem couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base n large : Nat} (hbaseN : base ≤ n) (hnLarge : n ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff large
            (targetCylinderEvent base large roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff n
            (targetCylinderEvent base n roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length (n - base) := by
  let middleRoots := transportedCylinderRoots base n roots
  have hmiddleCanonical : ∀ root, root ∈ middleRoots →
      root ∈ canonicalSurfacePolymers n :=
    transportedCylinderRoots_canonical hbaseN hroots
  have hmiddleInside : ∀ root, root ∈ middleRoots →
      PolymerInsideBox base n root :=
    transportedCylinderRoots_inside_source hbaseN hroots
  have hbox : base + (n - base) = n := Nat.add_sub_of_le hbaseN
  have hraw :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hnLarge middleRoots hmiddleCanonical predicate
      hmiddleInside hbox
  have htarget :
      markedCylinderEvent
          (transportedCanonicalCylinderAtoms hnLarge middleRoots
            hmiddleCanonical) predicate =
        targetCylinderEvent base large roots predicate := by
    refine Eq.trans
      (markedTransportedCylinderEvent_eq_target
        hnLarge middleRoots hmiddleCanonical predicate) ?_
    exact targetCylinderEvent_trans hbaseN hnLarge hroots predicate
  have hsource :
      sourceCylinderEvent middleRoots predicate =
        targetCylinderEvent base n roots predicate := rfl
  rw [htarget, hsource] at hraw
  have hlength : middleRoots.length = roots.length := by
    simp [middleRoots, transportedCylinderRoots]
  simpa only [hlength] using hraw

theorem couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base precision n large : Nat}
    (hprecision : base + precision ≤ n) (hnLarge : n ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff large
            (targetCylinderEvent base large roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff n
            (targetCylinderEvent base n roots predicate)) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ precision := by
  have hbaseN : base ≤ n :=
    Nat.le_trans (Nat.le_add_right base precision) hprecision
  have hraw :=
    couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le
      hcoupling hle cutoff hbaseN hnLarge hroots predicate
  have htail :=
    spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      roots.length (n - base)
  have hprecisionSub : precision ≤ n - base :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hprecision)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hprecisionSub
  have hhalf : HalfPow.half ^ (n - base) ≤
      HalfPow.half ^ precision := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone precision offset
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ (n - base)) (HalfPow.half ^ precision)
    (spinSummedCylinderBoundaryCoefficient roots.length) hhalf
    (spinSummedCylinderBoundaryCoefficient_nonnegative roots.length)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ htail hscaled)

/-! ## 2. Constructive fixed-cutoff thermodynamic limit -/

private theorem two_sided_add_of_abs_sub_le {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def couplingParametricKSpinSummedCylinderCofinalSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

def couplingParametricKSpinSummedCylinderCofinalLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) : CReal where
  approx := couplingParametricKSpinSummedCylinderCofinalSequence
    coupling hcoupling cutoff base roots predicate
  cauchy := by
    intro epsilon hepsilon
    let coefficient := spinSummedCylinderBoundaryCoefficient roots.length
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      spinSummedCylinderBoundaryCoefficient_nonnegative roots.length
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hdyadic :=
        couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
          hcoupling hle cutoff (base := base)
          (precision := scaledTolerance.den)
          (n := base + m) (large := base + n)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (couplingParametricKSpinSummedCylinderCofinalSequence
              coupling hcoupling cutoff base roots predicate n -
            couplingParametricKSpinSummedCylinderCofinalSequence
              coupling hcoupling cutoff base roots predicate m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      have hpair := two_sided_add_of_abs_sub_le habs
      exact ⟨hpair.2, hpair.1⟩
    · have hdyadic :=
        couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
          hcoupling hle cutoff (base := base)
          (precision := scaledTolerance.den)
          (n := base + n) (large := base + m)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (couplingParametricKSpinSummedCylinderCofinalSequence
              coupling hcoupling cutoff base roots predicate m -
            couplingParametricKSpinSummedCylinderCofinalSequence
              coupling hcoupling cutoff base roots predicate n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      exact two_sided_add_of_abs_sub_le habs

@[simp] theorem couplingParametricKSpinSummedCylinderCofinalLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (couplingParametricKSpinSummedCylinderCofinalLimit
      coupling hcoupling hle cutoff hroots predicate).approx stage =
      couplingParametricKSpinSummedCylinderCofinalSequence
        coupling hcoupling cutoff base roots predicate stage := rfl

theorem couplingParametricKCompatibleSupportEventProbability_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤ couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff n event := by
  unfold couplingParametricKCompatibleSupportEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (couplingParametricKCompatibleSupportEventNumerator_nonnegative
      hcoupling cutoff n event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingParametricKCompatibleSupportGasPartition_pos
          hcoupling cutoff n)))

theorem couplingParametricKCompatibleSupportEventProbability_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n event ≤ (1 : Q') := by
  unfold couplingParametricKCompatibleSupportEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (couplingParametricKCompatibleSupportEventNumerator_le_partition
      hcoupling cutoff n event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n)))

theorem couplingParametricKSpinSummedCylinderCofinalLimit_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤
      couplingParametricKSpinSummedCylinderCofinalLimit
        coupling hcoupling hle cutoff hroots predicate := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling cutoff (base + stage) _

theorem couplingParametricKSpinSummedCylinderCofinalLimit_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKSpinSummedCylinderCofinalLimit
        coupling hcoupling hle cutoff hroots predicate ≤
      CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling cutoff (base + stage) _

#print axioms couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le
#print axioms couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
#print axioms couplingParametricKSpinSummedCylinderCofinalLimit
#print axioms couplingParametricKCompatibleSupportEventProbability_nonnegative
#print axioms couplingParametricKCompatibleSupportEventProbability_le_one
#print axioms couplingParametricKSpinSummedCylinderCofinalLimit_nonnegative
#print axioms couplingParametricKSpinSummedCylinderCofinalLimit_le_one

end YMGap.Continuum.Z4CouplingParametricCylinderCofinal
