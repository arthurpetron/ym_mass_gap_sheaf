/-
# Thermodynamic cylinder limits for every physical spin cutoff

The exact cross-volume bridge turns the same-volume boundary estimate into a
genuine comparison of finite-box laws.  This module converts that comparison
to a dyadic modulus and constructs, for every representation cutoff, the
thermodynamic-limit functional of every finite canonical cylinder event.
The modulus is independent of the cutoff.
-/

import YMGap.Continuum.Z4CanonicalCylinderCofinal
import YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

namespace YMGap.Continuum.Z4SpinSummedCylinderCofinal

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A dyadic form of the spin-summed boundary tail -/

def spinSummedCylinderBoundaryCoefficient (rootCount : Nat) : Q' :=
  Q'.ofNat rootCount * (Q'.ofNat 2 + Q'.ofNat 2)

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

theorem spinSummedCylinderBoundaryCoefficient_nonnegative
    (rootCount : Nat) :
    (0 : Q') ≤ spinSummedCylinderBoundaryCoefficient rootCount := by
  unfold spinSummedCylinderBoundaryCoefficient
  exact Q'.mul_nonneg _ _
    (ofNat_nonnegative_local rootCount)
    (Q'.zero_le_add _ _
      (ofNat_nonnegative_local 2) (ofNat_nonnegative_local 2))

private theorem qpow_base_mono_local {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ exponent : Nat, x ^ exponent ≤ y ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      change x * x ^ exponent ≤ y * y ^ exponent
      exact Q'.mul_le_mul_of_nonneg
        hxy (qpow_base_mono_local hx hxy exponent)
        (Q'.le_trans' _ _ _ hx hxy)
        (Q'.pow_nonneg x hx exponent)

theorem spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
    (rootCount distance : Nat) :
    spinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ distance := by
  have hbase :
      anchorDecoratedEffectiveRatio ^ (distance + 2) ≤
        HalfPow.half ^ (distance + 2) :=
    qpow_base_mono_local anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half (distance + 2)
  have hdrop : HalfPow.half ^ (distance + 2) ≤
      HalfPow.half ^ distance :=
    ExpNeg.pow_half_antitone distance 2
  have hpow : anchorDecoratedEffectiveRatio ^ (distance + 2) ≤
      HalfPow.half ^ distance :=
    Q'.le_trans' _ _ _ hbase hdrop
  have hterm :
      anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2 ≤
        HalfPow.half ^ distance * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow
      (ofNat_nonnegative_local 2)
  have hsum := Q'.add_le_add hterm hterm
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hsum
    (ofNat_nonnegative_local rootCount)
  have hreorder :
      Q'.ofNat rootCount *
          (HalfPow.half ^ distance * Q'.ofNat 2 +
            HalfPow.half ^ distance * Q'.ofNat 2) ≈
        spinSummedCylinderBoundaryCoefficient rootCount *
          HalfPow.half ^ distance := by
    refine Q'.eqv_trans _
      (Q'.ofNat rootCount *
        (Q'.ofNat 2 * HalfPow.half ^ distance +
          Q'.ofNat 2 * HalfPow.half ^ distance)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _))
    refine Q'.eqv_trans _
      (Q'.ofNat rootCount *
        ((Q'.ofNat 2 + Q'.ofNat 2) * HalfPow.half ^ distance)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2)
            (HalfPow.half ^ distance)))
    unfold spinSummedCylinderBoundaryCoefficient
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat rootCount)
        (Q'.ofNat 2 + Q'.ofNat 2) (HalfPow.half ^ distance))
  unfold spinSummedCylinderBoundaryEpsilon at hscaled ⊢
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreorder)


/-! ## 2. Pairwise cofinal volume modulus -/

theorem parametricKCompatibleCylinderProbability_cofinal_abs_sub_le
    (cutoff : Nat) {base n large : Nat}
    (hbaseN : base ≤ n) (hnLarge : n ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability cutoff large
            (targetCylinderEvent base large roots predicate) -
          parametricKCompatibleSupportEventProbability cutoff n
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
    parametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      cutoff hnLarge middleRoots hmiddleCanonical predicate
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
        targetCylinderEvent base n roots predicate := by
    rfl
  rw [htarget, hsource] at hraw
  have hlength : middleRoots.length = roots.length := by
    simp [middleRoots, transportedCylinderRoots]
  simpa only [hlength] using hraw


theorem parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
    (cutoff : Nat) {base precision n large : Nat}
    (hprecision : base + precision ≤ n) (hnLarge : n ≤ large)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability cutoff large
            (targetCylinderEvent base large roots predicate) -
          parametricKCompatibleSupportEventProbability cutoff n
            (targetCylinderEvent base n roots predicate)) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ precision := by
  have hbaseN : base ≤ n :=
    Nat.le_trans (Nat.le_add_right base precision) hprecision
  have hraw :=
    parametricKCompatibleCylinderProbability_cofinal_abs_sub_le
      cutoff hbaseN hnLarge hroots predicate
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


/-! ## 3. A constructive thermodynamic cylinder functional at every cutoff -/

private theorem two_sided_add_of_abs_sub_le {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def parametricKSpinSummedCylinderCofinalSequence
    (cutoff base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  parametricKCompatibleSupportEventProbability cutoff (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

def parametricKSpinSummedCylinderCofinalLimit
    (cutoff : Nat) {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) : CReal where
  approx := parametricKSpinSummedCylinderCofinalSequence
    cutoff base roots predicate
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
        parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
          cutoff (base := base) (precision := scaledTolerance.den)
          (n := base + m) (large := base + n)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (parametricKSpinSummedCylinderCofinalSequence
              cutoff base roots predicate n -
            parametricKSpinSummedCylinderCofinalSequence
              cutoff base roots predicate m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      have hpair := two_sided_add_of_abs_sub_le habs
      exact ⟨hpair.2, hpair.1⟩
    · have hdyadic :=
        parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
          cutoff (base := base) (precision := scaledTolerance.den)
          (n := base + n) (large := base + m)
          (by omega) (by omega) hroots predicate
      have hhalf := HalfPow.pow_half_le
        scaledTolerance hscaledPositive
      have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ scaledTolerance.den) scaledTolerance
        coefficient hhalf hcoefficient
      have habs : Q'.abs
          (parametricKSpinSummedCylinderCofinalSequence
              cutoff base roots predicate m -
            parametricKSpinSummedCylinderCofinalSequence
              cutoff base roots predicate n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hdyadic
          (Q'.le_trans' _ _ _ hscaledHalf hscaledFinal)
      exact two_sided_add_of_abs_sub_le habs


@[simp] theorem parametricKSpinSummedCylinderCofinalLimit_approx
    (cutoff : Nat) {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (parametricKSpinSummedCylinderCofinalLimit
      cutoff hroots predicate).approx stage =
      parametricKSpinSummedCylinderCofinalSequence
        cutoff base roots predicate stage := rfl

theorem parametricKSpinSummedCylinderCofinalLimit_nonnegative
    (cutoff : Nat) {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤
      parametricKSpinSummedCylinderCofinalLimit cutoff hroots predicate := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact parametricKCompatibleSupportEventProbability_nonnegative
    cutoff (base + stage) _

theorem parametricKSpinSummedCylinderCofinalLimit_le_one
    (cutoff : Nat) {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    parametricKSpinSummedCylinderCofinalLimit cutoff hroots predicate ≤
      CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact parametricKCompatibleSupportEventProbability_le_one
    cutoff (base + stage) _

#print axioms spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
#print axioms parametricKCompatibleCylinderProbability_cofinal_abs_sub_le
#print axioms parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
#print axioms parametricKSpinSummedCylinderCofinalLimit
#print axioms parametricKSpinSummedCylinderCofinalLimit_nonnegative
#print axioms parametricKSpinSummedCylinderCofinalLimit_le_one

end YMGap.Continuum.Z4SpinSummedCylinderCofinal
