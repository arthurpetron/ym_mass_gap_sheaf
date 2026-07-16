/-
# Joint representation-cutoff and thermodynamic cylinder limits

The volume modulus for canonical cylinder events is uniform in the physical
representation cutoff.  Independently, the exact cutoff-event bridge and the
telescoped cutoff tail give a derived cutoff at every finite volume.  This
module combines those estimates through a common-cutoff comparison.  The
result is one constructive real obtained while the cutoff and the box grow
simultaneously, rather than an iterated or weak compactness limit.
-/

import YMGap.Continuum.Z4SpinSummedCylinderCofinal
import YMGap.Continuum.Z4SpinSummedCutoffTail

namespace YMGap.Continuum.Z4SpinSummedCylinderJointCofinal

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderCofinal

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The diagonal sequence and its explicit modulus -/

def spinSummedJointCylinderCoefficient (rootCount : Nat) : Q' :=
  (1 : Q') +
    (spinSummedCylinderBoundaryCoefficient rootCount + (1 : Q'))

theorem spinSummedJointCylinderCoefficient_nonnegative
    (rootCount : Nat) :
    (0 : Q') ≤ spinSummedJointCylinderCoefficient rootCount := by
  unfold spinSummedJointCylinderCoefficient
  exact Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _
      (spinSummedCylinderBoundaryCoefficient_nonnegative rootCount)
      (by decide))

def spinSummedJointCylinderSequence
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  parametricKCompatibleSupportEventProbability
    (spinSummedJointCutoff stage (base + stage)) (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

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

theorem spinSummedJointCylinderSequence_pair_abs_le
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (spinSummedJointCylinderSequence base roots predicate later -
          spinSummedJointCylinderSequence base roots predicate earlier) ≤
      spinSummedJointCylinderCoefficient roots.length *
        HalfPow.half ^ earlier := by
  let small := base + earlier
  let large := base + later
  let smallCutoff := spinSummedJointCutoff earlier small
  let largeCutoff := spinSummedJointCutoff later large
  let commonCutoff := smallCutoff + largeCutoff
  let smallEvent := targetCylinderEvent base small roots predicate
  let largeEvent := targetCylinderEvent base large roots predicate
  let a := parametricKCompatibleSupportEventProbability
    largeCutoff large largeEvent
  let b := parametricKCompatibleSupportEventProbability
    smallCutoff small smallEvent
  let c := parametricKCompatibleSupportEventProbability
    commonCutoff large largeEvent
  let d := parametricKCompatibleSupportEventProbability
    commonCutoff small smallEvent
  have hlargeCutoff : largeCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hsmallCutoff : smallCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlargeRaw : Q'.abs (c - a) ≤ HalfPow.half ^ later := by
    dsimp only [a, c, largeCutoff]
    exact
      parametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        largeEvent hlargeCutoff
  have hlarge : Q'.abs (a - c) ≤ HalfPow.half ^ earlier := by
    have horiented : Q'.abs (a - c) ≤ HalfPow.half ^ later :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm a c))
        hlargeRaw
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    have hhalf : HalfPow.half ^ later ≤ HalfPow.half ^ earlier := by
      rw [hoffset]
      exact ExpNeg.pow_half_antitone earlier offset
    exact Q'.le_trans' _ _ _ horiented hhalf
  have hvolume :
      Q'.abs (c - d) ≤
        spinSummedCylinderBoundaryCoefficient roots.length *
          HalfPow.half ^ earlier := by
    dsimp only [c, d, small, large, smallEvent, largeEvent]
    exact
      parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
        commonCutoff (base := base) (precision := earlier)
          (n := base + earlier) (large := base + later)
          (by omega) (by omega) hroots predicate
  have hsmall : Q'.abs (d - b) ≤ HalfPow.half ^ earlier := by
    dsimp only [b, d, smallCutoff]
    exact
      parametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        smallEvent hsmallCutoff
  have hthree := four_point_abs_sub_le a b c d
    (HalfPow.half ^ earlier)
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ earlier)
    (HalfPow.half ^ earlier) hlarge hvolume hsmall
  have hreorder :
      HalfPow.half ^ earlier +
          (spinSummedCylinderBoundaryCoefficient roots.length *
              HalfPow.half ^ earlier +
            HalfPow.half ^ earlier) ≈
        spinSummedJointCylinderCoefficient roots.length *
          HalfPow.half ^ earlier := by
    let h := HalfPow.half ^ earlier
    let coefficient := spinSummedCylinderBoundaryCoefficient roots.length
    have hinner :
        (coefficient + (1 : Q')) * h ≈
          coefficient * h + h := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv coefficient (1 : Q') h)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (coefficient * h))
          (Q'.one_mul_eqv h))
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

/-- Changing the finite box in which a cylinder is first represented does not
change the diagonal law in the limit.  At matched stages the two
representations differ by the same three-term common-cutoff modulus. -/
theorem spinSummedJointCylinderSequence_base_transport_abs_le
    {base outerBase stage : Nat} (hbase : base ≤ outerBase)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (spinSummedJointCylinderSequence outerBase
            (transportedCylinderRoots base outerBase roots)
            predicate stage -
          spinSummedJointCylinderSequence base roots predicate stage) ≤
      spinSummedJointCylinderCoefficient roots.length *
        HalfPow.half ^ stage := by
  let small := base + stage
  let large := outerBase + stage
  let smallCutoff := spinSummedJointCutoff stage small
  let largeCutoff := spinSummedJointCutoff stage large
  let commonCutoff := smallCutoff + largeCutoff
  let smallEvent := targetCylinderEvent base small roots predicate
  let largeEvent := targetCylinderEvent outerBase large
    (transportedCylinderRoots base outerBase roots) predicate
  let a := parametricKCompatibleSupportEventProbability
    largeCutoff large largeEvent
  let b := parametricKCompatibleSupportEventProbability
    smallCutoff small smallEvent
  let c := parametricKCompatibleSupportEventProbability
    commonCutoff large largeEvent
  let d := parametricKCompatibleSupportEventProbability
    commonCutoff small smallEvent
  have hlargeCutoff : largeCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hsmallCutoff : smallCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlargeTarget : largeEvent =
      targetCylinderEvent base large roots predicate := by
    dsimp only [largeEvent, large]
    exact targetCylinderEvent_trans hbase (by omega) hroots predicate
  have hlarge : Q'.abs (a - c) ≤ HalfPow.half ^ stage := by
    have hraw : Q'.abs (c - a) ≤ HalfPow.half ^ stage := by
      dsimp only [a, c, largeCutoff]
      exact
        parametricKCompatibleEventProbability_jointCutoff_extension_abs_le
          largeEvent hlargeCutoff
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm a c)) hraw
  have hvolume :
      Q'.abs (c - d) ≤
        spinSummedCylinderBoundaryCoefficient roots.length *
          HalfPow.half ^ stage := by
    dsimp only [c, d, small, large, smallEvent]
    rw [hlargeTarget]
    exact
      parametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
        commonCutoff (base := base) (precision := stage)
          (n := base + stage) (large := outerBase + stage)
          (by omega) (by omega) hroots predicate
  have hsmall : Q'.abs (d - b) ≤ HalfPow.half ^ stage := by
    dsimp only [b, d, smallCutoff]
    exact
      parametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        smallEvent hsmallCutoff
  have hthree := four_point_abs_sub_le a b c d
    (HalfPow.half ^ stage)
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ stage)
    (HalfPow.half ^ stage) hlarge hvolume hsmall
  have hreorder :
      HalfPow.half ^ stage +
          (spinSummedCylinderBoundaryCoefficient roots.length *
              HalfPow.half ^ stage + HalfPow.half ^ stage) ≈
        spinSummedJointCylinderCoefficient roots.length *
          HalfPow.half ^ stage := by
    let h := HalfPow.half ^ stage
    let coefficient := spinSummedCylinderBoundaryCoefficient roots.length
    have hinner :
        (coefficient + (1 : Q')) * h ≈
          coefficient * h + h := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv coefficient (1 : Q') h)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (coefficient * h))
          (Q'.one_mul_eqv h))
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
      HalfPow.half ^ stage
  exact Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv hreorder)

/-! ## 2. The simultaneous cutoff/volume constructive real -/

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def spinSummedJointCylinderLimit
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) : CReal where
  approx := spinSummedJointCylinderSequence base roots predicate
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
        spinSummedJointCylinderSequence_pair_abs_le
          hmn hroots predicate
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
          (spinSummedJointCylinderSequence base roots predicate n -
            spinSummedJointCylinderSequence base roots predicate m) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        spinSummedJointCylinderSequence_pair_abs_le
          hnm hroots predicate
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
          (spinSummedJointCylinderSequence base roots predicate m -
            spinSummedJointCylinderSequence base roots predicate n) ≤
          epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem spinSummedJointCylinderLimit_approx
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (spinSummedJointCylinderLimit hroots predicate).approx stage =
      spinSummedJointCylinderSequence base roots predicate stage := rfl

theorem spinSummedJointCylinderLimit_nonnegative
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤ spinSummedJointCylinderLimit hroots predicate := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact parametricKCompatibleSupportEventProbability_nonnegative
    (spinSummedJointCutoff stage (base + stage)) (base + stage) _

theorem spinSummedJointCylinderLimit_le_one
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    spinSummedJointCylinderLimit hroots predicate ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact parametricKCompatibleSupportEventProbability_le_one
    (spinSummedJointCutoff stage (base + stage)) (base + stage) _

#print axioms spinSummedJointCylinderSequence_pair_abs_le
#print axioms spinSummedJointCylinderSequence_base_transport_abs_le
#print axioms spinSummedJointCylinderLimit
#print axioms spinSummedJointCylinderLimit_nonnegative
#print axioms spinSummedJointCylinderLimit_le_one

end YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
