/-
# Presentation transport for coupling-parametric joint cylinder limits

The same local cylinder may first be presented in any finite canonical box.
At matched diagonal stages, transporting the marked roots to a larger base box
changes the coupling-parametric probability by an explicit vanishing modulus.
This is the quantitative input for presentation independence of the limiting
cylinder functional.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal

namespace YMGap.Continuum.Z4CouplingParametricCylinderJointBaseTransport

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

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

private theorem four_point_abs_sub_le_local
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

/-- Transporting a finite cylinder to a larger presentation box changes the
matched diagonal approximants by at most the standard joint modulus. -/
theorem couplingParametricSpinSummedJointCylinderSequence_base_transport_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base outerBase stage : Nat} (hbase : base ≤ outerBase)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricSpinSummedJointCylinderSequence
            coupling hcoupling outerBase
            (transportedCylinderRoots base outerBase roots)
            predicate stage -
          couplingParametricSpinSummedJointCylinderSequence
            coupling hcoupling base roots predicate stage) ≤
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
  let a := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling largeCutoff large largeEvent
  let b := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling smallCutoff small smallEvent
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff large largeEvent
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff small smallEvent
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
        couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
          hcoupling hle largeEvent hlargeCutoff
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
      couplingParametricKCompatibleCylinderProbability_cofinal_abs_sub_le_half_pow
        hcoupling hle commonCutoff (base := base) (precision := stage)
          (n := base + stage) (large := outerBase + stage)
          (by omega) (by omega) hroots predicate
  have hsmall : Q'.abs (d - b) ≤ HalfPow.half ^ stage := by
    dsimp only [b, d, smallCutoff]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle smallEvent hsmallCutoff
  have hthree := four_point_abs_sub_le_local a b c d
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
      HalfPow.half ^ stage
  exact Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv hreorder)

#print axioms couplingParametricSpinSummedJointCylinderSequence_base_transport_abs_le

end YMGap.Continuum.Z4CouplingParametricCylinderJointBaseTransport
