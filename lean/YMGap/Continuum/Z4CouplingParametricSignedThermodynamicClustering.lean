/-
# Thermodynamic diagonal for the strict signed covariance

This module connects the arbitrary-cutoff geometric covariance to the
centered thermodynamic schedules used by the Osterwalder--Schrader transfer
construction.  The central even-volume sequence uses the same selected
lower-source and upper-target roots as the geometric theorem.  Entrywise
adjacent-volume comparison then relates it to the ordinary centered joint
bilinear with an explicit half-power error.

The final goal of this file is a constructed receding-volume connected
`CReal`, its `1/16` geometric bound, and its exact identification with the
dense connected transfer form.  No presentation-independent completed-space
bound or continuum gap is asserted.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly

namespace YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem sub_sub_rearrange_local (a b c d : Q') :
    (a - b) - (c - d) ≈ (a - c) + -(b - d) := by
  change ((a + -b) + -(c + -d)) ≈ (a + -c) + -(b + -d)
  ring_qeqv

private theorem factor_three_rate_local
    (a b c d e rate : Q') :
    a * rate + (b * (c * rate) + d * (e * rate)) ≈
      (a + (b * c + d * e)) * rate := by
  ring_qeqv

private theorem qmul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem add_neg_zero_eqv_local (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl value)
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

private theorem finiteHeterogeneousCrossBilinear_zeroLaw_eqv
    {Left Right : Type}
    (leftStates : List Left) (rightStates : List Right)
    (leftCoefficient : Left → Q') (rightCoefficient : Right → Q') :
    finiteHeterogeneousCrossBilinear
        leftStates rightStates leftCoefficient rightCoefficient
        (fun _ _ => (0 : Q')) ≈ 0 := by
  unfold finiteHeterogeneousCrossBilinear
  refine Q'.eqv_trans _
    (listQSum (fun _ : Left => (0 : Q')) leftStates) _ ?_
    (listQSum_zero leftStates)
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _
    (listQSum (fun _ : Right => (0 : Q')) rightStates) _ ?_
    (listQSum_zero rightStates)
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_zero_eqv (leftCoefficient left * rightCoefficient right)

private theorem finiteHeterogeneousCrossBilinear_abs_le_of_entry_abs_le
    {Left Right : Type}
    (leftStates : List Left) (rightStates : List Right)
    (leftCoefficient : Left → Q') (rightCoefficient : Right → Q')
    (joint : Left → Right → Q') (bound : Q')
    (hentry : ∀ left right, left ∈ leftStates → right ∈ rightStates →
      Q'.abs (joint left right) ≤ bound) :
    Q'.abs (finiteHeterogeneousCrossBilinear
        leftStates rightStates leftCoefficient rightCoefficient joint) ≤
      heterogeneousCoefficientPairL1
        leftStates rightStates leftCoefficient rightCoefficient * bound := by
  let zeroLaw : Left → Right → Q' := fun _ _ => 0
  have hfinite := finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    leftStates rightStates leftCoefficient rightCoefficient
    joint zeroLaw bound
    (fun left right hleft hright => by
      have hdifference : joint left right - zeroLaw left right ≈
          joint left right := by
        exact add_neg_zero_eqv_local (joint left right)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
        (hentry left right hleft hright))
  have hzero : finiteHeterogeneousCrossBilinear
      leftStates rightStates leftCoefficient rightCoefficient zeroLaw ≈ 0 :=
    finiteHeterogeneousCrossBilinear_zeroLaw_eqv
      leftStates rightStates leftCoefficient rightCoefficient
  have hdifference :
      finiteHeterogeneousCrossBilinear
          leftStates rightStates leftCoefficient rightCoefficient joint -
        finiteHeterogeneousCrossBilinear
          leftStates rightStates leftCoefficient rightCoefficient zeroLaw ≈
      finiteHeterogeneousCrossBilinear
        leftStates rightStates leftCoefficient rightCoefficient joint := by
    refine Q'.eqv_trans _
      (finiteHeterogeneousCrossBilinear
          leftStates rightStates leftCoefficient rightCoefficient joint - 0) _
      ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hzero)
    · exact add_neg_zero_eqv_local _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hdifference))) hfinite

private theorem abs_mul_sub_mul_le_local
    {a b c d aBound dBound bError aError : Q'}
    (haBound : (0 : Q') ≤ aBound) (hdBound : (0 : Q') ≤ dBound)
    (ha : Q'.abs a ≤ aBound) (hd : Q'.abs d ≤ dBound)
    (hb : Q'.abs (b - d) ≤ bError)
    (hc : Q'.abs (a - c) ≤ aError) :
    Q'.abs (a * b - c * d) ≤
      aBound * bError + dBound * aError := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr
      (CReal.mul_sub_decomp a b c d))) ?_
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
  apply Q'.add_le_add
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        (Q'.abs a) aBound (Q'.abs (b - d))
        ha (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.abs (b - d)) bError aBound hb haBound)
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        (Q'.abs d) dBound (Q'.abs (a - c))
        hd (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.abs (a - c)) aError dBound hc hdBound)

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

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

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (ExpNeg.abs_add_le _ _)

private theorem quarter_half_quarter_eqv_local (epsilon : Q') :
    (HalfPow.half * (HalfPow.half * epsilon)) +
        (HalfPow.half * epsilon +
          HalfPow.half * (HalfPow.half * epsilon)) ≈ epsilon := by
  let quarter := HalfPow.half * (HalfPow.half * epsilon)
  let halfEpsilon := HalfPow.half * epsilon
  refine Q'.eqv_trans _
    (quarter + (quarter + halfEpsilon)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left quarter _ _
      (Q'.add_comm_eqv halfEpsilon quarter)
  refine Q'.eqv_trans _ ((quarter + quarter) + halfEpsilon) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.add_assoc_eqv quarter quarter halfEpsilon)
  refine Q'.eqv_trans _ (halfEpsilon + halfEpsilon) _ ?_ ?_
  · exact Q'.add_eqv_congr_right
      (quarter + quarter) halfEpsilon halfEpsilon
      (ExpNeg.two_halves halfEpsilon)
  · exact ExpNeg.two_halves epsilon

private theorem dyadic_scaled_eventually_local
    (bound : Q') (hbound : (0 : Q') ≤ bound)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ∃ N : Nat, ∀ stage : Nat, N ≤ stage →
      bound * HalfPow.half ^ stage ≤ epsilon := by
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
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ bound
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hbound)
    hscaledFinal

/-- Construct a `CReal` from a rational sequence equipped with an explicit
dyadic comparison to an already constructed `CReal`. -/
def crealOfDyadicallyClose
    (sequence : Nat → Q') (target : CReal)
    (bound : Q') (hbound : (0 : Q') ≤ bound)
    (hclose : ∀ stage : Nat,
      Q'.abs (sequence stage - target.approx stage) ≤
        bound * HalfPow.half ^ stage) : CReal where
  approx := sequence
  cauchy := by
    intro epsilon hepsilon
    let quarter := HalfPow.half * (HalfPow.half * epsilon)
    let halfEpsilon := HalfPow.half * epsilon
    have hquarter : (0 : Q') < quarter :=
      ExpNeg.half_mul_pos (HalfPow.half * epsilon)
        (ExpNeg.half_mul_pos epsilon hepsilon)
    have hhalfEpsilon : (0 : Q') < halfEpsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    obtain ⟨Nclose, hNclose⟩ :=
      dyadic_scaled_eventually_local bound hbound quarter hquarter
    obtain ⟨Ntarget, hNtarget⟩ := target.cauchy halfEpsilon hhalfEpsilon
    refine ⟨max Nclose Ntarget, fun m n hm hn => ?_⟩
    have hmClose : Q'.abs (sequence m - target.approx m) ≤ quarter :=
      Q'.le_trans' _ _ _ (hclose m)
        (hNclose m (Nat.le_trans (Nat.le_max_left _ _) hm))
    have hnCloseForward :
        Q'.abs (target.approx n - sequence n) ≤ quarter :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
            (target.approx n) (sequence n)))
        (Q'.le_trans' _ _ _ (hclose n)
          (hNclose n (Nat.le_trans (Nat.le_max_left _ _) hn)))
    have htarget := hNtarget m n
      (Nat.le_trans (Nat.le_max_right _ _) hm)
      (Nat.le_trans (Nat.le_max_right _ _) hn)
    have htargetAbs :
        Q'.abs (target.approx m - target.approx n) ≤ halfEpsilon :=
      CReal.abs_sub_le_of_bounds htarget.1 htarget.2
    have htail : Q'.abs (target.approx m - sequence n) ≤
        halfEpsilon + quarter :=
      Q'.le_trans' _ _ _
        (abs_sub_triangle_local
          (target.approx m) (sequence n) (target.approx n))
        (Q'.add_le_add htargetAbs hnCloseForward)
    have htotal : Q'.abs (sequence m - sequence n) ≤ epsilon := by
      refine Q'.le_trans' _ _ _
        (abs_sub_triangle_local
          (sequence m) (sequence n) (target.approx m)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hmClose htail) ?_
      exact Q'.le_of_eqv (quarter_half_quarter_eqv_local epsilon)
    exact two_sided_add_of_abs_sub_le_local htotal

private theorem crealOfDyadicallyClose_equiv_target
    (sequence : Nat → Q') (target : CReal)
    (bound : Q') (hbound : (0 : Q') ≤ bound)
    (hclose : ∀ stage : Nat,
      Q'.abs (sequence stage - target.approx stage) ≤
        bound * HalfPow.half ^ stage) :
    CReal.Equiv
      (crealOfDyadicallyClose sequence target bound hbound hclose) target := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    dyadic_scaled_eventually_local bound hbound epsilon hepsilon
  refine ⟨N, fun stage hstage => ?_⟩
  exact two_sided_add_of_abs_sub_le_local
    (Q'.le_trans' _ _ _ (hclose stage) (hN stage hstage))

private theorem creal_mul_congr_both_local
    {a a' b b' : CReal}
    (ha : CReal.Equiv a a') (hb : CReal.Equiv b b') :
    CReal.Equiv (CReal.mul a b) (CReal.mul a' b') := by
  refine CReal.Equiv.trans (CReal.mul_congr_left ha) ?_
  refine CReal.Equiv.trans (CRealAlg.cmul_comm a' b) ?_
  refine CReal.Equiv.trans (CReal.mul_congr_left hb) ?_
  exact CRealAlg.cmul_comm b' a'

/-! ## 1. The selected central even-volume cross form -/

def orientedDoubledTimeCentralBilinearSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) : Q' :=
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let cutoff := centralStrictJointCenteredStageCutoff outer stage
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace left.roots.length)
    (strictJointFingerprintSpace right.roots.length)
    left.coefficient right.coefficient
    (fun leftBits rightBits =>
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (centralAmbient radius)
        (sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            radius shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits)))

/-- The selected central event is literally the projected ordinary-joint
event used by the adjacent odd/even comparison theorem. -/
theorem orientedDoubledTimeCentralEvent_eq_projectedJoint
    {base : Nat} (shift stage : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    let outer := base + (shift + shift)
    let radius := strictQueryBase outer + stage
    let roots := orientedDoubledTimeJointRoots shift left right
    let hroots := orientedDoubledTimeJointRoots_canonical shift left right
    slabMarkedCylinderEvent
        (centralStrictJointCanonicalAtoms radius outer roots
          (Nat.le_add_right (strictQueryBase outer) stage) hroots)
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      sourceCylinderEvent
        (orientedDoubledTimeCommonCylinderRoots
          radius shift left right)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) := by
  dsimp only
  unfold slabMarkedCylinderEvent
  calc
    cylinderEvent
        ((centralStrictJointCanonicalAtoms
          (strictQueryBase (base + (shift + shift)) + stage)
          (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right)
          (Nat.le_add_right (strictQueryBase (base + (shift + shift))) stage)
          (orientedDoubledTimeJointRoots_canonical shift left right)).map
            Subtype.val)
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      cylinderEvent
        (centralStrictJointCylinderRoots
          (strictQueryBase (base + (shift + shift)) + stage)
          (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right))
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) := by
      apply congrArg (fun markedRoots => cylinderEvent markedRoots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits))
      exact centralStrictJointCanonicalAtoms_values
        (strictQueryBase (base + (shift + shift)) + stage)
        (base + (shift + shift))
        (orientedDoubledTimeJointRoots shift left right)
        (Nat.le_add_right (strictQueryBase (base + (shift + shift))) stage)
        (orientedDoubledTimeJointRoots_canonical shift left right)
    _ = _ := orientedDoubledTimeJointEvent_eq_common
      shift (strictQueryBase (base + (shift + shift)) + stage)
      left right leftBits rightBits

def orientedDoubledTimeCentralToCenteredCoefficient
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : Q' :=
  heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient *
    spinSummedCylinderBoundaryCoefficient
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length)

theorem orientedDoubledTimeCentralToCenteredCoefficient_nonnegative
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    (0 : Q') ≤ orientedDoubledTimeCentralToCenteredCoefficient
      shift left right := by
  unfold orientedDoubledTimeCentralToCenteredCoefficient
  exact Q'.mul_nonneg _ _
    (heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient)
    (spinSummedCylinderBoundaryCoefficient_nonnegative
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length))

/-- At every stage, the central even-volume cross form differs from the
ordinary centered joint bilinear by an explicit dyadic boundary term. -/
theorem orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs
        (orientedDoubledTimeCentralBilinearSequence
            coupling hcoupling shift left right stage -
          (orientedDoubledTimeJointCenteredBilinear
            coupling hcoupling hle shift left right).approx stage) ≤
      orientedDoubledTimeCentralToCenteredCoefficient shift left right *
        HalfPow.half ^ stage := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let cutoff := centralStrictJointCenteredStageCutoff outer stage
  let roots := orientedDoubledTimeJointRoots shift left right
  let hroots := orientedDoubledTimeJointRoots_canonical shift left right
  let statesLeft := strictJointFingerprintSpace left.roots.length
  let statesRight := strictJointFingerprintSpace right.roots.length
  let centralLaw : List Bool → List Bool → Q' :=
    fun leftBits rightBits =>
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (centralAmbient radius)
        (sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            radius shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits))
  let centeredLaw : List Bool → List Bool → Q' :=
    fun leftBits rightBits =>
      couplingParametricStrictJointCenteredSequence
        coupling hcoupling outer roots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) stage
  let epsilon := spinSummedCylinderBoundaryEpsilon
    (roots.length + roots.length) stage
  have hcentered :
      (orientedDoubledTimeJointCenteredBilinear
          coupling hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
          statesLeft statesRight left.coefficient right.coefficient
          centeredLaw := by
    simpa only [statesLeft, statesRight, centeredLaw, roots, outer] using
      (orientedDoubledTimeJointCenteredBilinear_approx_eqv
        hcoupling hle left right (shift := shift) (stage := stage))
  have hentry : ∀ leftBits rightBits,
      leftBits ∈ statesLeft → rightBits ∈ statesRight →
      Q'.abs (centralLaw leftBits rightBits -
        centeredLaw leftBits rightBits) ≤ epsilon := by
    intro leftBits rightBits hleft hright
    have hraw :=
      couplingParametricKCompatibleStrictJoint_cross_centered_abs_sub_le
        hcoupling hle cutoff hroots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits)
        (stage := stage)
    rw [orientedDoubledTimeCentralEvent_eq_projectedJoint
      shift stage left right leftBits rightBits] at hraw
    simpa only [centralLaw, centeredLaw, epsilon,
      couplingParametricStrictJointCenteredSequence,
      outer, radius, roots, hroots, cutoff,
      centralStrictJointCenteredCylinderEvent] using hraw
  have hfinite := finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    statesLeft statesRight left.coefficient right.coefficient
    centralLaw centeredLaw epsilon hentry
  have hleft :
      orientedDoubledTimeCentralBilinearSequence
          coupling hcoupling shift left right stage =
        finiteHeterogeneousCrossBilinear
          statesLeft statesRight left.coefficient right.coefficient
          centralLaw := by rfl
  have hdifference :
      orientedDoubledTimeCentralBilinearSequence
            coupling hcoupling shift left right stage -
          (orientedDoubledTimeJointCenteredBilinear
            coupling hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
            statesLeft statesRight left.coefficient right.coefficient
            centralLaw -
          finiteHeterogeneousCrossBilinear
            statesLeft statesRight left.coefficient right.coefficient
            centeredLaw := by
    rw [hleft]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ hcentered)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hfinite ?_)
  unfold orientedDoubledTimeCentralToCenteredCoefficient
  have hboundary : epsilon ≤
      spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
    exact spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hmul := Q'.mul_le_mul_of_nonneg_left
    epsilon
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length) * HalfPow.half ^ stage)
    (heterogeneousCoefficientPairL1
      statesLeft statesRight left.coefficient right.coefficient)
    hboundary
    (heterogeneousCoefficientPairL1_nonnegative
      statesLeft statesRight left.coefficient right.coefficient)
  refine Q'.le_trans' _ _ _ hmul ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv
    (heterogeneousCoefficientPairL1
      statesLeft statesRight left.coefficient right.coefficient)
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length))
    (HalfPow.half ^ stage)))

/-- A finite central cross form is bounded by its literal rectangular
coefficient `l1` norm because every normalized event probability lies in
`[0,1]`. -/
theorem orientedDoubledTimeCentralBilinearSequence_abs_le_pairL1
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs (orientedDoubledTimeCentralBilinearSequence
        coupling hcoupling shift left right stage) ≤
      heterogeneousCoefficientPairL1
        (strictJointFingerprintSpace left.roots.length)
        (strictJointFingerprintSpace right.roots.length)
        left.coefficient right.coefficient := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let cutoff := centralStrictJointCenteredStageCutoff outer stage
  let statesLeft := strictJointFingerprintSpace left.roots.length
  let statesRight := strictJointFingerprintSpace right.roots.length
  let law : List Bool → List Bool → Q' := fun leftBits rightBits =>
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff (centralAmbient radius)
      (sourceCylinderEvent
        (orientedDoubledTimeCommonCylinderRoots radius shift left right)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits))
  have hentry : ∀ leftBits rightBits,
      leftBits ∈ statesLeft → rightBits ∈ statesRight →
      Q'.abs (law leftBits rightBits) ≤ (1 : Q') := by
    intro leftBits rightBits hleft hright
    apply Q'.abs_le
    · exact Q'.le_trans' _ _ _ (by decide : (-(1 : Q')) ≤ 0)
        (couplingParametricKCompatibleSupportEventProbability_nonnegative
          hcoupling cutoff (centralAmbient radius) _)
    · exact couplingParametricKCompatibleSupportEventProbability_le_one
        hcoupling cutoff (centralAmbient radius) _
  have hfinite :=
    finiteHeterogeneousCrossBilinear_abs_le_of_entry_abs_le
      statesLeft statesRight left.coefficient right.coefficient law 1 hentry
  have hleft :
      orientedDoubledTimeCentralBilinearSequence
          coupling hcoupling shift left right stage =
        finiteHeterogeneousCrossBilinear
          statesLeft statesRight left.coefficient right.coefficient law := by
    rfl
  rw [hleft]
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.le_of_eqv (Q'.mul_one_eqv
      (heterogeneousCoefficientPairL1
        statesLeft statesRight left.coefficient right.coefficient)))

/-- The ordinary centered thermodynamic approximant obeys the same literal
rectangular coefficient bound. -/
theorem orientedDoubledTimeJointCenteredBilinear_approx_abs_le_pairL1
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs ((orientedDoubledTimeJointCenteredBilinear
        coupling hcoupling hle shift left right).approx stage) ≤
      heterogeneousCoefficientPairL1
        (strictJointFingerprintSpace left.roots.length)
        (strictJointFingerprintSpace right.roots.length)
        left.coefficient right.coefficient := by
  let statesLeft := strictJointFingerprintSpace left.roots.length
  let statesRight := strictJointFingerprintSpace right.roots.length
  let law : List Bool → List Bool → Q' := fun leftBits rightBits =>
    couplingParametricStrictJointCenteredSequence
      coupling hcoupling (base + (shift + shift))
      (orientedDoubledTimeJointRoots shift left right)
      (orientedDoubledTimeJointPredicate
        left.roots.length right.roots.length leftBits rightBits) stage
  have hentry : ∀ leftBits rightBits,
      leftBits ∈ statesLeft → rightBits ∈ statesRight →
      Q'.abs (law leftBits rightBits) ≤ (1 : Q') := by
    intro leftBits rightBits hleft hright
    apply Q'.abs_le
    · exact Q'.le_trans' _ _ _ (by decide : (-(1 : Q')) ≤ 0)
        (couplingParametricStrictJointCenteredSequence_nonnegative
          hcoupling (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right)
          (orientedDoubledTimeJointPredicate
            left.roots.length right.roots.length leftBits rightBits) stage)
    · exact couplingParametricStrictJointCenteredSequence_le_one
        hcoupling (base + (shift + shift))
        (orientedDoubledTimeJointRoots shift left right)
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) stage
  have hfinite :=
    finiteHeterogeneousCrossBilinear_abs_le_of_entry_abs_le
      statesLeft statesRight left.coefficient right.coefficient law 1 hentry
  have happrox := orientedDoubledTimeJointCenteredBilinear_approx_eqv
    hcoupling hle left right (shift := shift) (stage := stage)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr happrox))
    (Q'.le_trans' _ _ _ hfinite ?_)
  exact Q'.le_of_eqv (Q'.mul_one_eqv
    (heterogeneousCoefficientPairL1
      statesLeft statesRight left.coefficient right.coefficient))

/-! ## 2. Exact recoding as a two-block observable product -/

/-- The selected oriented roots are exactly the lower and upper root values
used by the arbitrary-cutoff geometric theorem.  The only non-definitional
step is that the lower observable was transported to the common outer box;
the strict lower query is independent of that numerical recoding. -/
theorem orientedDoubledTimeCommonCylinderRoots_eq_doubledTimeValues
    {base radius : Nat} (shift : Nat)
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    (left right : StrictJointCylinderVector base) :
    orientedDoubledTimeCommonCylinderRoots radius shift left right =
      strictJointDoubledTimeLowerRootValues
          radius base shift left.roots ++
      strictJointDoubledTimeUpperRootValues
          radius base shift right.roots := by
  have hlower :
      centralStrictLowerCylinderRoots radius (base + (shift + shift))
          (orientedDoubledTimeSource shift left).roots =
        strictJointDoubledTimeLowerRootValues
          radius base shift left.roots := by
    unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
      centralStrictLowerCylinderRoots
      strictJointDoubledTimeLowerRootValues
      strictJointDoubledTimeMixedLowerRoot
    simp only [List.map_map]
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictLowerCanonicalRoot_transportBase_eq
      (Nat.le_add_right base (shift + shift)) hadmissible
      (left.rootsCanonical root hroot)
  unfold orientedDoubledTimeCommonCylinderRoots
  dsimp only
  rw [hlower]
  unfold orientedDoubledTimeTarget timeTranslateStrictJointCylinderVector
    centralStrictUpperCylinderRoots
    strictJointDoubledTimeUpperRootValues
    strictJointDoubledTimeMixedUpperRoot
  rw [List.map_map]
  apply congrArg (fun upper =>
    strictJointDoubledTimeLowerRootValues
      radius base shift left.roots ++ upper)
  apply List.map_congr_left
  intro root hroot
  rfl

/-- The selected common-cylinder exact-fingerprint event is literally the
conjunction of the two block events used in the conventional observable
product expectation. -/
theorem orientedDoubledTimeCentralPairEvent_eq_blockPair
    {base radius : Nat} (shift : Nat)
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    sourceCylinderEvent
        (orientedDoubledTimeCommonCylinderRoots radius shift left right)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) =
      fun family =>
        blockCylinderEvent
            (strictJointDoubledTimeLowerRootAtoms
              hadmissible left.rootsCanonical)
            (exactFingerprintPredicate leftBits) family &&
          blockCylinderEvent
            (strictJointDoubledTimeUpperRootAtoms
              hadmissible right.rootsCanonical)
            (exactFingerprintPredicate rightBits) family := by
  funext family
  unfold sourceCylinderEvent cylinderEvent
    blockCylinderEvent exactFingerprintPredicate
    centralStrictJointPairPredicate
  rw [orientedDoubledTimeCommonCylinderRoots_eq_doubledTimeValues
    shift hadmissible left right]
  rw [familyOccurrenceFingerprint_append]
  rw [strictJointDoubledTimeLowerRootAtoms_values,
    strictJointDoubledTimeUpperRootAtoms_values]
  have hlowerLength :
      (familyOccurrenceFingerprint
        (strictJointDoubledTimeLowerRootValues
          radius base shift left.roots) family).length =
        left.roots.length := by
    rw [familyOccurrenceFingerprint_length]
    unfold strictJointDoubledTimeLowerRootValues
    simp only [List.length_map]
  rw [← hlowerLength, List.take_append_length,
    List.drop_append_length]
  simp

/-- The selected central cross bilinear is exactly the finite observable
product expectation on the geometric lower/upper root atoms. -/
theorem orientedDoubledTimeCentralBilinearSequence_eqv_productExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    orientedDoubledTimeCentralBilinearSequence
        coupling hcoupling shift left right stage ≈
      couplingParametricKTwoBlockProductExpectation hcoupling
        (centralStrictJointCenteredStageCutoff
          (base + (shift + shift)) stage)
        (strictJointDoubledTimeLowerRootAtoms
          (Nat.le_add_right
            (strictQueryBase (base + (shift + shift))) stage)
          left.rootsCanonical)
        (strictJointDoubledTimeUpperRootAtoms
          (Nat.le_add_right
            (strictQueryBase (base + (shift + shift))) stage)
          right.rootsCanonical)
        left.coefficient right.coefficient := by
  unfold orientedDoubledTimeCentralBilinearSequence
    couplingParametricKTwoBlockProductExpectation
    finiteHeterogeneousCrossBilinear
  simp only [strictJointDoubledTimeLowerRootAtoms_length,
    strictJointDoubledTimeUpperRootAtoms_length]
  apply listQSum_congr
  intro leftBits
  apply listQSum_congr
  intro rightBits
  rw [orientedDoubledTimeCentralPairEvent_eq_blockPair
    shift
    (Nat.le_add_right
      (strictQueryBase (base + (shift + shift))) stage)
    left right leftBits rightBits]
  exact Q'.eqv_refl _

private theorem twoBlockProductExpectation_empty_right_eqv_blockExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (roots : List (CanonicalAtom n))
    (coefficient : List Bool → Q') :
    couplingParametricKTwoBlockProductExpectation hcoupling cutoff
        roots [] coefficient (fun _ => 1) ≈
      couplingParametricKBlockObservableExpectation hcoupling cutoff
        roots coefficient := by
  unfold couplingParametricKTwoBlockProductExpectation
    couplingParametricKBlockObservableExpectation
    finiteHeterogeneousCrossBilinear
  simp only [List.length_nil, strictJointFingerprintSpace, listQSum]
  apply listQSum_congr
  intro bits
  have hevent :
      (fun family =>
        blockCylinderEvent roots (exactFingerprintPredicate bits) family &&
          blockCylinderEvent ([] : List (CanonicalAtom n))
            (exactFingerprintPredicate []) family) =
        blockCylinderEvent roots (exactFingerprintPredicate bits) := by
    funext family
    simp [blockCylinderEvent, exactFingerprintPredicate,
      familyOccurrenceFingerprint]
  rw [hevent]
  refine Q'.eqv_trans _
    ((coefficient bits * 1) *
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n
        (blockCylinderEvent roots (exactFingerprintPredicate bits))) _ ?_ ?_
  · exact YMGap.Constructive.QPoly.q_add_zero_eqv _
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)

private theorem twoBlockProductExpectation_empty_left_eqv_blockExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (roots : List (CanonicalAtom n))
    (coefficient : List Bool → Q') :
    couplingParametricKTwoBlockProductExpectation hcoupling cutoff
        [] roots (fun _ => 1) coefficient ≈
      couplingParametricKBlockObservableExpectation hcoupling cutoff
        roots coefficient := by
  unfold couplingParametricKTwoBlockProductExpectation
    couplingParametricKBlockObservableExpectation
    finiteHeterogeneousCrossBilinear
  simp only [List.length_nil, strictJointFingerprintSpace, listQSum]
  refine Q'.eqv_trans _
    (listQSum (fun bits =>
      (1 * coefficient bits) *
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n
          (blockCylinderEvent roots (exactFingerprintPredicate bits)))
      (strictJointFingerprintSpace roots.length)) _ ?_ ?_
  · exact YMGap.Constructive.QPoly.q_add_zero_eqv _
  · apply listQSum_congr
    intro bits
    have hevent :
        (fun family =>
          blockCylinderEvent ([] : List (CanonicalAtom n))
              (exactFingerprintPredicate []) family &&
            blockCylinderEvent roots (exactFingerprintPredicate bits) family) =
          blockCylinderEvent roots (exactFingerprintPredicate bits) := by
      funext family
      simp [blockCylinderEvent, exactFingerprintPredicate,
        familyOccurrenceFingerprint]
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)

/-- Pairing with the constant cylinder on the right extracts the lower-block
observable expectation from the central cross form. -/
theorem orientedDoubledTimeCentralBilinearSequence_vector_vacuum_eqv_lowerExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    orientedDoubledTimeCentralBilinearSequence coupling hcoupling
        shift vector (strictJointCylinderVacuum base) stage ≈
      couplingParametricKBlockObservableExpectation hcoupling
        (centralStrictJointCenteredStageCutoff
          (base + (shift + shift)) stage)
        (strictJointDoubledTimeLowerRootAtoms
          (Nat.le_add_right
            (strictQueryBase (base + (shift + shift))) stage)
          vector.rootsCanonical)
        vector.coefficient := by
  refine Q'.eqv_trans _ _ _
    (orientedDoubledTimeCentralBilinearSequence_eqv_productExpectation
      hcoupling shift vector (strictJointCylinderVacuum base) stage) ?_
  simpa only [strictJointCylinderVacuum] using
    (twoBlockProductExpectation_empty_right_eqv_blockExpectation
      hcoupling
      (centralStrictJointCenteredStageCutoff
        (base + (shift + shift)) stage)
      (strictJointDoubledTimeLowerRootAtoms
        (Nat.le_add_right
          (strictQueryBase (base + (shift + shift))) stage)
        vector.rootsCanonical)
      vector.coefficient)

/-- Pairing with the constant cylinder on the left extracts the upper-block
observable expectation from the central cross form. -/
theorem orientedDoubledTimeCentralBilinearSequence_vacuum_vector_eqv_upperExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    orientedDoubledTimeCentralBilinearSequence coupling hcoupling
        shift (strictJointCylinderVacuum base) vector stage ≈
      couplingParametricKBlockObservableExpectation hcoupling
        (centralStrictJointCenteredStageCutoff
          (base + (shift + shift)) stage)
        (strictJointDoubledTimeUpperRootAtoms
          (Nat.le_add_right
            (strictQueryBase (base + (shift + shift))) stage)
          vector.rootsCanonical)
        vector.coefficient := by
  refine Q'.eqv_trans _ _ _
    (orientedDoubledTimeCentralBilinearSequence_eqv_productExpectation
      hcoupling shift (strictJointCylinderVacuum base) vector stage) ?_
  simpa only [strictJointCylinderVacuum] using
    (twoBlockProductExpectation_empty_left_eqv_blockExpectation
      hcoupling
      (centralStrictJointCenteredStageCutoff
        (base + (shift + shift)) stage)
      (strictJointDoubledTimeUpperRootAtoms
        (Nat.le_add_right
          (strictQueryBase (base + (shift + shift))) stage)
        vector.rootsCanonical)
      vector.coefficient)

/-! ## 3. The central connected sequence and its geometric bound -/

/-- The ordinary centered observable moment on the same central even-volume
law as `orientedDoubledTimeCentralBilinearSequence`. -/
def orientedDoubledTimeCentralConnectedSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) : Q' :=
  couplingParametricKTwoBlockObservableCovariance hcoupling
    (centralStrictJointCenteredStageCutoff
      (base + (shift + shift)) stage)
    (strictJointDoubledTimeLowerRootAtoms
      (Nat.le_add_right
        (strictQueryBase (base + (shift + shift))) stage)
      vector.rootsCanonical)
    (strictJointDoubledTimeUpperRootAtoms
      (Nat.le_add_right
        (strictQueryBase (base + (shift + shift))) stage)
      vector.rootsCanonical)
    vector.coefficient vector.coefficient

/-- Every central connected approximant already has the common strict
geometric rate `1/16`; neither the stage nor the cutoff appears in the
presentation prefactor. -/
theorem orientedDoubledTimeCentralConnectedSequence_abs_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs (orientedDoubledTimeCentralConnectedSequence
        coupling hcoupling shift vector stage) ≤
      couplingParametricStrictSignedPositivePrefactor vector.roots.length
          (strictJointFingerprintSpace vector.roots.length)
          (strictJointFingerprintSpace vector.roots.length)
          vector.coefficient vector.coefficient *
        anchorDecoratedDoubledTimeRate ^ shift := by
  exact
    couplingParametricKStrictDoubledTimeObservableCovariance_abs_le_geometric
      hcoupling hle
      (centralStrictJointCenteredStageCutoff
        (base + (shift + shift)) stage)
      (Nat.le_add_right
        (strictQueryBase (base + (shift + shift))) stage)
      vector.rootsCanonical vector.coefficient vector.coefficient

/-- Finite centered-moment algebra in the central box: the observable
covariance is exactly joint cross form minus the product of the two
vacuum-paired one-point cross forms. -/
theorem orientedDoubledTimeCentralConnectedSequence_eqv_bilinearSub
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    orientedDoubledTimeCentralConnectedSequence
        coupling hcoupling shift vector stage ≈
      orientedDoubledTimeCentralBilinearSequence
          coupling hcoupling shift vector vector stage -
        orientedDoubledTimeCentralBilinearSequence coupling hcoupling
            shift vector (strictJointCylinderVacuum base) stage *
          orientedDoubledTimeCentralBilinearSequence coupling hcoupling
            shift (strictJointCylinderVacuum base) vector stage := by
  unfold orientedDoubledTimeCentralConnectedSequence
    couplingParametricKTwoBlockObservableCovariance
  have hjoint :=
    orientedDoubledTimeCentralBilinearSequence_eqv_productExpectation
      hcoupling shift vector vector stage
  have hlower :=
    orientedDoubledTimeCentralBilinearSequence_vector_vacuum_eqv_lowerExpectation
      hcoupling shift vector stage
  have hupper :=
    orientedDoubledTimeCentralBilinearSequence_vacuum_vector_eqv_upperExpectation
      hcoupling shift vector stage
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm hjoint)
    (Q'.neg_eqv_congr _ _
      (qmul_eqv_both_local
        (Q'.eqv_symm hlower) (Q'.eqv_symm hupper)))

/-! ## 4. Thermodynamic connected form and explicit comparison modulus -/

/-- The centered-limit version of the same joint-minus-means expression.
This is a genuine `CReal`; its approximants are the ordinary centered joint
laws already compared with the central even-volume laws above. -/
def orientedDoubledTimeJointCenteredConnectedForm
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  CReal.sub
    (orientedDoubledTimeJointCenteredBilinear
      coupling hcoupling hle shift vector vector)
    (CReal.mul
      (orientedDoubledTimeJointCenteredBilinear coupling hcoupling hle
        shift vector (strictJointCylinderVacuum base))
      (orientedDoubledTimeJointCenteredBilinear coupling hcoupling hle
        shift (strictJointCylinderVacuum base) vector))

/-- One explicit presentation-level coefficient controlling the whole
central-connected to centered-connected comparison. -/
def orientedDoubledTimeCentralConnectedComparisonCoefficient
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : Q' :=
  let vacuum := strictJointCylinderVacuum base
  let jointError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vector vector
  let lowerError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vector vacuum
  let upperError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vacuum vector
  let lowerBound := heterogeneousCoefficientPairL1
    (strictJointFingerprintSpace vector.roots.length)
    (strictJointFingerprintSpace vacuum.roots.length)
    vector.coefficient vacuum.coefficient
  let upperBound := heterogeneousCoefficientPairL1
    (strictJointFingerprintSpace vacuum.roots.length)
    (strictJointFingerprintSpace vector.roots.length)
    vacuum.coefficient vector.coefficient
  jointError + (lowerBound * upperError + upperBound * lowerError)

theorem orientedDoubledTimeCentralConnectedComparisonCoefficient_nonnegative
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    (0 : Q') ≤ orientedDoubledTimeCentralConnectedComparisonCoefficient
      shift vector := by
  unfold orientedDoubledTimeCentralConnectedComparisonCoefficient
  dsimp only
  apply Q'.zero_le_add
  · exact orientedDoubledTimeCentralToCenteredCoefficient_nonnegative
      shift vector vector
  · apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _
        (heterogeneousCoefficientPairL1_nonnegative
          (strictJointFingerprintSpace vector.roots.length)
          (strictJointFingerprintSpace
            (strictJointCylinderVacuum base).roots.length)
          vector.coefficient (strictJointCylinderVacuum base).coefficient)
        (orientedDoubledTimeCentralToCenteredCoefficient_nonnegative
          shift (strictJointCylinderVacuum base) vector)
    · exact Q'.mul_nonneg _ _
        (heterogeneousCoefficientPairL1_nonnegative
          (strictJointFingerprintSpace
            (strictJointCylinderVacuum base).roots.length)
          (strictJointFingerprintSpace vector.roots.length)
          (strictJointCylinderVacuum base).coefficient vector.coefficient)
        (orientedDoubledTimeCentralToCenteredCoefficient_nonnegative
          shift vector (strictJointCylinderVacuum base))

/-- The central connected observable moment converges to the centered
connected `CReal` with an explicit dyadic comparison coefficient. -/
theorem orientedDoubledTimeCentralConnectedSequence_abs_sub_centered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs
        (orientedDoubledTimeCentralConnectedSequence
            coupling hcoupling shift vector stage -
          (orientedDoubledTimeJointCenteredConnectedForm
            coupling hcoupling hle shift vector).approx stage) ≤
      orientedDoubledTimeCentralConnectedComparisonCoefficient shift vector *
        HalfPow.half ^ stage := by
  let vacuum := strictJointCylinderVacuum base
  let centralJoint := orientedDoubledTimeCentralBilinearSequence
    coupling hcoupling shift vector vector stage
  let centralLower := orientedDoubledTimeCentralBilinearSequence
    coupling hcoupling shift vector vacuum stage
  let centralUpper := orientedDoubledTimeCentralBilinearSequence
    coupling hcoupling shift vacuum vector stage
  let centeredJoint := (orientedDoubledTimeJointCenteredBilinear
    coupling hcoupling hle shift vector vector).approx stage
  let centeredLower := (orientedDoubledTimeJointCenteredBilinear
    coupling hcoupling hle shift vector vacuum).approx stage
  let centeredUpper := (orientedDoubledTimeJointCenteredBilinear
    coupling hcoupling hle shift vacuum vector).approx stage
  let jointError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vector vector
  let lowerError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vector vacuum
  let upperError :=
    orientedDoubledTimeCentralToCenteredCoefficient shift vacuum vector
  let lowerBound := heterogeneousCoefficientPairL1
    (strictJointFingerprintSpace vector.roots.length)
    (strictJointFingerprintSpace vacuum.roots.length)
    vector.coefficient vacuum.coefficient
  let upperBound := heterogeneousCoefficientPairL1
    (strictJointFingerprintSpace vacuum.roots.length)
    (strictJointFingerprintSpace vector.roots.length)
    vacuum.coefficient vector.coefficient
  let rate := HalfPow.half ^ stage
  have hsequence :
      orientedDoubledTimeCentralConnectedSequence
          coupling hcoupling shift vector stage ≈
        centralJoint - centralLower * centralUpper := by
    simpa only [vacuum, centralJoint, centralLower, centralUpper] using
      (orientedDoubledTimeCentralConnectedSequence_eqv_bilinearSub
        hcoupling shift vector stage)
  have hcentered :
      (orientedDoubledTimeJointCenteredConnectedForm
        coupling hcoupling hle shift vector).approx stage =
        centeredJoint - centeredLower * centeredUpper := by
    rfl
  have hdifference :
      orientedDoubledTimeCentralConnectedSequence
            coupling hcoupling shift vector stage -
          (orientedDoubledTimeJointCenteredConnectedForm
            coupling hcoupling hle shift vector).approx stage ≈
        (centralJoint - centeredJoint) +
          -(centralLower * centralUpper -
            centeredLower * centeredUpper) := by
    rw [hcentered]
    refine Q'.eqv_trans _
      ((centralJoint - centralLower * centralUpper) -
        (centeredJoint - centeredLower * centeredUpper)) _ ?_ ?_
    · exact Q'.add_eqv_congr' hsequence (Q'.eqv_refl _)
    · exact sub_sub_rearrange_local
        centralJoint (centralLower * centralUpper)
        centeredJoint (centeredLower * centeredUpper)
  have hjointError : Q'.abs (centralJoint - centeredJoint) ≤
      jointError * rate := by
    exact orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
      hcoupling hle shift vector vector stage
  have hlowerError : Q'.abs (centralLower - centeredLower) ≤
      lowerError * rate := by
    exact orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
      hcoupling hle shift vector vacuum stage
  have hupperError : Q'.abs (centralUpper - centeredUpper) ≤
      upperError * rate := by
    exact orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
      hcoupling hle shift vacuum vector stage
  have hcentralLower : Q'.abs centralLower ≤ lowerBound := by
    exact orientedDoubledTimeCentralBilinearSequence_abs_le_pairL1
      hcoupling shift vector vacuum stage
  have hcenteredUpper : Q'.abs centeredUpper ≤ upperBound := by
    exact orientedDoubledTimeJointCenteredBilinear_approx_abs_le_pairL1
      hcoupling hle shift vacuum vector stage
  have hlowerBound : (0 : Q') ≤ lowerBound := by
    exact heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace vector.roots.length)
      (strictJointFingerprintSpace vacuum.roots.length)
      vector.coefficient vacuum.coefficient
  have hupperBound : (0 : Q') ≤ upperBound := by
    exact heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace vacuum.roots.length)
      (strictJointFingerprintSpace vector.roots.length)
      vacuum.coefficient vector.coefficient
  have hproduct :
      Q'.abs (centralLower * centralUpper -
          centeredLower * centeredUpper) ≤
        lowerBound * (upperError * rate) +
          upperBound * (lowerError * rate) :=
    abs_mul_sub_mul_le_local hlowerBound hupperBound
      hcentralLower hcenteredUpper hupperError hlowerError
  have hproductNeg :
      Q'.abs (-(centralLower * centralUpper -
          centeredLower * centeredUpper)) ≤
        lowerBound * (upperError * rate) +
          upperBound * (lowerError * rate) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_neg'
        (centralLower * centralUpper - centeredLower * centeredUpper)))
      hproduct
  have hraw :
      Q'.abs ((centralJoint - centeredJoint) +
          -(centralLower * centralUpper -
            centeredLower * centeredUpper)) ≤
        jointError * rate +
          (lowerBound * (upperError * rate) +
            upperBound * (lowerError * rate)) := by
    exact Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add hjointError hproductNeg)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hraw ?_)
  unfold orientedDoubledTimeCentralConnectedComparisonCoefficient
  dsimp only
  exact Q'.le_of_eqv (factor_three_rate_local
    jointError lowerBound upperError upperBound lowerError rate)

/-- The receding-volume central connected covariance as a separately
constructed Bishop real, with its Cauchy modulus supplied by the explicit
dyadic comparison above. -/
def orientedDoubledTimeCentralConnectedLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  crealOfDyadicallyClose
    (orientedDoubledTimeCentralConnectedSequence
      coupling hcoupling shift vector)
    (orientedDoubledTimeJointCenteredConnectedForm
      coupling hcoupling hle shift vector)
    (orientedDoubledTimeCentralConnectedComparisonCoefficient shift vector)
    (orientedDoubledTimeCentralConnectedComparisonCoefficient_nonnegative
      shift vector)
    (orientedDoubledTimeCentralConnectedSequence_abs_sub_centered_le
      hcoupling hle shift vector)

@[simp] theorem orientedDoubledTimeCentralConnectedLimit_approx
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift stage : Nat)
    (vector : StrictJointCylinderVector base) :
    (orientedDoubledTimeCentralConnectedLimit
      coupling hcoupling hle shift vector).approx stage =
        orientedDoubledTimeCentralConnectedSequence
          coupling hcoupling shift vector stage := rfl

/-- The independently constructed central connected limit is the same
constructive real as the centered joint-minus-means form. -/
theorem orientedDoubledTimeCentralConnectedLimit_equiv_centered
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeCentralConnectedLimit
        coupling hcoupling hle shift vector)
      (orientedDoubledTimeJointCenteredConnectedForm
        coupling hcoupling hle shift vector) :=
  crealOfDyadicallyClose_equiv_target
    (orientedDoubledTimeCentralConnectedSequence
      coupling hcoupling shift vector)
    (orientedDoubledTimeJointCenteredConnectedForm
      coupling hcoupling hle shift vector)
    (orientedDoubledTimeCentralConnectedComparisonCoefficient shift vector)
    (orientedDoubledTimeCentralConnectedComparisonCoefficient_nonnegative
      shift vector)
    (orientedDoubledTimeCentralConnectedSequence_abs_sub_centered_le
      hcoupling hle shift vector)

/-- The centered joint-minus-means form is exactly the literal connected
doubled-time OS form.  This closes the analytic and algebraic halves of the
same-object bridge before any vacuum-orthogonality simplification. -/
theorem orientedDoubledTimeJointCenteredConnectedForm_equiv_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeJointCenteredConnectedForm
        coupling hcoupling hle shift vector)
      (strictJointDoubledTimeConnectedForm
        hcoupling hle shift vector) := by
  have hjoint : CReal.Equiv
      (orientedDoubledTimeJointCenteredBilinear
        coupling hcoupling hle shift vector vector)
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift vector) := by
    simpa only [orientedDoubledTimeReflectionBilinear,
      orientedDoubledTimeSource, orientedDoubledTimeTarget,
      strictJointDoubledTimeMixedOSBilinear,
      strictJointDoubledTimeMixedSource,
      strictJointDoubledTimeMixedTarget] using
      CReal.Equiv.symm
        (orientedDoubledTimeReflectionBilinear_equiv_jointCentered
          hcoupling hle shift vector vector)
  have hlower : CReal.Equiv
      (orientedDoubledTimeJointCenteredBilinear coupling hcoupling hle
        shift vector (strictJointCylinderVacuum base))
      (strictJointDoubledTimeLowerMean hcoupling hle shift vector) := by
    simpa only [orientedDoubledTimeReflectionBilinear,
      orientedDoubledTimeSource, orientedDoubledTimeTarget,
      strictJointDoubledTimeLowerMean,
      strictJointDoubledTimeMixedSource,
      timeTranslateStrictJointCylinderVacuum] using
      CReal.Equiv.symm
        (orientedDoubledTimeReflectionBilinear_equiv_jointCentered
          hcoupling hle shift vector (strictJointCylinderVacuum base))
  have hupper : CReal.Equiv
      (orientedDoubledTimeJointCenteredBilinear coupling hcoupling hle
        shift (strictJointCylinderVacuum base) vector)
      (strictJointDoubledTimeUpperMean hcoupling hle shift vector) := by
    simpa only [orientedDoubledTimeReflectionBilinear,
      orientedDoubledTimeSource, orientedDoubledTimeTarget,
      strictJointDoubledTimeUpperMean,
      strictJointDoubledTimeMixedTarget,
      boxTransportStrictJointCylinderVacuum] using
      CReal.Equiv.symm
        (orientedDoubledTimeReflectionBilinear_equiv_jointCentered
          hcoupling hle shift (strictJointCylinderVacuum base) vector)
  unfold orientedDoubledTimeJointCenteredConnectedForm
    strictJointDoubledTimeConnectedForm
  exact CReal.Equiv.trans (CReal.sub_congr_left hjoint)
    (CReal.sub_congr_right
      (creal_mul_congr_both_local hlower hupper))

/-- The independently constructed receding-volume connected covariance is
the literal dense connected transfer form. -/
theorem orientedDoubledTimeCentralConnectedLimit_equiv_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeCentralConnectedLimit
        coupling hcoupling hle shift vector)
      (strictJointDoubledTimeConnectedForm
        hcoupling hle shift vector) :=
  CReal.Equiv.trans
    (orientedDoubledTimeCentralConnectedLimit_equiv_centered
      hcoupling hle shift vector)
    (orientedDoubledTimeJointCenteredConnectedForm_equiv_connected
      hcoupling hle shift vector)

/-- On the dense vacuum complement, the completed two-step autocorrelation
is represented by the independently constructed receding-volume central
connected covariance. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)) shift =
      Quotient.mk CReal.crealSetoid
        (orientedDoubledTimeCentralConnectedLimit
          coupling hcoupling hle shift vector) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_connected
    hcoupling hle shift vector horthogonal]
  apply Quotient.sound
  exact CReal.Equiv.symm
    (orientedDoubledTimeCentralConnectedLimit_equiv_connected
      hcoupling hle shift vector)

/-- Presentation-level geometric decay for the actual completed same-object
autocorrelation of a dense vacuum-orthogonal vector.  This is not yet a
uniform operator bound because the prefactor still depends on the chosen
cylinder presentation. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)) shift)
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (couplingParametricStrictSignedPositivePrefactor vector.roots.length
              (strictJointFingerprintSpace vector.roots.length)
              (strictJointFingerprintSpace vector.roots.length)
              vector.coefficient vector.coefficient *
            anchorDecoratedDoubledTimeRate ^ shift))) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
    hcoupling hle shift vector horthogonal]
  change CReal.leEv
    (orientedDoubledTimeCentralConnectedLimit
      coupling hcoupling hle shift vector)
    (CReal.ofQ'
      (couplingParametricStrictSignedPositivePrefactor vector.roots.length
          (strictJointFingerprintSpace vector.roots.length)
          (strictJointFingerprintSpace vector.roots.length)
          vector.coefficient vector.coefficient *
        anchorDecoratedDoubledTimeRate ^ shift))
  intro epsilon hepsilon
  refine ⟨0, fun stage hstage => ?_⟩
  rw [orientedDoubledTimeCentralConnectedLimit_approx,
    CReal.ofQ'_approx]
  refine Q'.le_trans' _ _ _
    (Q'.le_abs_self
      (orientedDoubledTimeCentralConnectedSequence
        coupling hcoupling shift vector stage)) ?_
  refine Q'.le_trans' _ _ _
    (orientedDoubledTimeCentralConnectedSequence_abs_le_geometric
      hcoupling hle shift vector stage) ?_
  exact Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)

/-- The thermodynamic central connected `CReal` inherits the exact common
`1/16` envelope from every finite central approximant. -/
theorem orientedDoubledTimeCentralConnectedLimit_abs_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.abs
        (orientedDoubledTimeCentralConnectedLimit
          coupling hcoupling hle shift vector) ≤
      CReal.ofQ'
        (couplingParametricStrictSignedPositivePrefactor vector.roots.length
            (strictJointFingerprintSpace vector.roots.length)
            (strictJointFingerprintSpace vector.roots.length)
            vector.coefficient vector.coefficient *
          anchorDecoratedDoubledTimeRate ^ shift) := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  rw [CReal.abs_approx,
    orientedDoubledTimeCentralConnectedLimit_approx]
  exact orientedDoubledTimeCentralConnectedSequence_abs_le_geometric
    hcoupling hle shift vector stage

#print axioms orientedDoubledTimeCentralEvent_eq_projectedJoint
#print axioms orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
#print axioms orientedDoubledTimeCommonCylinderRoots_eq_doubledTimeValues
#print axioms orientedDoubledTimeCentralPairEvent_eq_blockPair
#print axioms orientedDoubledTimeCentralBilinearSequence_eqv_productExpectation
#print axioms orientedDoubledTimeCentralConnectedSequence_abs_le_geometric
#print axioms orientedDoubledTimeCentralConnectedSequence_eqv_bilinearSub
#print axioms orientedDoubledTimeCentralConnectedComparisonCoefficient_nonnegative
#print axioms orientedDoubledTimeCentralConnectedSequence_abs_sub_centered_le
#print axioms orientedDoubledTimeCentralConnectedLimit
#print axioms orientedDoubledTimeCentralConnectedLimit_equiv_centered
#print axioms orientedDoubledTimeJointCenteredConnectedForm_equiv_connected
#print axioms orientedDoubledTimeCentralConnectedLimit_equiv_connected
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_geometric
#print axioms orientedDoubledTimeCentralConnectedLimit_abs_le_geometric

end YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
