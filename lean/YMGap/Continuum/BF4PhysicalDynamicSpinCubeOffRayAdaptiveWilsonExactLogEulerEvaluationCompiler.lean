/-
# Exact-log Euler evaluation for the adaptive Wilson rate

The dynamic scalar path already proves two separate facts about one cutoff
family.  First, its physical-gap stream converges to the exact logarithm of
the separator selected by the Wilson reconstruction.  Second, the scheduled
one-time rate powers and their upper Euler exponentials converge to one common
constructive limit.  The remaining analytic statement is the corresponding
logarithm/exponential evaluation: that the upper Euler exponential converges
to the square of that same rational separator.

This module isolates exactly that statement as
`DynamicVacuumSectorWilsonExactLogEulerEvaluation`.  The record is indexed by
the same family, gap variation, Wilson datum, and exact-rate handoff, so it
cannot be paired with an unrelated logarithm or separator.  All surrounding
work is compiled here:

* the upper rational exponents converge to the exact Wilson logarithmic
  exponent at every physical time;
* one upper-endpoint evaluation at time one identifies the already-constructed
  scheduled-power limit by uniqueness; and
* the literal scheduled finite rate stream consequently converges to the
  selected separator square required by the all-vector graph-norm compiler.

The Euler evaluation record is deliberately not inhabited.  In particular,
this file does not pretend that the repository already contains a general
constructive `exp (-log q) = q` theorem.  No adaptive family, evaluation,
graph-norm approximation, projective measure, continuum Yang--Mills theory,
or Clay conclusion is constructed here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealExpRationalStreamContinuity
import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealExpRationalStreamContinuity
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. The exact logarithmic exponent already selected by Wilson data -/

/-- The physical-time exponent obtained by replacing the dynamic gap limit by
the exact logarithm of the separator selected by the same Wilson datum. -/
def selectedWilsonExactPhysicalTimeExponent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (time : Nat) : CReal :=
  CReal.mul
    (CReal.mul
      (exactLogGap D.reconstruction positiveGapBound)
      (CReal.add CReal.cone CReal.cone))
    (CReal.ofQ' (Q'.ofNat time))

/-- Every approximation of the exact Wilson logarithmic gap is nonnegative.
This strengthens the existing limit-level strict positivity only at the
representation actually used here.  The binary `k * log 2` summand has
nonnegative partial sums, while the mantissa lies below one, so its artanh
partial sums are nonpositive and their negation is nonnegative. -/
theorem exactLogGap_approx_nonnegative
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu)
    (positiveGapBound : PositiveTransferGapBound rec)
    (stage : Nat) :
    (0 : Q') <= (exactLogGap rec positiveGapBound).approx stage := by
  let mantissa : Q' := gapMantissa rec positiveGapBound
  let hm1 : (0 : Q') < mantissa + 1 :=
    gapMantissaPlusOne_pos rec positiveGapBound
  let hyb : Q'.abs (CRealLog.yOf mantissa hm1) <= CRealLog.recipOdd 1 :=
    gapMantissa_window rec positiveGapBound
  have hyNonpositive : CRealLog.yOf mantissa hm1 <= (0 : Q') :=
    Q'.le_of_lt
      (YMGap.Continuum.yOf_sep_neg mantissa hm1
        (gapMantissa_lt_one rec positiveGapBound))
  have hpartial : CRealLog.partialSum (CRealLog.yOf mantissa hm1) stage <= 0 := by
    have hanti := CRealLog.partialSum_anti_of_nonpos
      (CRealLog.yOf mantissa hm1) hyNonpositive 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hanti
    exact hanti
  have hlog : (CRealLog.logRat mantissa hm1 hyb).approx stage <= 0 := by
    rw [CRealLog.logRat_approx]
    have hsum := Q'.add_le_add hpartial hpartial
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (by decide : ((0 : Q') + 0).eqv 0))
  have hnegLog : (0 : Q') <=
      (CReal.neg (CRealLog.logRat mantissa hm1 hyb)).approx stage :=
    Q'.nonneg_neg_of_nonpos hlog
  change (0 : Q') <=
    (HamiltonianAllSep.kLog2 (gapBinExp rec positiveGapBound).k).approx stage +
      (CReal.neg (CRealLog.logRat mantissa hm1 hyb)).approx stage
  exact Q'.zero_le_add _ _
    (HamiltonianAllSep.kLog2_approx_nonneg
      (gapBinExp rec positiveGapBound).k stage)
    hnegLog

/-- Pointwise nonnegativity of every canonical rational approximation of the
selected physical-time exponent.  This is the sign datum required by rational
`expNeg`; unlike `ExpNegCData`, it imposes no global upper bound. -/
theorem selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (time stage : Nat) :
    (0 : Q') <=
      (selectedWilsonExactPhysicalTimeExponent
        D positiveGapBound time).approx stage := by
  show (0 : Q') <=
    ((exactLogGap D.reconstruction positiveGapBound).approx stage *
      ((1 : Q') + 1)) * Q'.ofNat time
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (exactLogGap_approx_nonnegative
        D.reconstruction positiveGapBound stage)
      (by decide))
    (ExpNeg.ofNat_nonneg' time)

/-- The actual upper Euler exponent stream converges to the exact Wilson
logarithmic exponent.  This is fully derived from the same-stream exact-rate
handoff; the exponential evaluation itself is the next, separate frontier. -/
theorem scheduledSquaredRateUpperExponent_converges_selectedWilsonExact
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (scheduledSquaredRateUpperExponent family scale time))
      (selectedWilsonExactPhysicalTimeExponent
        D exactRate.positiveGapBound time) := by
  have hgap := exactRate.physicalGapLimit_equiv_exactLog
  have hinner : CReal.Equiv
      (CReal.mul gapVariation.limit (CReal.add CReal.cone CReal.cone))
      (CReal.mul
        (exactLogGap D.reconstruction exactRate.positiveGapBound)
        (CReal.add CReal.cone CReal.cone)) :=
    CReal.mul_congr_left hgap
  have hexponent : CReal.Equiv
      (scheduledSquaredRatePhysicalExponentLimit gapVariation time)
      (selectedWilsonExactPhysicalTimeExponent
        D exactRate.positiveGapBound time) :=
    CReal.mul_congr_left hinner
  exact CReal.convergesTo_limit_congr
    (scheduledSquaredRateUpperExponent_converges
      family band gapVariation time)
    hexponent

/-! ## 2. The one remaining exact-log Euler evaluation -/

/-- The rational exponent stream for the dyadic part of the separator-square
identity: twice the `k * log 2` approximant. -/
def dyadicLogSquareExponent (k stage : Nat) : Q' :=
  (HamiltonianAllSep.kLog2 k).approx stage * ((1 : Q') + 1)

/-- Pointwise nonnegativity of the dyadic exponent stream. -/
theorem dyadicLogSquareExponent_nonnegative (k stage : Nat) :
    (0 : Q') <= dyadicLogSquareExponent k stage :=
  Q'.mul_nonneg _ _
    (HamiltonianAllSep.kLog2_approx_nonneg k stage) (by decide)

/-- The rational exponent stream for the reduced-mantissa part of the
separator-square identity: twice the negative logarithm approximant. -/
def mantissaLogSquareExponent
    (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (CRealLog.yOf m hm1) <= CRealLog.recipOdd 1)
    (stage : Nat) : Q' :=
  (CReal.neg (CRealLog.logRat m hm1 hyb)).approx stage *
    ((1 : Q') + 1)

/-- Every direct-window logarithm approximant is nonpositive when its rational
argument lies below one. -/
theorem logRat_approx_nonpositive_of_lt_one
    (m : Q') (hm1 : (0 : Q') < m + 1) (hlt : m < (1 : Q'))
    (hyb : Q'.abs (CRealLog.yOf m hm1) <= CRealLog.recipOdd 1)
    (stage : Nat) :
    (CRealLog.logRat m hm1 hyb).approx stage <= (0 : Q') := by
  have hyNonpositive : CRealLog.yOf m hm1 <= (0 : Q') :=
    Q'.le_of_lt (YMGap.Continuum.yOf_sep_neg m hm1 hlt)
  have hpartial : CRealLog.partialSum (CRealLog.yOf m hm1) stage <= 0 := by
    have hanti := CRealLog.partialSum_anti_of_nonpos
      (CRealLog.yOf m hm1) hyNonpositive 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hanti
    exact hanti
  rw [CRealLog.logRat_approx]
  have hsum := Q'.add_le_add hpartial hpartial
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (by decide : ((0 : Q') + 0).eqv 0))

/-- Pointwise nonnegativity of the reduced-mantissa exponent stream. -/
theorem mantissaLogSquareExponent_nonnegative
    (m : Q') (hm1 : (0 : Q') < m + 1) (hlt : m < (1 : Q'))
    (hyb : Q'.abs (CRealLog.yOf m hm1) <= CRealLog.recipOdd 1)
    (stage : Nat) :
    (0 : Q') <= mantissaLogSquareExponent m hm1 hyb stage :=
  Q'.mul_nonneg _ _
    (Q'.nonneg_neg_of_nonpos
      (logRat_approx_nonpositive_of_lt_one m hm1 hlt hyb stage))
    (by decide)

/-- The first independent atomic inverse frontier.  It identifies the
negative exponential of twice `k * log 2` with the square of `2^-k`.
The record is static and depends only on the computable dyadic exponent. -/
structure DyadicLogSquareEulerEvaluation (k : Nat) : Type 1 where
  exponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      (dyadicLogSquareExponent k stage)
      (dyadicLogSquareExponent_nonnegative k stage))
    (CReal.ofQ'
      (HamiltonianAllSep.scaleQ k * HamiltonianAllSep.scaleQ k))

/-- The second independent atomic inverse frontier.  It identifies the
negative exponential of twice the negative direct-window logarithm with the
square of the reduced mantissa. -/
structure MantissaLogSquareEulerEvaluation
    (m : Q') (hm1 : (0 : Q') < m + 1) (hlt : m < (1 : Q'))
    (hyb : Q'.abs (CRealLog.yOf m hm1) <= CRealLog.recipOdd 1) : Type 1 where
  exponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      (mantissaLogSquareExponent m hm1 hyb stage)
      (mantissaLogSquareExponent_nonnegative m hm1 hlt hyb stage))
    (CReal.ofQ' (m * m))

/-- The dyadic square exponent at `k+1` is the sum of the one-copy
`log 2` square exponent and the exponent at `k`. -/
theorem dyadicLogSquareExponent_one_add_eqv_succ (k stage : Nat) :
    (dyadicLogSquareExponent 1 stage +
      dyadicLogSquareExponent k stage).eqv
    (dyadicLogSquareExponent (k + 1) stage) := by
  let A : Q' := CRealLog.log2.approx stage
  let B : Q' := (HamiltonianAllSep.kLog2 k).approx stage
  let two : Q' := (1 : Q') + 1
  change (((A + 0) * two) + (B * two)).eqv ((A + B) * two)
  refine Q'.eqv_trans _ ((A * two) + (B * two)) _ ?_ ?_
  · exact ExpNeg.add_eqv_congr2
      (Q'.mul_eqv_congr_right (A + 0) A two
        (QPoly.q_add_zero_eqv A))
      (Q'.eqv_refl (B * two))
  · refine Q'.eqv_trans _ ((two * A) + (two * B)) _ ?_ ?_
    · exact ExpNeg.add_eqv_congr2
        (Q'.mul_comm_eqv A two) (Q'.mul_comm_eqv B two)
    · exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv two A B))
        (Q'.mul_comm_eqv two (A + B))

/-- Termwise exponential multiplication for the dyadic successor step. -/
theorem dyadicLogSquareExponential_one_mul_equiv_succ (k stage : Nat) :
    CReal.Equiv
      (CReal.mul
        (ExpNeg.expNeg
          (dyadicLogSquareExponent 1 stage)
          (dyadicLogSquareExponent_nonnegative 1 stage))
        (ExpNeg.expNeg
          (dyadicLogSquareExponent k stage)
          (dyadicLogSquareExponent_nonnegative k stage)))
      (ExpNeg.expNeg
        (dyadicLogSquareExponent (k + 1) stage)
        (dyadicLogSquareExponent_nonnegative (k + 1) stage)) :=
  CReal.Equiv.trans
    (expNeg_add_equiv
      (dyadicLogSquareExponent 1 stage)
      (dyadicLogSquareExponent k stage)
      (dyadicLogSquareExponent_nonnegative 1 stage)
      (dyadicLogSquareExponent_nonnegative k stage))
    (expNeg_eqv_congr
      (Q'.zero_le_add _ _
        (dyadicLogSquareExponent_nonnegative 1 stage)
        (dyadicLogSquareExponent_nonnegative k stage))
      (dyadicLogSquareExponent_nonnegative (k + 1) stage)
      (dyadicLogSquareExponent_one_add_eqv_succ k stage))

/-- The exact dyadic rational scale satisfies
`scaleQ 1 * scaleQ k = scaleQ (k+1)`. -/
theorem scaleQ_one_mul_scaleQ_eqv_succ (k : Nat) :
    (HamiltonianAllSep.scaleQ 1 * HamiltonianAllSep.scaleQ k).eqv
      (HamiltonianAllSep.scaleQ (k + 1)) := by
  unfold HamiltonianAllSep.scaleQ
  show
    ((Q'.mkPos 1 (2 ^ 1) (Nat.two_pow_pos 1) *
        Q'.mkPos 1 (2 ^ k) (Nat.two_pow_pos k)).num *
      ((Q'.mkPos 1 (2 ^ (k + 1))
        (Nat.two_pow_pos (k + 1))).den : Int)) =
    ((Q'.mkPos 1 (2 ^ (k + 1))
        (Nat.two_pow_pos (k + 1))).num *
      ((Q'.mkPos 1 (2 ^ 1) (Nat.two_pow_pos 1) *
        Q'.mkPos 1 (2 ^ k) (Nat.two_pow_pos k)).den : Int))
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_num, Q'.mkPos_den]
  simp only [Nat.pow_one, Int.one_mul]
  rw [Nat.pow_succ, Int.natCast_mul]
  exact Int.mul_comm _ _

/-- Squaring the dyadic successor scale factors into the square at one and
the square at `k`. -/
theorem scaleQ_square_one_mul_square_eqv_succ (k : Nat) :
    ((HamiltonianAllSep.scaleQ 1 * HamiltonianAllSep.scaleQ 1) *
      (HamiltonianAllSep.scaleQ k * HamiltonianAllSep.scaleQ k)).eqv
    (HamiltonianAllSep.scaleQ (k + 1) *
      HamiltonianAllSep.scaleQ (k + 1)) := by
  let s1 := HamiltonianAllSep.scaleQ 1
  let sk := HamiltonianAllSep.scaleQ k
  let sn := HamiltonianAllSep.scaleQ (k + 1)
  have hStep : (s1 * sk).eqv sn := scaleQ_one_mul_scaleQ_eqv_succ k
  have hShuffle : ((s1 * s1) * (sk * sk)).eqv
      ((s1 * sk) * (s1 * sk)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s1 s1 (sk * sk)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left s1 _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv s1 sk sk))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv s1 (s1 * sk) sk)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (s1 * (s1 * sk)) ((s1 * sk) * s1) sk
        (Q'.mul_comm_eqv s1 (s1 * sk))) ?_
    exact Q'.mul_assoc_eqv (s1 * sk) s1 sk
  refine Q'.eqv_trans _ _ _ hShuffle ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (s1 * sk) sn (s1 * sk) hStep) ?_
  exact Q'.mul_eqv_congr_left sn (s1 * sk) sn hStep

namespace DyadicLogSquareEulerEvaluation

/-- The zero-copy dyadic evaluator is constructive without an analytic
inverse input: its exponent is identically zero and its target scale is one. -/
def zero : DyadicLogSquareEulerEvaluation 0 where
  exponentialConverges := by
    have hTerm : forall stage : Nat, CReal.Equiv
        (ExpNeg.expNeg
          (dyadicLogSquareExponent 0 stage)
          (dyadicLogSquareExponent_nonnegative 0 stage))
        CReal.cone := by
      intro stage
      have hArg : (dyadicLogSquareExponent 0 stage).eqv (0 : Q') := by
        unfold dyadicLogSquareExponent HamiltonianAllSep.kLog2
        change ((0 : Q') * ((1 : Q') + 1)).eqv 0
        ring_qeqv
      exact CReal.Equiv.trans
        (expNeg_eqv_congr
          (dyadicLogSquareExponent_nonnegative 0 stage)
          (by decide) hArg)
        (CReal.expNeg_zero_equiv_cone (by decide))
    have hCone : CReal.ConvergesTo (fun _ : Nat => CReal.cone) CReal.cone :=
      CReal.convergesTo_const CReal.cone
    have hSequence : CReal.ConvergesTo
        (fun stage => ExpNeg.expNeg
          (dyadicLogSquareExponent 0 stage)
          (dyadicLogSquareExponent_nonnegative 0 stage))
        CReal.cone :=
      YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
        (fun stage => (hTerm stage).symm) hCone
    exact CReal.convergesTo_limit_congr hSequence
      (TrigAdd.equiv_ofQ'_of_eqv
        (by decide : (1 : Q').eqv
          (HamiltonianAllSep.scaleQ 0 * HamiltonianAllSep.scaleQ 0)))

/-- A single evaluator at `k=1` generates the evaluator at every natural
dyadic exponent.  The successor compiler uses only the exponential addition
law, constructive multiplication continuity, and exact dyadic rational
algebra; no further logarithm/exponential inverse input is required. -/
def allOfOne (one : DyadicLogSquareEulerEvaluation 1) :
    (k : Nat) -> DyadicLogSquareEulerEvaluation k
  | 0 => zero
  | k + 1 => by
      let previous := allOfOne one k
      refine { exponentialConverges := ?_ }
      have hProduct : CReal.ConvergesTo
          (fun stage => CReal.mul
            (ExpNeg.expNeg
              (dyadicLogSquareExponent 1 stage)
              (dyadicLogSquareExponent_nonnegative 1 stage))
            (ExpNeg.expNeg
              (dyadicLogSquareExponent k stage)
              (dyadicLogSquareExponent_nonnegative k stage)))
          (CReal.mul
            (CReal.ofQ'
              (HamiltonianAllSep.scaleQ 1 * HamiltonianAllSep.scaleQ 1))
            (CReal.ofQ'
              (HamiltonianAllSep.scaleQ k * HamiltonianAllSep.scaleQ k))) :=
        YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
          one.exponentialConverges previous.exponentialConverges
      have hSuccessor : CReal.ConvergesTo
          (fun stage => ExpNeg.expNeg
            (dyadicLogSquareExponent (k + 1) stage)
            (dyadicLogSquareExponent_nonnegative (k + 1) stage))
          (CReal.mul
            (CReal.ofQ'
              (HamiltonianAllSep.scaleQ 1 * HamiltonianAllSep.scaleQ 1))
            (CReal.ofQ'
              (HamiltonianAllSep.scaleQ k * HamiltonianAllSep.scaleQ k))) :=
        YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
          (fun stage =>
            dyadicLogSquareExponential_one_mul_equiv_succ k stage)
          hProduct
      exact CReal.convergesTo_limit_congr hSuccessor
        (CReal.Equiv.trans
          (CReal.Equiv.symm (CRealAlg.ofQ'_mul
            (HamiltonianAllSep.scaleQ 1 * HamiltonianAllSep.scaleQ 1)
            (HamiltonianAllSep.scaleQ k * HamiltonianAllSep.scaleQ k)))
          (TrigAdd.equiv_ofQ'_of_eqv
            (scaleQ_square_one_mul_square_eqv_succ k)))

end DyadicLogSquareEulerEvaluation

/-- At physical time one, the canonical exact Wilson exponent is the sum of
the dyadic and reduced-mantissa exponent streams. -/
theorem selectedWilsonExactPhysicalTimeExponent_one_approx_eqv_split
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (stage : Nat) :
    ((selectedWilsonExactPhysicalTimeExponent
      D positiveGapBound 1).approx stage).eqv
      (dyadicLogSquareExponent (gapBinExp
          D.reconstruction positiveGapBound).k stage +
        mantissaLogSquareExponent
          (gapMantissa D.reconstruction positiveGapBound)
          (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
          (gapMantissa_window D.reconstruction positiveGapBound) stage) := by
  unfold selectedWilsonExactPhysicalTimeExponent exactLogGap
    HamiltonianAllSep.hamiltonianGapRealAll dyadicLogSquareExponent
    mantissaLogSquareExponent
  let A : Q' := (HamiltonianAllSep.kLog2
    (gapBinExp D.reconstruction positiveGapBound).k).approx stage
  let B : Q' := (CReal.neg (CRealLog.logRat
    (gapMantissa D.reconstruction positiveGapBound)
    (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
    (gapMantissa_window D.reconstruction positiveGapBound))).approx stage
  let two : Q' := (1 : Q') + 1
  change (((A + B) * two) * Q'.ofNat 1).eqv
    ((A * two) + (B * two))
  have hOne : (Q'.ofNat 1).eqv (1 : Q') := by decide
  refine Q'.eqv_trans _ ((A + B) * two) _ ?_ ?_
  · refine Q'.eqv_trans _ (((A + B) * two) * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left ((A + B) * two)
        (Q'.ofNat 1) 1 hOne
    · exact Q'.mul_one_eqv ((A + B) * two)
  · refine Q'.eqv_trans _ (two * (A + B)) _
      (Q'.mul_comm_eqv (A + B) two) ?_
    refine Q'.eqv_trans _ (two * A + two * B) _
      (Q'.mul_add_eqv two A B) ?_
    exact ExpNeg.add_eqv_congr2
      (Q'.mul_comm_eqv two A) (Q'.mul_comm_eqv two B)

/-- Termwise exponential factorization of the canonical Wilson stream into
the two independent atomic inverse streams. -/
theorem selectedWilsonCanonicalExponential_equiv_atomicProduct
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (stage : Nat) :
    CReal.Equiv
      (CReal.mul
        (ExpNeg.expNeg
          (dyadicLogSquareExponent
            (gapBinExp D.reconstruction positiveGapBound).k stage)
          (dyadicLogSquareExponent_nonnegative
            (gapBinExp D.reconstruction positiveGapBound).k stage))
        (ExpNeg.expNeg
          (mantissaLogSquareExponent
            (gapMantissa D.reconstruction positiveGapBound)
            (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
            (gapMantissa_window D.reconstruction positiveGapBound) stage)
          (mantissaLogSquareExponent_nonnegative
            (gapMantissa D.reconstruction positiveGapBound)
            (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
            (gapMantissa_lt_one D.reconstruction positiveGapBound)
            (gapMantissa_window D.reconstruction positiveGapBound) stage)))
      (ExpNeg.expNeg
        ((selectedWilsonExactPhysicalTimeExponent
          D positiveGapBound 1).approx stage)
        (selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
          D positiveGapBound 1 stage)) := by
  let k := (gapBinExp D.reconstruction positiveGapBound).k
  let m := gapMantissa D.reconstruction positiveGapBound
  let hm1 := gapMantissaPlusOne_pos D.reconstruction positiveGapBound
  let hyb := gapMantissa_window D.reconstruction positiveGapBound
  let a := dyadicLogSquareExponent k stage
  let b := mantissaLogSquareExponent m hm1 hyb stage
  have ha : (0 : Q') <= a := dyadicLogSquareExponent_nonnegative k stage
  have hb : (0 : Q') <= b :=
    mantissaLogSquareExponent_nonnegative m hm1
      (gapMantissa_lt_one D.reconstruction positiveGapBound) hyb stage
  have hab : (a + b).eqv
      ((selectedWilsonExactPhysicalTimeExponent
        D positiveGapBound 1).approx stage) :=
    Q'.eqv_symm
      (selectedWilsonExactPhysicalTimeExponent_one_approx_eqv_split
        D positiveGapBound stage)
  exact CReal.Equiv.trans
    (expNeg_add_equiv a b ha hb)
    (expNeg_eqv_congr
      (Q'.zero_le_add a b ha hb)
      (selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
        D positiveGapBound 1 stage)
      hab)

/-- The family-independent analytic frontier for one Wilson reconstruction.
It evaluates the negative exponential on the canonical rational approximation
stream of twice the exact logarithmic gap.  Unlike the older dynamic record,
this datum mentions no cutoff family, rate variation, strength band, or Euler
schedule, so the analytic inverse proof can be developed independently of all
dynamic producer work. -/
structure WilsonCanonicalExactLogEulerEvaluation
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction) : Type 2 where
  canonicalExponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      ((selectedWilsonExactPhysicalTimeExponent
        D positiveGapBound 1).approx stage)
      (selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
        D positiveGapBound 1 stage))
    (CReal.ofQ'
      (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep))

namespace WilsonCanonicalExactLogEulerEvaluation

/-- Recombine the two independent atomic inverse evaluators into the static
canonical Wilson evaluator.  All remaining work in this compiler is algebraic:
the exponential addition law, multiplication continuity, and the exact
identity `scaleQ k * mantissa = separator`. -/
def ofAtomicEvaluations
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (dyadic : DyadicLogSquareEulerEvaluation
      (gapBinExp D.reconstruction positiveGapBound).k)
    (mantissa : MantissaLogSquareEulerEvaluation
      (gapMantissa D.reconstruction positiveGapBound)
      (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
      (gapMantissa_lt_one D.reconstruction positiveGapBound)
      (gapMantissa_window D.reconstruction positiveGapBound)) :
    WilsonCanonicalExactLogEulerEvaluation D positiveGapBound where
  canonicalExponentialConverges := by
    let k := (gapBinExp D.reconstruction positiveGapBound).k
    let m := gapMantissa D.reconstruction positiveGapBound
    let s := HamiltonianAllSep.scaleQ k
    have hProduct : CReal.ConvergesTo
        (fun stage => CReal.mul
          (ExpNeg.expNeg
            (dyadicLogSquareExponent k stage)
            (dyadicLogSquareExponent_nonnegative k stage))
          (ExpNeg.expNeg
            (mantissaLogSquareExponent m
              (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
              (gapMantissa_window D.reconstruction positiveGapBound) stage)
            (mantissaLogSquareExponent_nonnegative m
              (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
              (gapMantissa_lt_one D.reconstruction positiveGapBound)
              (gapMantissa_window D.reconstruction positiveGapBound) stage)))
        (CReal.mul (CReal.ofQ' (s * s)) (CReal.ofQ' (m * m))) :=
      YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        dyadic.exponentialConverges mantissa.exponentialConverges
    have hCanonical : CReal.ConvergesTo
        (fun stage => ExpNeg.expNeg
          ((selectedWilsonExactPhysicalTimeExponent
            D positiveGapBound 1).approx stage)
          (selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
            D positiveGapBound 1 stage))
        (CReal.mul (CReal.ofQ' (s * s)) (CReal.ofQ' (m * m))) :=
      YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
        (fun stage =>
          selectedWilsonCanonicalExponential_equiv_atomicProduct
            D positiveGapBound stage)
        hProduct
    have hScaleMantissa : (s * m).eqv
        D.selectedSpectralData.gap.sep :=
      HamiltonianAllSep.scaleQ_mul_mant_eqv
        D.selectedSpectralData.gap.sep k
    have hShuffle : ((s * s) * (m * m)).eqv ((s * m) * (s * m)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s s (m * m)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left s _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv s m m))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv s (s * m) m)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (s * (s * m)) ((s * m) * s) m
          (Q'.mul_comm_eqv s (s * m))) ?_
      exact Q'.mul_assoc_eqv (s * m) s m
    have hSquare : ((s * s) * (m * m)).eqv
        (D.selectedSpectralData.gap.sep *
          D.selectedSpectralData.gap.sep) := by
      refine Q'.eqv_trans _ _ _ hShuffle ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (s * m)
          D.selectedSpectralData.gap.sep (s * m) hScaleMantissa) ?_
      exact Q'.mul_eqv_congr_left D.selectedSpectralData.gap.sep
        (s * m) D.selectedSpectralData.gap.sep hScaleMantissa
    exact CReal.convergesTo_limit_congr hCanonical
      (CReal.Equiv.trans
        (CReal.Equiv.symm (CRealAlg.ofQ'_mul (s * s) (m * m)))
        (TrigAdd.equiv_ofQ'_of_eqv hSquare))

/-- The full dyadic input to `ofAtomicEvaluations` is generated by a single
evaluation at exponent one.  Consequently a Wilson reconstruction needs only
one universal log-two inverse seed, together with its reconstruction-specific
mantissa evaluator. -/
def ofDyadicOneAndMantissa
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (dyadicOne : DyadicLogSquareEulerEvaluation 1)
    (mantissa : MantissaLogSquareEulerEvaluation
      (gapMantissa D.reconstruction positiveGapBound)
      (gapMantissaPlusOne_pos D.reconstruction positiveGapBound)
      (gapMantissa_lt_one D.reconstruction positiveGapBound)
      (gapMantissa_window D.reconstruction positiveGapBound)) :
    WilsonCanonicalExactLogEulerEvaluation D positiveGapBound :=
  ofAtomicEvaluations D positiveGapBound
    (DyadicLogSquareEulerEvaluation.allOfOne dyadicOne
      (gapBinExp D.reconstruction positiveGapBound).k)
    mantissa

end WilsonCanonicalExactLogEulerEvaluation

/-- The minimal scalar analytic frontier: the upper Euler exponential built
from this exact-rate family converges at one physical-time unit to the square
of the separator selected by the same Wilson reconstruction.

The preceding theorem proves that the generating exponents converge to twice
the selected exact logarithmic gap.  Thus this field is the construction-
specific `exp (-2 * (-log sep)) = sep^2` evaluation, stated with an explicit
cutoff stream and convergence modulus rather than a free completed equality. -/
structure DynamicVacuumSectorWilsonExactLogEulerEvaluation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (_exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D) : Type 2 where
  upperEulerExponentialConverges : CReal.ConvergesTo
    (fun scale => scheduledSquaredRateUpperExponential family scale 1)
    (CReal.ofQ'
      (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep))

namespace DynamicVacuumSectorWilsonExactLogEulerEvaluation

/-- Compile the family-independent Wilson evaluation into the dynamic Euler
evaluation.  The proved rational-stream continuity theorem transports along
the fact that both exponent streams converge to the same exact Wilson
physical-time exponent. -/
def ofCanonicalWilsonEvaluation
    {family : DynamicVacuumSectorCompletedFamily 0}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D}
    (evaluation : WilsonCanonicalExactLogEulerEvaluation
      D exactRate.positiveGapBound) :
    DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family gapVariation D exactRate where
  upperEulerExponentialConverges := by
    change CReal.ConvergesTo
      (fun scale => ExpNeg.expNeg
        (scheduledSquaredRateUpperExponent family scale 1)
        (scheduledSquaredRateUpperExponent_nonnegative family scale 1))
      (CReal.ofQ'
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep))
    exact
      YMGap.Constructive.CRealExpRationalStreamContinuity.CReal.convergesTo_expNeg_of_common_rational_exponent_limit
        (fun scale =>
          scheduledSquaredRateUpperExponent_nonnegative family scale 1)
        (fun stage =>
          selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
            D exactRate.positiveGapBound 1 stage)
        (scheduledSquaredRateUpperExponent_converges_selectedWilsonExact
          family band gapVariation exactRate 1)
        (CReal.convergesTo_self
          (selectedWilsonExactPhysicalTimeExponent
            D exactRate.positiveGapBound 1))
        evaluation.canonicalExponentialConverges

/-- An upper-endpoint identification compiles the exact-log Euler evaluation
to convergence of the literal scheduled finite one-time rate stream. -/
def toPhysicalTimeRateConvergence
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family gapVariation D exactRate)
    (upperIdentification : CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential family scale 1)
      (ratePower.limitRepresentative 1)) :
    DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family ratePower D where
  scheduledRateConverges :=
    CReal.convergesTo_limit_congr
      (ratePower.converges 1)
      (CReal.Equiv_of_limit_of_equal
        (fun scale => CReal.Equiv.refl
          (scheduledSquaredRateUpperExponential family scale 1))
        upperIdentification evaluation.upperEulerExponentialConverges)

/-- The same compiler followed by same-stream uniqueness gives the scalar pin
consumed by the three-way all-vector graph-norm join. -/
def toPhysicalTimeRateLimitPin
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family gapVariation D exactRate)
    (upperIdentification : CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential family scale 1)
      (ratePower.limitRepresentative 1)) :
    DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin
      family ratePower D :=
  DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin.ofScheduledRateConvergence
    (evaluation.toPhysicalTimeRateConvergence upperIdentification)

end DynamicVacuumSectorWilsonExactLogEulerEvaluation

/-! ## 3. Specialize to the adaptive physical-exponential producer -/

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- For the adaptive producer, the existing physical-exponential endpoint
identification supplies every input around the single exact-log Euler
evaluation. -/
def wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family.toCompletedFamily gapVariation D exactRate) :
    DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  evaluation.toPhysicalTimeRateConvergence
    (physicalExponentialLimit_identification family
      band gapVariation positiveRatePower 1).1

/-- Rejoin the compiled scalar evaluation with the two independent all-vector
branches: a representative lift of the selected transfer and finite
graph-norm approximation through that lift. -/
def wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family.toCompletedFamily gapVariation D exactRate)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift D)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily D transfer) :
    DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelConvergenceCompilers
    (wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
      family band gapVariation positiveRatePower evaluation)
    transfer finite

/-- Adaptive scalar convergence directly from the family-independent
canonical Wilson evaluator. -/
def wilsonPhysicalTimeRateConvergenceOfCanonicalWilsonEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : WilsonCanonicalExactLogEulerEvaluation
      D exactRate.positiveGapBound) :
    DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
    family band gapVariation positiveRatePower
    (DynamicVacuumSectorWilsonExactLogEulerEvaluation.ofCanonicalWilsonEvaluation
      (family.physicalRateBand band) evaluation)

/-- Adaptive graph-norm compiler with the dynamic Euler-specific assumption
removed.  Only the static Wilson inverse evaluator remains on the scalar
branch; the transfer lift and finite graph approximation remain independent
parallel inputs. -/
def wilsonPhysicalTimeGraphNormLimitOfCanonicalWilsonEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : WilsonCanonicalExactLogEulerEvaluation
      D exactRate.positiveGapBound)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift D)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily D transfer) :
    DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelConvergenceCompilers
    (wilsonPhysicalTimeRateConvergenceOfCanonicalWilsonEvaluation
      family band gapVariation positiveRatePower evaluation)
    transfer finite

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.exactLogGap_approx_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.selectedWilsonExactPhysicalTimeExponent_approx_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.scheduledSquaredRateUpperExponent_converges_selectedWilsonExact
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.dyadicLogSquareExponent_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.logRat_approx_nonpositive_of_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.mantissaLogSquareExponent_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.dyadicLogSquareExponent_one_add_eqv_succ
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.dyadicLogSquareExponential_one_mul_equiv_succ
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.scaleQ_one_mul_scaleQ_eqv_succ
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.scaleQ_square_one_mul_square_eqv_succ
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DyadicLogSquareEulerEvaluation.zero
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DyadicLogSquareEulerEvaluation.allOfOne
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.selectedWilsonExactPhysicalTimeExponent_one_approx_eqv_split
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.selectedWilsonCanonicalExponential_equiv_atomicProduct
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.WilsonCanonicalExactLogEulerEvaluation.ofAtomicEvaluations
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.WilsonCanonicalExactLogEulerEvaluation.ofDyadicOneAndMantissa
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicVacuumSectorWilsonExactLogEulerEvaluation.ofCanonicalWilsonEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicVacuumSectorWilsonExactLogEulerEvaluation.toPhysicalTimeRateConvergence
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicVacuumSectorWilsonExactLogEulerEvaluation.toPhysicalTimeRateLimitPin
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeRateConvergenceOfCanonicalWilsonEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeGraphNormLimitOfCanonicalWilsonEvaluation
