/-
# The ordinary transfer logarithm on the EXISTING derivative domain

The finite positive-tail comparison passes first through the existing
regularized-log limit and then through the existing derivative graph.
Thus the literal unregularized partial sums converge to the SAME original
domain action.  Their computed rate is the output's already supplied
time-range defect modulus.  No inverse of T or preimage norm cap is used.
Conversely, a supplied ordinary-log limit on the SAME time sector constructs
the original domain equation. Both directions retain literal input/output
states; only the forward direction computes a replacement modulus.

This identifies the original fixed-carrier domain logarithm. It neither
asserts convergence on the ambient fringe kernel nor identifies this sector
with the canonical physical OS carrier. Scaling, physical time/mass and
the continuum Clay theorem remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogTailComparison
import YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial
import YMGap.Continuum.BF4WilsonAllNomeRootLogIdentification
import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder

namespace YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (completedDist_sub_le)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDefectContraction (defectPower_distance_contraction)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial (logPartial logTail logPartial_add_tail)
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
  (regularizedLog regularizedLog_approximation convergenceModulus
    logRows logRows_point regularizedLog_mk)
open YMGap.Continuum.BF4WilsonAllNomeLogTailComparison (logTail_norm_le_shifted_partial)
open YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeRootLogIdentification (derivativeAction_eq_regularizedLog)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (limit_unique completedDist_time)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedTime_additive completedTime_smul completedTime_zero_element)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (time_defectPower)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (quarter quarter_positive four_quarters defectModulus defect_small)
open YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder (norm_limit_order)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "F" => regularizedLog hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "U" => unregularizedLogPartial hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem add_sub_cancel (x y : V) :
    Sub (completedAdd hw0 hw1 x y) x = y := by
  unfold completedSub
  rw [completedAdd_comm hw0 hw1 x y, completedAdd_assoc,
    completedAdd_comm hw0 hw1 x, completedNeg_add, completedAdd_zero]

private theorem tail_difference (x : V) (m n : Nat) :
    logTail hw0 hw1 m n x = Sub (logPartial hw0 hw1 (m+n) x)
      (logPartial hw0 hw1 m x) := by
  rw [logPartial_add_tail, add_sub_cancel]

private theorem constant_close (x : V) (e : Q') (he : (0 : Q') < e) :
    RCle (dist x x) (rat e) := by
  rw [(completedDist_zero_iff hw0 hw1 x x).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

/-- Relative tail control after the ACTUAL regularized-log limit, on every
original core source. This is not a whole-carrier ordinary log map. -/
theorem regularizedLog_tail_norm_bound (x : V) (m : Nat) :
    RCle (B (Sub (F x) (logPartial hw0 hw1 m x))
        (Sub (F x) (logPartial hw0 hw1 m x)))
      (B (DP m (F x)) (DP m (F x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  let xs := fun n => logTail hw0 hw1 m n (Class X)
  let ys := fun n => DP m (logPartial hw0 hw1 n (Class X))
  apply norm_limit_order hw0 hw1 xs ys _ _
    (fun e => convergenceModulus hw0 hw1 X (quarter e))
    (convergenceModulus hw0 hw1 X)
  · intro e he n hn
    have hd := quarter_positive he
    have hfirst := regularizedLog_approximation hw0 hw1 X (quarter e) hd (m+n)
      (by omega)
    have hsecond := constant_close hw0 hw1 (logPartial hw0 hw1 m (Class X))
      (quarter e) hd
    dsimp only [xs]
    rw [tail_difference]
    have h := RCle_trans (completedDist_sub_le hw0 hw1 _ _ _ _)
      (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
    rwa [four_quarters] at h
  · intro e he n hn
    exact RCle_trans (defectPower_distance_contraction hw0 hw1 m _ _)
      (regularizedLog_approximation hw0 hw1 X e he n hn)
  · intro n
    exact logTail_norm_le_shifted_partial hw0 hw1 (Class X) m n

private def partialTolerance (m : Nat) (e : Q') : Q' :=
  linearTolerance (Q'.ofNat m*Q'.ofNat m)
    (SumOfSquares.q_mul_self_nonneg (Q'.ofNat m)) e

private theorem partialTolerance_positive (m : Nat) {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < partialTolerance m e :=
  linearTolerance_pos _ _ he

private theorem partial_close (m : Nat) (x y : V) (e : Q') (he : (0 : Q') < e)
    (h : RCle (dist x y) (rat (partialTolerance m e))) :
    RCle (dist (U m x) (U m y)) (rat e) := by
  let c := Q'.ofNat m*Q'.ofNat m
  have hc : (0 : Q') ≤ c := SumOfSquares.q_mul_self_nonneg (Q'.ofNat m)
  have hs := RCle_trans (unregularizedLogPartial_distance_bound hw0 hw1 m x y)
    (RCscale_mono hc h)
  have hpin : RCscale c (rat (partialTolerance m e)) = rat (c*partialTolerance m e) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hpin] at hs
  exact RCle_trans hs (leEv_le_ofQ'_of_approx_le (fun _ =>
    linearTolerance_budget c hc he))

/-- The original represented derivative graph controls its literal ordinary
logarithm error by the original defect tail of its OWN output. -/
theorem graph_logarithm_tail_bound {input output : V}
    (G : GraphLimit hw0 hw1 input output) (m : Nat) :
    RCle (dist (U m input) output) (B (DP m output) (DP m output)) := by
  let xs := fun n => Sub (A (G.source n)) (U m (T 1 (G.source n)))
  let ys := fun n => DP m (A (G.source n))
  have h := norm_limit_order hw0 hw1 xs ys (Sub output (U m input)) (DP m output)
    (fun e => max (G.modulus (quarter e))
      (G.modulus (partialTolerance m (quarter e)))) G.modulus
    (by
      intro e he n hn
      have hd := quarter_positive he
      have hout := (G.bound (quarter e) hd n (Nat.le_trans (Nat.le_max_left _ _) hn)).2
      have hin := (G.bound (partialTolerance m (quarter e))
        (partialTolerance_positive m hd) n (Nat.le_trans (Nat.le_max_right _ _) hn)).1
      have hp := partial_close hw0 hw1 m _ _ (quarter e) hd hin
      have hs := RCle_trans (completedDist_sub_le hw0 hw1 _ _ _ _)
        (RCadd_le_add (RCadd_le_add hout hout) (RCadd_le_add hp hp))
      rwa [four_quarters] at hs)
    (by
      intro e he n hn
      exact RCle_trans (defectPower_distance_contraction hw0 hw1 m _ _)
        (G.bound e he n hn).2)
    (by
      intro n
      dsimp only [xs, ys]
      rw [unregularizedLogPartial_time, derivativeAction_eq_regularizedLog]
      exact regularizedLog_tail_norm_bound hw0 hw1 (G.source n) m)
  rw [completedDist_symm hw0 hw1 (U m input) output]
  exact h

/-- Rate data come from this domain point's EXISTING output range witness,
not from selection of a transfer preimage or a new analytic assumption. -/
def domainLogModulus (p : DomainPoint hw0 hw1 (width := width)) (e : Q') : Nat :=
  defectModulus hw0 hw1 p.output.range e

/-- The ordinary logarithm series converges to the SAME original domain
action, with its explicit all-tail squared-distance modulus. -/
theorem domainLogarithm_bound (p : DomainPoint hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (m : Nat)
    (hm : domainLogModulus hw0 hw1 p e ≤ m) :
    RCle (dist (U m p.input.val) p.output.val) (rat e) :=
  RCle_trans (graph_logarithm_tail_bound hw0 hw1 (graph hw0 hw1 p) m)
    (defect_small hw0 hw1 p.output.range e he m hm)

/-- The already constructed action and its ordinary-log modulus as data. -/
def domainLogarithmCertificate (p : DomainPoint hw0 hw1 (width := width)) :
    Σ' y : V, Σ' modulus : Q' → Nat, (y = p.output.val) ×'
      (∀ e : Q', (0 : Q') < e → ∀ m, modulus e ≤ m →
        RCle (dist (U m p.input.val) y) (rat e)) :=
  ⟨p.output.val, domainLogModulus hw0 hw1 p, rfl, domainLogarithm_bound hw0 hw1 p⟩

/-- Each literal finite logarithm commutes with the ORIGINAL temporal map.
No limiting operator or transfer inverse is invoked. -/
theorem time_unregularizedLogPartial (time n : Nat) (x : V) :
    T time (U n x) = U n (T time x) := by
  induction n with
  | zero => exact completedTime_zero_element hw0 hw1 time
  | succ n ih =>
      change T time (completedAdd hw0 hw1 (U n x)
        (completedSmul hw0 hw1 (Q'.invSucc n) (DP (n+1) x))) =
        completedAdd hw0 hw1 (U n (T time x))
          (completedSmul hw0 hw1 (Q'.invSucc n) (DP (n+1) (T time x)))
      rw [completedTime_additive, completedTime_smul, time_defectPower, ih]

/-- The ordinary logarithm domain as witnessing data on the EXISTING sector.
The modulus is supplied, not inferred from mere convergence in Prop. -/
structure LogLimitPoint where
  input : State hw0 hw1 (width := width)
  output : State hw0 hw1 (width := width)
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
    RCle (dist (U n input.val) output.val) (rat e)

/-- A supplied ordinary-log limit entails the ORIGINAL domain equation,
because temporal contraction preserves its modulus and the regularized
finite logarithm already has its actual, uniquely determined limit. -/
theorem logLimit_equation (p : LogLimitPoint hw0 hw1 (width := width)) :
    A p.input.val = T 1 p.output.val := by
  let X := representative hw0 hw1 p.input.range
  have hpin : Class X = p.input.val := representative_pin hw0 hw1 p.input.range
  rw [derivativeAction_eq_regularizedLog, ← hpin, regularizedLog_mk]
  apply limit_unique hw0 hw1 (logRows hw0 hw1 X) _ p.modulus
  intro e he n hn
  rw [logRows_point, hpin, ← unregularizedLogPartial_time,
    ← time_unregularizedLogPartial]
  exact RCle_trans (completedDist_time hw0 hw1 1 _ _) (p.bound e he n hn)

/-- Backward construction from the literal ordinary-log domain to the
original derivative domain, preserving both supplied sector states. -/
def domainPointOfLogLimit (p : LogLimitPoint hw0 hw1 (width := width)) :
    DomainPoint hw0 hw1 (width := width) :=
  ⟨p.input, p.output, logLimit_equation hw0 hw1 p⟩

/-- Forward construction computes an ordinary-log modulus from the actual
output range witness. It does not impose a new convergence assumption. -/
def logLimitPointOfDomain (p : DomainPoint hw0 hw1 (width := width)) :
    LogLimitPoint hw0 hw1 (width := width) :=
  ⟨p.input, p.output, domainLogModulus hw0 hw1 p, domainLogarithm_bound hw0 hw1 p⟩

/-- The forward/backward domain join returns the SAME original domain point.
The reverse join can change the modulus, so no equality of rate witnesses
is asserted. -/
theorem domain_of_log_of_domain (p : DomainPoint hw0 hw1 (width := width)) :
    domainPointOfLogLimit hw0 hw1 (logLimitPointOfDomain hw0 hw1 p) = p := rfl

#print axioms regularizedLog_tail_norm_bound
#print axioms graph_logarithm_tail_bound
#print axioms domainLogModulus
#print axioms domainLogarithm_bound
#print axioms domainLogarithmCertificate
#print axioms time_unregularizedLogPartial
#print axioms logLimit_equation
#print axioms domainPointOfLogLimit
#print axioms logLimitPointOfDomain
#print axioms domain_of_log_of_domain

end YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm
