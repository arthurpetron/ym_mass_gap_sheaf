/-
# The original witnessed range is exactly the dyadic zero-continuity sector

A range witness constructs all-small-dyadic-time continuity, using the
existing continuity theorem on its computed original time-image rows.
Conversely, convergence R_k x -> x of just the original root images,
with an explicit modulus and original input representative, constructs a
range witness: every R_k x already has one and the sector is closed.
This upgrades that root-sequence continuity to all small dyadic increments.

Both directions retain their witnesses and computed moduli. The original
ambient kernel is not removed. This identifies a mathematical continuity
sector, not its physical OS interpretation, a full Hilbert/adjoint package,
or physical-time/scaling control.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
import YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
import YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeTimeContinuitySector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (rangeRows rangeRows_point rangeRows_limit ofLimit)
open YMGap.Continuum.BF4WilsonAllNomeRootTimeRange (rootRange)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
  (closureModulus closure_smallTime)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "R" => root hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def continuityModulus {x : V} (witness : RangeLimit hw0 hw1 x) (e : Q') : Nat :=
  closureModulus hw0 hw1 (rangeRows hw0 hw1 witness) witness.preimage e

/-- Every sufficiently small original dyadic increment, including zero. -/
theorem smallTime {x : V} (witness : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) (depth steps : Nat)
    (hsmall : steps*2^(continuityModulus hw0 hw1 witness e) ≤ 2^depth) :
    RCle (dist (S depth steps x) x) (rat e) := by
  have h := closure_smallTime hw0 hw1 (rangeRows hw0 hw1 witness) witness.preimage
    (rangeRows_point hw0 hw1 witness) e he depth steps hsmall
  rwa [rangeRows_limit] at h

/-- In particular the same modulus controls the root sequence. -/
theorem root_small {x : V} (witness : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) (k : Nat)
    (hk : continuityModulus hw0 hw1 witness e ≤ k) :
    RCle (dist (R k x) x) (rat e) := by
  have hsmall : 1*2^(continuityModulus hw0 hw1 witness e) ≤ 2^k := by
    rw [Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide) hk
  exact smallTime hw0 hw1 witness e he k 1 hsmall

/-- Root continuity alone suffices to construct range membership; no
derivative, quotient limit, or candidate derivative output is assumed. -/
def rangeOfRootLimit (X : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ k, modulus e ≤ k →
      RCle (dist (R k (Class X)) (Class X)) (rat e)) :
    RangeLimit hw0 hw1 (Class X) :=
  ofLimit hw0 hw1 (fun k => rootRange hw0 hw1 k X) (Class X) modulus bound

def rangeOfDyadicContinuity (X : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ depth steps,
      steps*2^(modulus e) ≤ 2^depth →
        RCle (dist (S depth steps (Class X)) (Class X)) (rat e)) :
    RangeLimit hw0 hw1 (Class X) :=
  rangeOfRootLimit hw0 hw1 X modulus (by
    intro e he k hk
    exact bound e he k 1 (by
      rw [Nat.one_mul]
      exact Nat.pow_le_pow_right (by decide) hk))

/-- Explicit upgrade from root-sequence continuity to ALL small dyadic
increments on the SAME original state. -/
def continuityOfRootLimit (X : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ k, modulus e ≤ k →
      RCle (dist (R k (Class X)) (Class X)) (rat e)) :
    Σ' m : Q' → Nat, ∀ e : Q', (0 : Q') < e → ∀ depth steps,
      steps*2^(m e) ≤ 2^depth →
        RCle (dist (S depth steps (Class X)) (Class X)) (rat e) :=
  ⟨continuityModulus hw0 hw1 (rangeOfRootLimit hw0 hw1 X modulus bound),
    smallTime hw0 hw1 (rangeOfRootLimit hw0 hw1 X modulus bound)⟩

#print axioms continuityModulus
#print axioms smallTime
#print axioms root_small
#print axioms rangeOfRootLimit
#print axioms rangeOfDyadicContinuity
#print axioms continuityOfRootLimit

end YMGap.Continuum.BF4WilsonAllNomeTimeContinuitySector
