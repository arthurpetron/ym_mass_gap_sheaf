/-
# Constructive-real limit of fixed-anchor physical SU(2) cutoff events

At the strong-coupling anchor `w = 1/400`, a fixed finite four-dimensional
box, and an arbitrary Boolean event of its physical face labels, the exact
normalized cutoff probabilities form a Bishop-Cauchy sequence.

`SU2PhysicalOuterCutoffAnchorTotalTolerance` supplies an executable retained
cutoff for every positive rational tolerance.  The modulus below requests
half the target tolerance.  Every later cutoff is half-tolerance close to the
retained cutoff, so a constructive triangle through that common retained
stage makes any two later probabilities target-tolerance close.

The resulting `CReal` has the exact cutoff probability as its `K`-th
approximation.  This module also proves convergence of the rationally lifted
sequence and uniqueness up to constructive `CReal.Equiv`.

This remains a fixed-anchor, fixed-finite-volume representation-cutoff limit.
It does not vary the coupling or spacing and does not take an infinite-volume
limit.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance
import YMGap.Continuum.SU2PhysicalOuterCutoffNormalizedEventTail
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNormalizedEventTail

/-! ## 1. Exact cutoff sequence and executable modulus -/

/-- The exact normalized finite-cutoff probability, lifted to a constant
constructive real at each cutoff. -/
def anchorPhysicalCutoffEventProbabilitySeq
    (volume : Nat) (event : EdgeLabelling → Bool) :
    Nat → CReal :=
  fun cutoff =>
    CReal.ofQ'
      (anchorPhysicalCutoffEventProbability
        cutoff volume event)

/-- Executable Cauchy modulus for every normalized event in one fixed box.
It is independent of the event and pays half of the requested tolerance;
the other half is spent comparing two arbitrary later cutoffs through the
common retained stage. -/
def anchorPhysicalCutoffEventProbabilityModulus
    (volume : Nat) (ε : Q') : Nat :=
  anchorPhysicalCutoffIncrementToleranceRetainedCutoff
    volume (HalfPow.half * ε)

private theorem twoSided_of_absQ_sub_le
    {a b ε : Q'} (h : absQ (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  have habs : Q'.abs (a + (-b)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
            (a + (-b)))))
      h
  constructor
  · exact YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le habs
  · apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a))
      habs

/-- Every cutoff past the explicit modulus is half-tolerance close to the
common retained cutoff selected by that modulus. -/
theorem anchorPhysicalCutoffEventProbability_from_modulus_abs_le_half
    (volume : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {cutoff : Nat}
    (hcutoff :
      anchorPhysicalCutoffEventProbabilityModulus
          volume ε ≤ cutoff) :
    absQ
        (anchorPhysicalCutoffEventProbability
            (anchorPhysicalCutoffEventProbabilityModulus
              volume ε)
            volume event +
          -anchorPhysicalCutoffEventProbability
            cutoff volume event) ≤
      HalfPow.half * ε := by
  have hhalf :
      (0 : Q') < HalfPow.half * ε :=
    ExpNeg.half_mul_pos ε hε
  exact Q'.le_trans' _ _ _
    (anchorPhysicalCutoffEventProbability_abs_le_increment
      hcutoff event)
    (anchorPhysicalCutoffIncrement_le_tolerance
      hhalf hcutoff)

private theorem add_two_halves_le
    (x ε : Q') :
    (x + HalfPow.half * ε) + HalfPow.half * ε ≤
      x + ε := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        x (HalfPow.half * ε) (HalfPow.half * ε))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      x
      (HalfPow.half * ε + HalfPow.half * ε)
      ε
      (ExpNeg.two_halves ε))

/-- Every two exact cutoff probabilities past the executable modulus are
two-sided `ε`-close.  This is the load-bearing Bishop-Cauchy estimate. -/
theorem anchorPhysicalCutoffEventProbability_twoSided_of_modulus
    (volume : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      anchorPhysicalCutoffEventProbabilityModulus
          volume ε ≤ first)
    (hsecond :
      anchorPhysicalCutoffEventProbabilityModulus
          volume ε ≤ second) :
    anchorPhysicalCutoffEventProbability
          first volume event ≤
        anchorPhysicalCutoffEventProbability
            second volume event + ε ∧
      anchorPhysicalCutoffEventProbability
          second volume event ≤
        anchorPhysicalCutoffEventProbability
            first volume event + ε := by
  let retained :=
    anchorPhysicalCutoffEventProbabilityModulus volume ε
  let halfTolerance := HalfPow.half * ε
  have hfirstHalf :=
    twoSided_of_absQ_sub_le
      (anchorPhysicalCutoffEventProbability_from_modulus_abs_le_half
        volume event hε hfirst)
  have hsecondHalf :=
    twoSided_of_absQ_sub_le
      (anchorPhysicalCutoffEventProbability_from_modulus_abs_le_half
        volume event hε hsecond)
  change
    anchorPhysicalCutoffEventProbability first volume event ≤
          anchorPhysicalCutoffEventProbability second volume event + ε ∧
      anchorPhysicalCutoffEventProbability second volume event ≤
          anchorPhysicalCutoffEventProbability first volume event + ε
  constructor
  · have hchain :
        anchorPhysicalCutoffEventProbability first volume event ≤
          (anchorPhysicalCutoffEventProbability second volume event +
              halfTolerance) +
            halfTolerance :=
      Q'.le_trans' _ _ _
        hfirstHalf.2
        (Q'.add_le_add_right _ _ halfTolerance hsecondHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (anchorPhysicalCutoffEventProbability second volume event)
        ε)
  · have hchain :
        anchorPhysicalCutoffEventProbability second volume event ≤
          (anchorPhysicalCutoffEventProbability first volume event +
              halfTolerance) +
            halfTolerance :=
      Q'.le_trans' _ _ _
        hsecondHalf.2
        (Q'.add_le_add_right _ _ halfTolerance hfirstHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (anchorPhysicalCutoffEventProbability first volume event)
        ε)

/-! ## 2. Bishop real, convergence, and uniqueness -/

/-- The fixed-anchor physical SU(2) event probability after removing the
Peter--Weyl cutoff in one fixed finite box. -/
def anchorPhysicalCutoffEventProbabilityLimit
    (volume : Nat) (event : EdgeLabelling → Bool) : CReal where
  approx cutoff :=
    anchorPhysicalCutoffEventProbability
      cutoff volume event
  cauchy := by
    intro ε hε
    refine
      ⟨anchorPhysicalCutoffEventProbabilityModulus volume ε,
        fun first second hfirst hsecond => ?_⟩
    exact anchorPhysicalCutoffEventProbability_twoSided_of_modulus
      volume event hε hfirst hsecond

@[simp] theorem anchorPhysicalCutoffEventProbabilityLimit_approx
    (volume cutoff : Nat) (event : EdgeLabelling → Bool) :
    (anchorPhysicalCutoffEventProbabilityLimit
      volume event).approx cutoff =
        anchorPhysicalCutoffEventProbability
          cutoff volume event :=
  rfl

/-- The exact rational finite-cutoff probabilities converge to the Bishop
real above, with the same executable modulus on both indices. -/
theorem anchorPhysicalCutoffEventProbabilitySeq_converges
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.ConvergesTo
      (anchorPhysicalCutoffEventProbabilitySeq volume event)
      (anchorPhysicalCutoffEventProbabilityLimit
        volume event) := by
  intro ε hε
  let retained :=
    anchorPhysicalCutoffEventProbabilityModulus volume ε
  refine
    ⟨retained, fun cutoff hcutoff =>
      ⟨retained, fun approximation happ => ?_⟩⟩
  change
    anchorPhysicalCutoffEventProbability cutoff volume event ≤
          anchorPhysicalCutoffEventProbability
              approximation volume event + ε ∧
      anchorPhysicalCutoffEventProbability
          approximation volume event ≤
        anchorPhysicalCutoffEventProbability
            cutoff volume event + ε
  exact anchorPhysicalCutoffEventProbability_twoSided_of_modulus
    volume event hε hcutoff happ

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- Constructive uniqueness: every Bishop real reached by the same exact
finite-cutoff sequence is equivalent to the canonical limit. -/
theorem anchorPhysicalCutoffEventProbabilityLimit_equiv_of_converges
    (volume : Nat) (event : EdgeLabelling → Bool)
    (limit : CReal)
    (hlimit :
      CReal.ConvergesTo
        (anchorPhysicalCutoffEventProbabilitySeq
          volume event)
        limit) :
    CReal.Equiv
      (anchorPhysicalCutoffEventProbabilityLimit
        volume event)
      limit := by
  exact CReal.Equiv_of_limit_of_equal
    (fun cutoff =>
      crealEquiv_refl
        (anchorPhysicalCutoffEventProbabilitySeq
          volume event cutoff))
    (anchorPhysicalCutoffEventProbabilitySeq_converges
      volume event)
    hlimit

#print axioms anchorPhysicalCutoffEventProbabilityModulus
#print axioms anchorPhysicalCutoffEventProbability_from_modulus_abs_le_half
#print axioms anchorPhysicalCutoffEventProbability_twoSided_of_modulus
#print axioms anchorPhysicalCutoffEventProbabilityLimit
#print axioms anchorPhysicalCutoffEventProbabilityLimit_approx
#print axioms anchorPhysicalCutoffEventProbabilitySeq_converges
#print axioms anchorPhysicalCutoffEventProbabilityLimit_equiv_of_converges

end YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealLimit
