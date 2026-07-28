/-
# Constructive-real limit of canonical BF4 U(1) cutoff events

At fixed rational nome `0 < w < 1`, fixed finite slab half-width, and fixed
Boolean charge event, the normalized canonical U(1) event probabilities form
an explicitly Cauchy rational sequence as the symmetric charge cutoff grows.
`BF4U1OuterCutoffNormalizedEventTail` supplies the quantitative modulus,
uniformly in every later cutoff.

This module turns that modulus into an actual Bishop-style `CReal`.  Its
`K`-th approximation is the exact rational probability at cutoff `K`.  The
same Type-level cutoff function proves:

* the `CReal.cauchy` field;
* convergence of the lifted rational cutoff sequence to that `CReal`; and
* uniqueness of the limit up to the repository's constructive `CReal.Equiv`.

The construction is fixed-nome, fixed-geometry, and finite-volume.  It does
not vary the nome toward one, take a spacing or volume limit, transport the
event across changing geometries, or address nonabelian gauge groups.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4U1OuterCutoffCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact cutoff sequence and its Type-level modulus -/

/-- The normalized finite-cutoff event probability, lifted from exact
rationals to a constant constructive real at each cutoff. -/
def canonicalU1SlabEventProbabilitySeq
    (w : Q') (hw0 : (0 : Q') < w)
    (half : Nat) (event : ChargeLabelling → Bool) :
    Nat → CReal :=
  fun K =>
    CReal.ofQ'
      (canonicalU1SlabEventProbability
        w (Q'.le_of_lt hw0) half K event)

/-- Type-level cutoff candidate for every normalized Boolean event on the
fixed canonical slab.  The theorem below certifies it as a Cauchy modulus
under `0 < w < 1` and `0 < ε`.  It is independent of the event and of the
later outer cutoff. -/
def canonicalU1SlabEventProbabilityModulus
    (w ε : Q') (half : Nat) : Nat :=
  signedChargeTensorTailCutoff w ε
    (slabPhysicalFaceEdges (centralExtent half)).length

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

/-- Every two cutoff probabilities past the explicit Type-level modulus are
two-sided `ε`-close.  Unlike the `CReal.cauchy` wrapper, the modulus itself is
available as executable data through
`canonicalU1SlabEventProbabilityModulus`. -/
theorem canonicalU1SlabEventProbability_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat}
    (hK :
      canonicalU1SlabEventProbabilityModulus w ε half ≤ K)
    (hL :
      canonicalU1SlabEventProbabilityModulus w ε half ≤ L) :
    canonicalU1SlabEventProbability
          w (Q'.le_of_lt hw0) half K event ≤
        canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half L event + ε ∧
      canonicalU1SlabEventProbability
          w (Q'.le_of_lt hw0) half L event ≤
        canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half K event + ε := by
  rcases Nat.le_total K L with hKL | hLK
  · exact twoSided_of_absQ_sub_le
      (canonicalU1SlabEventProbability_outerCutoff_abs_le_of_cutoff
        hw0 hw1 hε half hKL hK event)
  · have h :=
      twoSided_of_absQ_sub_le
        (canonicalU1SlabEventProbability_outerCutoff_abs_le_of_cutoff
          hw0 hw1 hε half hLK hL event)
    exact ⟨h.2, h.1⟩

/-! ## 2. The Bishop real and convergence -/

/-- The constructive-real normalized event probability obtained by removing
the outer signed-charge cutoff at fixed nome and fixed finite geometry. -/
def canonicalU1SlabEventProbabilityLimit
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) : CReal where
  approx K :=
    canonicalU1SlabEventProbability
      w (Q'.le_of_lt hw0) half K event
  cauchy := by
    intro ε hε
    refine
      ⟨canonicalU1SlabEventProbabilityModulus w ε half,
        fun K L hK hL => ?_⟩
    exact canonicalU1SlabEventProbability_twoSided_of_modulus
      hw0 hw1 half event hε hK hL

@[simp] theorem canonicalU1SlabEventProbabilityLimit_approx
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half K : Nat) (event : ChargeLabelling → Bool) :
    (canonicalU1SlabEventProbabilityLimit
      w hw0 hw1 half event).approx K =
        canonicalU1SlabEventProbability
          w (Q'.le_of_lt hw0) half K event := rfl

/-- The exact finite-cutoff probabilities converge to the constructed Bishop
real.  At tolerance `ε`, both the sequence-stage and approximation-stage are
the explicit tensor-tail cutoff. -/
theorem canonicalU1SlabEventProbabilitySeq_converges
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) :
    CReal.ConvergesTo
      (canonicalU1SlabEventProbabilitySeq w hw0 half event)
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half event) := by
  intro ε hε
  let M :=
    canonicalU1SlabEventProbabilityModulus w ε half
  refine ⟨M, fun K hK => ⟨M, fun n hn => ?_⟩⟩
  change
    canonicalU1SlabEventProbability
          w (Q'.le_of_lt hw0) half K event ≤
        canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half n event + ε ∧
      canonicalU1SlabEventProbability
          w (Q'.le_of_lt hw0) half n event ≤
        canonicalU1SlabEventProbability
            w (Q'.le_of_lt hw0) half K event + ε
  exact canonicalU1SlabEventProbability_twoSided_of_modulus
    hw0 hw1 half event hε hK hn

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- Constructive uniqueness: any `CReal` that is a limit of the same exact
finite-cutoff probability sequence is equivalent to the canonical diagonal
limit. -/
theorem canonicalU1SlabEventProbabilityLimit_equiv_of_converges
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool)
    (L : CReal)
    (hL :
      CReal.ConvergesTo
        (canonicalU1SlabEventProbabilitySeq
          w hw0 half event) L) :
    CReal.Equiv
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half event) L := by
  exact CReal.Equiv_of_limit_of_equal
    (fun K =>
      crealEquiv_refl
        (canonicalU1SlabEventProbabilitySeq
          w hw0 half event K))
    (canonicalU1SlabEventProbabilitySeq_converges
      w hw0 hw1 half event)
    hL

#print axioms canonicalU1SlabEventProbabilityModulus
#print axioms canonicalU1SlabEventProbability_twoSided_of_modulus
#print axioms canonicalU1SlabEventProbabilityLimit
#print axioms canonicalU1SlabEventProbabilityLimit_approx
#print axioms canonicalU1SlabEventProbabilitySeq_converges
#print axioms canonicalU1SlabEventProbabilityLimit_equiv_of_converges

end YMGap.Continuum.BF4U1OuterCutoffCRealLimit
