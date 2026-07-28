/-
# Arbitrary-fixed-nome Bishop limit of physical SU(2) cutoff events

For every rational `0 < w < 1`, fixed finite four-dimensional volume, and
Boolean predicate of the physical face labels, the exact normalized
Peter--Weyl cutoff probabilities form a Bishop-Cauchy sequence.

The executable modulus asks the arbitrary-nome physical tail schedule for
half the requested tolerance.  Two later cutoffs are compared through that
common retained stage.  The resulting constructive real is unique up to
`CReal.Equiv`, lies in the constructive unit interval, and preserves exact
Boolean-complement normalization.

The construction is pointwise in `w` and fixed finite volume.  Its modulus
may diverge as `w` approaches one; this module asserts no spacing-uniform,
continuum, or infinite-volume limit.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.SU2PhysicalOuterCutoffNomeCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact cutoff sequence and half-tolerance modulus -/

def physicalNomeCutoffEventProbabilitySeq
    {w : Q'} (hw0 : (0 : Q') < w)
    (volume : Nat) (event : EdgeLabelling → Bool) :
    Nat → CReal :=
  fun cutoff =>
    CReal.ofQ'
      (physicalNomeCutoffEventProbability
        w (Q'.le_of_lt hw0)
        cutoff volume event)

/-- Event-independent executable modulus at fixed nome and volume. -/
def physicalNomeCutoffEventProbabilityModulus
    (w : Q') (volume : Nat) (ε : Q') : Nat :=
  physicalNomeTensorToleranceRetainedCutoff
    w (plaquetteEdgeCount volume)
    (HalfPow.half * ε)

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
  · exact
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
        habs
  · apply
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          b a))
      habs

/-- Every cutoff past the modulus is half-tolerance close to the common
retained cutoff selected by that modulus. -/
theorem physicalNomeCutoffEventProbability_from_modulus_abs_le_half
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {cutoff : Nat}
    (hcutoff :
      physicalNomeCutoffEventProbabilityModulus
          w volume ε ≤ cutoff) :
    absQ
        (physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            (physicalNomeCutoffEventProbabilityModulus
              w volume ε)
            volume event +
          -physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            cutoff volume event) ≤
      HalfPow.half * ε := by
  have hhalf :
      (0 : Q') < HalfPow.half * ε :=
    ExpNeg.half_mul_pos ε hε
  exact physicalNomeCutoffEventProbability_abs_le_tolerance
    hw0 hw1 volume hhalf hcutoff event

private theorem add_two_halves_le
    (x ε : Q') :
    (x + HalfPow.half * ε) +
        HalfPow.half * ε ≤
      x + ε := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        x (HalfPow.half * ε)
        (HalfPow.half * ε))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      x
      (HalfPow.half * ε + HalfPow.half * ε)
      ε
      (ExpNeg.two_halves ε))

/-- Load-bearing Bishop-Cauchy estimate for two arbitrary later cutoffs. -/
theorem physicalNomeCutoffEventProbability_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      physicalNomeCutoffEventProbabilityModulus
          w volume ε ≤ first)
    (hsecond :
      physicalNomeCutoffEventProbabilityModulus
          w volume ε ≤ second) :
    physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          first volume event ≤
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            second volume event + ε ∧
      physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          second volume event ≤
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            first volume event + ε := by
  let halfTolerance := HalfPow.half * ε
  have hfirstHalf :=
    twoSided_of_absQ_sub_le
      (physicalNomeCutoffEventProbability_from_modulus_abs_le_half
        hw0 hw1 volume event hε hfirst)
  have hsecondHalf :=
    twoSided_of_absQ_sub_le
      (physicalNomeCutoffEventProbability_from_modulus_abs_le_half
        hw0 hw1 volume event hε hsecond)
  constructor
  · have hchain :
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            first volume event ≤
          (physicalNomeCutoffEventProbability
              w (Q'.le_of_lt hw0)
              second volume event +
            halfTolerance) +
          halfTolerance :=
      Q'.le_trans' _ _ _
        hfirstHalf.2
        (Q'.add_le_add_right _ _
          halfTolerance hsecondHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          second volume event)
        ε)
  · have hchain :
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            second volume event ≤
          (physicalNomeCutoffEventProbability
              w (Q'.le_of_lt hw0)
              first volume event +
            halfTolerance) +
          halfTolerance :=
      Q'.le_trans' _ _ _
        hsecondHalf.2
        (Q'.add_le_add_right _ _
          halfTolerance hfirstHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          first volume event)
        ε)

/-! ## 2. Bishop real, convergence, and uniqueness -/

def physicalNomeCutoffEventProbabilityLimit
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) : CReal where
  approx cutoff :=
    physicalNomeCutoffEventProbability
      w (Q'.le_of_lt hw0)
      cutoff volume event
  cauchy := by
    intro ε hε
    refine
      ⟨physicalNomeCutoffEventProbabilityModulus
          w volume ε,
        fun first second hfirst hsecond => ?_⟩
    exact
      physicalNomeCutoffEventProbability_twoSided_of_modulus
        hw0 hw1 volume event hε hfirst hsecond

@[simp] theorem physicalNomeCutoffEventProbabilityLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume cutoff : Nat)
    (event : EdgeLabelling → Bool) :
    (physicalNomeCutoffEventProbabilityLimit
      hw0 hw1 volume event).approx cutoff =
        physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          cutoff volume event :=
  rfl

theorem physicalNomeCutoffEventProbabilitySeq_converges
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.ConvergesTo
      (physicalNomeCutoffEventProbabilitySeq
        hw0 volume event)
      (physicalNomeCutoffEventProbabilityLimit
        hw0 hw1 volume event) := by
  intro ε hε
  let retained :=
    physicalNomeCutoffEventProbabilityModulus
      w volume ε
  refine
    ⟨retained, fun cutoff hcutoff =>
      ⟨retained, fun approximation happ => ?_⟩⟩
  change
    physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          cutoff volume event ≤
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            approximation volume event + ε ∧
      physicalNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          approximation volume event ≤
        physicalNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            cutoff volume event + ε
  exact
    physicalNomeCutoffEventProbability_twoSided_of_modulus
      hw0 hw1 volume event hε hcutoff happ

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε
          (Q'.le_of_lt hε)⟩⟩

theorem physicalNomeCutoffEventProbabilityLimit_equiv_of_converges
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool)
    (limit : CReal)
    (hlimit :
      CReal.ConvergesTo
        (physicalNomeCutoffEventProbabilitySeq
          hw0 volume event)
        limit) :
    CReal.Equiv
      (physicalNomeCutoffEventProbabilityLimit
        hw0 hw1 volume event)
      limit := by
  exact CReal.Equiv_of_limit_of_equal
    (fun cutoff =>
      crealEquiv_refl
        (physicalNomeCutoffEventProbabilitySeq
          hw0 volume event cutoff))
    (physicalNomeCutoffEventProbabilitySeq_converges
      hw0 hw1 volume event)
    hlimit

/-! ## 3. Unit interval at finite cutoff and in the limit -/

theorem physicalNomeCutoffEventProbability_nonnegative
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      physicalNomeCutoffEventProbability
        w hw0 cutoff volume event := by
  unfold physicalNomeCutoffEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEventNumerator_nonnegative
      hw0 cutoff volume event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingKPhysicalPartition_pos
          hw0 cutoff volume)))

theorem physicalNomeCutoffEventProbability_le_one
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    physicalNomeCutoffEventProbability
        w hw0 cutoff volume event ≤
      (1 : Q') := by
  unfold physicalNomeCutoffEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKEventNumerator_le_partition
      hw0 cutoff volume event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKPhysicalPartition
          w cutoff volume)))

theorem physicalNomeCutoffEventProbabilityLimit_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
      (physicalNomeCutoffEventProbabilityLimit
        hw0 hw1 volume event) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro cutoff
  exact physicalNomeCutoffEventProbability_nonnegative
    w (Q'.le_of_lt hw0) cutoff volume event

theorem physicalNomeCutoffEventProbabilityLimit_le_one
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv
      (physicalNomeCutoffEventProbabilityLimit
        hw0 hw1 volume event)
      CReal.cone := by
  apply CReal.leEv_le_ofQ'_of_approx_le
  intro cutoff
  exact physicalNomeCutoffEventProbability_le_one
    w (Q'.le_of_lt hw0) cutoff volume event

theorem physicalNomeCutoffEventProbabilityLimit_mem_unitInterval
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
        (physicalNomeCutoffEventProbabilityLimit
          hw0 hw1 volume event) ∧
      CReal.leEv
        (physicalNomeCutoffEventProbabilityLimit
          hw0 hw1 volume event)
        CReal.cone :=
  ⟨physicalNomeCutoffEventProbabilityLimit_nonnegative
      hw0 hw1 volume event,
    physicalNomeCutoffEventProbabilityLimit_le_one
      hw0 hw1 volume event⟩

/-! ## 4. Exact Boolean-complement normalization -/

private theorem listQSum_mask_eq_filter_local
    {A : Type} (weight : A → Q')
    (event : A → Bool) :
    ∀ source : List A,
      listQSum
          (fun item =>
            if event item then weight item else 0)
          source ≈
        listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head
      · simp only [listQSum, hevent,
          Bool.false_eq_true, ↓reduceIte,
          List.filter_cons]
        exact Q'.eqv_trans _
          (0 + listQSum weight
            (tail.filter event)) _
          (Q'.add_eqv_congr_left 0 _
            (listQSum weight (tail.filter event))
            (listQSum_mask_eq_filter_local
              weight event tail))
          (QPoly.q_zero_add_eqv
            (listQSum weight
              (tail.filter event)))
      · simp only [listQSum, hevent,
          ↓reduceIte, List.filter_cons]
        exact Q'.add_eqv_congr_left
          (weight head)
          (listQSum
            (fun item =>
              if event item
                then weight item else 0)
            tail)
          (listQSum weight (tail.filter event))
          (listQSum_mask_eq_filter_local
            weight event tail)

theorem physicalNomeCutoffEventNumerator_add_complement_eqv_partition
    (w : Q') (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator w
          cutoff volume event +
        parametricKEventNumerator w
          cutoff volume
          (fun state => !(event state)) ≈
      parametricKPhysicalPartition
        w cutoff volume := by
  unfold parametricKEventNumerator
    parametricKEventTerm
    parametricKPhysicalPartition
  let states :=
    boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount volume))
  let weight :=
    parametricKPhysicalTerm w cutoff volume
  have hevent :=
    listQSum_mask_eq_filter_local
      weight event states
  have hcomplement :=
    listQSum_mask_eq_filter_local
      weight (fun state => !(event state)) states
  have hpartition :=
    listQSum_filter_partition
      weight event states
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hevent hcomplement)
    (Q'.eqv_symm hpartition)

private theorem add_divPos_eqv_local
    (p q d : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd + Q'.divPos q d hd ≈
      Q'.divPos (p + q) d hd :=
  Q'.eqv_symm
    (Q'.add_mul_eqv
      p q (Q'.recipPos d hd))

theorem physicalNomeCutoffEventProbability_add_complement_eqv_one
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    physicalNomeCutoffEventProbability
          w hw0 cutoff volume event +
        physicalNomeCutoffEventProbability
          w hw0 cutoff volume
          (fun state => !(event state)) ≈
      (1 : Q') := by
  have hsplit :=
    physicalNomeCutoffEventNumerator_add_complement_eqv_partition
      w cutoff volume event
  unfold physicalNomeCutoffEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (parametricKEventNumerator
        w cutoff volume event)
      (parametricKEventNumerator
        w cutoff volume
        (fun state => !(event state)))
      (parametricKPhysicalPartition
        w cutoff volume)
      (couplingKPhysicalPartition_pos
        hw0 cutoff volume)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (parametricKPhysicalPartition
          w cutoff volume)
        (couplingKPhysicalPartition_pos
          hw0 cutoff volume))
      hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (parametricKPhysicalPartition
      w cutoff volume)
    (couplingKPhysicalPartition_pos
      hw0 cutoff volume)

theorem
    physicalNomeCutoffEventProbabilityLimit_add_complement_equiv_one
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (volume : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.Equiv
      (CReal.add
        (physicalNomeCutoffEventProbabilityLimit
          hw0 hw1 volume event)
        (physicalNomeCutoffEventProbabilityLimit
          hw0 hw1 volume
          (fun state => !(event state))))
      CReal.cone := by
  apply Equiv_of_approx_eqv
  intro cutoff
  exact
    physicalNomeCutoffEventProbability_add_complement_eqv_one
      w (Q'.le_of_lt hw0)
      cutoff volume event

/-! ## Axiom audit -/

#print axioms physicalNomeCutoffEventProbabilityModulus
#print axioms physicalNomeCutoffEventProbability_from_modulus_abs_le_half
#print axioms physicalNomeCutoffEventProbability_twoSided_of_modulus
#print axioms physicalNomeCutoffEventProbabilityLimit
#print axioms physicalNomeCutoffEventProbabilitySeq_converges
#print axioms
  physicalNomeCutoffEventProbabilityLimit_equiv_of_converges
#print axioms
  physicalNomeCutoffEventProbabilityLimit_mem_unitInterval
#print axioms
  physicalNomeCutoffEventProbabilityLimit_add_complement_equiv_one

end YMGap.Continuum.SU2PhysicalOuterCutoffNomeCRealLimit
