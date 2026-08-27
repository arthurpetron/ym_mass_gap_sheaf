/-
# The first valence-five associator as a finite bistochastic block sum

For fixed external labels, the first associator acts independently in every
transient-output `y` sector and leaves the final fusion `y,d -> e` untouched.
We enumerate the admissible sectors and their complete left/right channel
fibers, zero-extend between distinct sectors, and prove exact row and column
normalization.

Constructive contract: bounded filtered lists, proof-carrying fusion data,
and exact `Q'` algebra only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernel
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
import YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier

namespace YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Explicit transient-output sectors -/

/-- Every possible output of the first three external factors is bounded by
their total degree; retain exactly those which can fuse with `d` to `e`. -/
def valenceFiveTransientOutputs (a b c d e : Nat) : List Nat :=
  (List.range (a + b + c + 1)).filter (fun y => fusionOK y d e)

private theorem range_nodup (bound : Nat) : (List.range bound).Nodup := by
  induction bound with
  | zero => exact List.nodup_nil
  | succ bound ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem valenceFiveTransientOutputs_nodup (a b c d e : Nat) :
    (valenceFiveTransientOutputs a b c d e).Nodup :=
  List.filter_sublist.nodup (range_nodup (a + b + c + 1))

private theorem fixedLeft_output_le_total {a b c y : Nat}
    (channel : FixedLeftCGChannel a b c y) : y ≤ a + b + c := by
  have hk := Nat.le_min.mp channel.k_le
  have hr := Nat.le_min.mp channel.r_le
  have hout := channel.degree_eq
  unfold FixedLeftCGChannel.intermediate at hr
  omega

private theorem fixedRight_output_le_total {a b c y : Nat}
    (channel : FixedRightCGChannel a b c y) : y ≤ a + b + c := by
  have hp := Nat.le_min.mp channel.p_le
  have hr := Nat.le_min.mp channel.r_le
  have hout := channel.degree_eq
  unfold FixedRightCGChannel.intermediate at hr
  omega

theorem valenceFiveLeftCarrier_y_mem_transientOutputs {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e) :
    source.y ∈ valenceFiveTransientOutputs a b c d e := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr
      (Nat.lt_succ_of_le (fixedLeft_output_le_total source.firstLeft)),
    source.suffix.fusionOK⟩

theorem valenceFiveMiddleCarrier_y_mem_transientOutputs {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middle.y ∈ valenceFiveTransientOutputs a b c d e := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr
      (Nat.lt_succ_of_le (fixedRight_output_le_total middle.first)),
    middle.suffix.fusionOK⟩

abbrev ValenceFiveTransientIndex (a b c d e : Nat) :=
  {y // y ∈ valenceFiveTransientOutputs a b c d e}

def transientSuffix {a b c d e : Nat}
    (index : ValenceFiveTransientIndex a b c d e) :
    CGFusionStep index.val d e :=
  cgFusionStepOfFusionOK index.val d e
    (List.mem_filter.mp index.property).2

/-! ## 2. Fiberwise and total carriers -/

def valenceFiveLeftFiber {a b c d e : Nat}
    (index : ValenceFiveTransientIndex a b c d e) :
    List (ValenceFiveLeftCarrier a b c d e) :=
  (fixedLeftChannels a b c index.val).map fun channel =>
    { y := index.val, firstLeft := channel, suffix := transientSuffix index }

def valenceFiveMiddleFiber {a b c d e : Nat}
    (index : ValenceFiveTransientIndex a b c d e) :
    List (ValenceFiveMiddleCarrier a b c d e) :=
  (fixedRightChannels a b c index.val).map fun channel =>
    { y := index.val, first := channel, suffix := transientSuffix index }

def valenceFiveLeftCarriers (a b c d e : Nat) :
    List (ValenceFiveLeftCarrier a b c d e) :=
  (valenceFiveTransientOutputs a b c d e).attach.flatMap
    valenceFiveLeftFiber

def valenceFiveMiddleCarriers (a b c d e : Nat) :
    List (ValenceFiveMiddleCarrier a b c d e) :=
  (valenceFiveTransientOutputs a b c d e).attach.flatMap
    valenceFiveMiddleFiber

/-! ## 3. The zero-extended first block -/

def valenceFiveFirstKernelAt {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e)
    (middle : ValenceFiveMiddleCarrier a b c d e) : Q' :=
  if h : source.y = middle.y then
    valenceFiveFirstBlockKernelAt source middle h
  else 0

theorem valenceFiveFirstKernelAt_nonnegative {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e)
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    (0 : Q') ≤ valenceFiveFirstKernelAt source middle := by
  unfold valenceFiveFirstKernelAt
  split
  · exact valenceFiveFirstBlockKernelAt_nonnegative _ _ _
  · exact Q'.le_refl' 0

private def leftTransientIndex {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e) :
    ValenceFiveTransientIndex a b c d e :=
  ⟨source.y, valenceFiveLeftCarrier_y_mem_transientOutputs source⟩

private def middleTransientIndex {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    ValenceFiveTransientIndex a b c d e :=
  ⟨middle.y, valenceFiveMiddleCarrier_y_mem_transientOutputs middle⟩

private theorem first_row_fiber_mass {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e)
    (index : ValenceFiveTransientIndex a b c d e) :
    listQSum (valenceFiveFirstKernelAt source)
        (valenceFiveMiddleFiber index) ≈
      deterministicKernel (fun _ : Unit => leftTransientIndex source)
        () index := by
  rcases source with ⟨sourceY, sourceChannel, sourceSuffix⟩
  by_cases hY : sourceY = index.val
  · subst sourceY
    simp only [valenceFiveMiddleFiber, listQSum_map,
      valenceFiveFirstKernelAt, valenceFiveFirstBlockKernelAt,
      deterministicKernel, leftTransientIndex]
    exact physicalSchurRecoupling_list_row_normalized sourceChannel
  · have hIndex : index ≠ leftTransientIndex
        (⟨sourceY, sourceChannel, sourceSuffix⟩ :
          ValenceFiveLeftCarrier a b c d e) := by
      intro heq
      exact hY (congrArg Subtype.val heq).symm
    simp only [valenceFiveMiddleFiber, listQSum_map,
      valenceFiveFirstKernelAt, deterministicKernel, hY, hIndex, if_false]
    exact listQSum_zero _

private theorem first_column_fiber_mass {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (index : ValenceFiveTransientIndex a b c d e) :
    listQSum (fun source => valenceFiveFirstKernelAt source middle)
        (valenceFiveLeftFiber index) ≈
      deterministicKernel (fun _ : Unit => middleTransientIndex middle)
        () index := by
  rcases middle with ⟨middleY, middleChannel, middleSuffix⟩
  by_cases hY : middleY = index.val
  · subst middleY
    simp only [valenceFiveLeftFiber, listQSum_map,
      valenceFiveFirstKernelAt, valenceFiveFirstBlockKernelAt,
      deterministicKernel, middleTransientIndex]
    exact physicalSchurRecoupling_list_column_normalized middleChannel
  · have hIndex : index ≠ middleTransientIndex
        (⟨middleY, middleChannel, middleSuffix⟩ :
          ValenceFiveMiddleCarrier a b c d e) := by
      intro heq
      exact hY (congrArg Subtype.val heq).symm
    have hY' : index.val ≠ middleY := fun heq => hY heq.symm
    simp only [valenceFiveLeftFiber, listQSum_map,
      valenceFiveFirstKernelAt, deterministicKernel, hY', hIndex, if_false]
    exact listQSum_zero _

/-! ## 4. Exact bistochasticity of the first global block -/

theorem valenceFiveFirstKernel_row_normalized {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e) :
    listQSum (valenceFiveFirstKernelAt source)
      (valenceFiveMiddleCarriers a b c d e) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index => listQSum (valenceFiveFirstKernelAt source)
        (valenceFiveMiddleFiber index))
      (valenceFiveTransientOutputs a b c d e).attach) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (deterministicKernel (fun _ : Unit => leftTransientIndex source) ())
        (valenceFiveTransientOutputs a b c d e).attach) _ ?_ ?_
    · exact listQSum_congr
        (fun index => first_row_fiber_mass source index)
        (valenceFiveTransientOutputs a b c d e).attach
    · exact deterministicKernel_row_normalized
        (fun _ : Unit => leftTransientIndex source) ()
        (valenceFiveTransientOutputs a b c d e).attach
        (attach_nodup_of_nodup _
          (valenceFiveTransientOutputs_nodup a b c d e))
        (List.mem_attach _ (leftTransientIndex source))

theorem valenceFiveFirstKernel_column_normalized {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    listQSum (fun source => valenceFiveFirstKernelAt source middle)
      (valenceFiveLeftCarriers a b c d e) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index => listQSum
        (fun source => valenceFiveFirstKernelAt source middle)
        (valenceFiveLeftFiber index))
      (valenceFiveTransientOutputs a b c d e).attach) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (deterministicKernel (fun _ : Unit => middleTransientIndex middle) ())
        (valenceFiveTransientOutputs a b c d e).attach) _ ?_ ?_
    · exact listQSum_congr
        (fun index => first_column_fiber_mass middle index)
        (valenceFiveTransientOutputs a b c d e).attach
    · exact deterministicKernel_row_normalized
        (fun _ : Unit => middleTransientIndex middle) ()
        (valenceFiveTransientOutputs a b c d e).attach
        (attach_nodup_of_nodup _
          (valenceFiveTransientOutputs_nodup a b c d e))
        (List.mem_attach _ (middleTransientIndex middle))

/-- **The first valence-five associator is an exact finite bistochastic
matrix on the complete left and common-middle carriers.** -/
def valenceFiveFirstBistochasticKernel (a b c d e : Nat) :
    FiniteBistochasticQKernel
      (ValenceFiveLeftCarrier a b c d e)
      (ValenceFiveMiddleCarrier a b c d e) where
  sources := valenceFiveLeftCarriers a b c d e
  targets := valenceFiveMiddleCarriers a b c d e
  weight := valenceFiveFirstKernelAt
  weight_nonnegative := valenceFiveFirstKernelAt_nonnegative
  row_normalized := valenceFiveFirstKernel_row_normalized
  column_normalized := valenceFiveFirstKernel_column_normalized

end YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock

#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveLeftCarrier_y_mem_transientOutputs
#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveMiddleCarrier_y_mem_transientOutputs
#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveFirstKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveFirstKernel_row_normalized
#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveFirstKernel_column_normalized
#print axioms YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock.valenceFiveFirstBistochasticKernel
