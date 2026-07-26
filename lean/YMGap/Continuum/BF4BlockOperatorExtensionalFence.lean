/-
# BF4 block-operator extensional fence

There is one genuine source-indexed, globally link-glued block operator in
the present Lean tree:

    `wholeSlabRecouplingRawWeight`

and, at cutoff one, its normalized completion

    `cutoffOneWholeSlabFiniteKernel`.

It acts from corrected-slab fine character labellings to coarse character
labellings.  It is not the continuous 120-face/five-holonomy Feynman--Kac
operator described in the BF4 notes: the latter currently appears in Lean
only through its constant five-dimensional Gaussian matrices, heat-channel
Hilbert--Schmidt scalar sums, and conditional Perron certificates.

This file proves the strongest extensional obstruction carried by the actual
source-indexed slab operator.  `SlabScalePair` contains a declared function

    couplingFlow : Q' -> Q',

but the raw kernel uses only the endpoint `fine` and `coarse` physical data.
It does not use `couplingFlow`.  We can therefore replace that function
arbitrarily, subject only to agreeing at the single current fine coupling,
without changing a single kernel entry.

The counterexample below makes this literal.  A constant flow and a spiked
flow disagree at a selected probe coupling, yet yield extensionally identical
globally link-glued raw kernels.  Thus neither a cubic AF recurrence nor an AF
heat-time trajectory can be extracted from the present operator declaration.
An `AFEnvelope` cannot become action-linked merely by pairing it with this
kernel: the operator is insensitive to the very flow field that would carry
that identification.

No new open interface is introduced.  The exact missing constructor must be a
definition of the *next physical action from the pushed current action* (or a
proved projection of that pushed law onto a coupling coordinate), so that:

1. the next slab's fine datum is definitionally/propositionally the preceding
   coarse datum;
2. the next coupling is extracted from the blocked physical law, rather than
   stored as a free `couplingFlow` value;
3. the extracted heat time obeys the cubic AF remainder;
4. the lattice spacing is tied to the geometric block rescaling; and
5. the resulting normalized operator is identified with the five-holonomy
   Feynman--Kac kernel.

Until that constructor exists, the exact cutoff-one slab kernel is a genuine
one-step finite operator but not an action-linked BF4/AF trajectory.
-/

import YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

namespace YMGap.Continuum.BF4BlockOperatorExtensionalFence

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Changing the declared flow leaves the physical endpoints fixed -/

/-- Replace the free coupling-flow field of a scale pair while retaining the
same fine and coarse physical actions and geometric/cutoff relations. -/
def replaceCouplingFlow
    (S : SlabScalePair) (flow : Q' → Q')
    (hflow : S.coarse.coupling ≈ flow S.fine.coupling) :
    SlabScalePair where
  fine := S.fine
  coarse := S.coarse
  couplingFlow := flow
  fine_extent := S.fine_extent
  coarse_cutoff := S.coarse_cutoff
  coarse_coupling := hflow

theorem replaceCouplingFlow_fine
    (S : SlabScalePair) (flow : Q' → Q')
    (hflow : S.coarse.coupling ≈ flow S.fine.coupling) :
    (replaceCouplingFlow S flow hflow).fine = S.fine :=
  rfl

theorem replaceCouplingFlow_coarse
    (S : SlabScalePair) (flow : Q' → Q')
    (hflow : S.coarse.coupling ≈ flow S.fine.coupling) :
    (replaceCouplingFlow S flow hflow).coarse = S.coarse :=
  rfl

/-! ## 2. The source-indexed raw block operator is flow-blind -/

/-- Extensional equivalence of the globally link-glued source-indexed raw
operators. -/
def RawBlockKernelEqv (left right : SlabScalePair) : Prop :=
  ∀ fineState coarseState,
    wholeSlabRecouplingRawWeight left fineState coarseState ≈
      wholeSlabRecouplingRawWeight right fineState coarseState

/-- Replacing the declared coupling flow does not change any raw block-kernel
entry.  This is definitional: the kernel uses the physical endpoint actions,
not `SlabScalePair.couplingFlow`. -/
theorem rawBlockKernel_replaceCouplingFlow
    (S : SlabScalePair) (flow : Q' → Q')
    (hflow : S.coarse.coupling ≈ flow S.fine.coupling) :
    RawBlockKernelEqv (replaceCouplingFlow S flow hflow) S := by
  intro fineState coarseState
  exact Q'.eqv_refl _

/-- Extensional equivalence of the declared coupling functions. -/
def CouplingFlowEqv (left right : SlabScalePair) : Prop :=
  ∀ coupling, left.couplingFlow coupling ≈
    right.couplingFlow coupling

/-! ## 3. Two different declared flows, one identical physical operator -/

/-- The constant endpoint flow. -/
def constantEndpointFlow (S : SlabScalePair) (_coupling : Q') : Q' :=
  S.coarse.coupling

/-- A flow equal to the coarse endpoint except at one selected probe. -/
def spikedEndpointFlow
    (S : SlabScalePair) (probe replacement coupling : Q') : Q' :=
  if coupling = probe then replacement else S.coarse.coupling

/-- The scale pair carrying the constant endpoint flow. -/
def constantFlowScalePair (S : SlabScalePair) : SlabScalePair :=
  replaceCouplingFlow S (constantEndpointFlow S)
    (Q'.eqv_refl S.coarse.coupling)

/-- The scale pair carrying a spike away from the current fine coupling. -/
def spikedFlowScalePair
    (S : SlabScalePair) (probe replacement : Q')
    (hprobe : probe ≠ S.fine.coupling) :
    SlabScalePair :=
  replaceCouplingFlow S
    (spikedEndpointFlow S probe replacement) (by
      unfold spikedEndpointFlow
      rw [if_neg (fun heq => hprobe heq.symm)]
      exact Q'.eqv_refl S.coarse.coupling)

/-- The constant and spiked declarations give exactly the same source-indexed
raw block operator. -/
theorem constant_spiked_rawBlockKernel_eqv
    (S : SlabScalePair) (probe replacement : Q')
    (hprobe : probe ≠ S.fine.coupling) :
    RawBlockKernelEqv
      (constantFlowScalePair S)
      (spikedFlowScalePair S probe replacement hprobe) := by
  intro fineState coarseState
  exact Q'.eqv_refl _

/-- If the spike value differs from the physical coarse endpoint, the two
declared coupling flows are not extensionally equivalent. -/
theorem constant_spiked_couplingFlow_not_eqv
    (S : SlabScalePair) (probe replacement : Q')
    (hprobe : probe ≠ S.fine.coupling)
    (hreplacement : ¬ replacement ≈ S.coarse.coupling) :
    ¬ CouplingFlowEqv
      (constantFlowScalePair S)
      (spikedFlowScalePair S probe replacement hprobe) := by
  intro hflows
  have hatProbe := hflows probe
  change S.coarse.coupling ≈
    (if probe = probe then replacement else S.coarse.coupling) at hatProbe
  rw [if_pos rfl] at hatProbe
  exact hreplacement (Q'.eqv_symm hatProbe)

/-- **The extensional obstruction.**  The same genuine source-indexed slab
operator supports two inequivalent declared coupling flows.  Hence the
operator declaration does not determine the flow needed for an AF recurrence. -/
theorem rawBlockKernel_does_not_determine_couplingFlow
    (S : SlabScalePair) (probe replacement : Q')
    (hprobe : probe ≠ S.fine.coupling)
    (hreplacement : ¬ replacement ≈ S.coarse.coupling) :
    RawBlockKernelEqv
        (constantFlowScalePair S)
        (spikedFlowScalePair S probe replacement hprobe) ∧
      ¬ CouplingFlowEqv
        (constantFlowScalePair S)
        (spikedFlowScalePair S probe replacement hprobe) :=
  ⟨constant_spiked_rawBlockKernel_eqv S probe replacement hprobe,
    constant_spiked_couplingFlow_not_eqv
      S probe replacement hprobe hreplacement⟩

/-! ## 4. Consequence for the BF4/AF handoff

The extensional counterexample isolates the missing *constructor*, rather
than adding another assumption record.  The next physical definition must
construct the coarse action/coupling from the blocked fine law itself and
export its equality with the next scale.  Only then can an extracted heat
coordinate be subjected to `AFTrajectoryCertificate.recurrence` and its
geometric spacing be fed to `BF4AFHeatSpacing`.

The present five-holonomy Lean modules cannot supply that constructor:

* `BF4FiveHolonomyGaussian.generalizedA` is a fixed quadratic-limit matrix;
* `SU2GroupedFiveHolonomyHilbertSchmidt` completes scalar tensor norms for a
  supplied heat nome;
* `FiveHolonomyPerronCutoff` consumes a supplied nonlinear spectral ratio;
* no declaration is a source/target five-holonomy Feynman--Kac kernel
  parameterized by a physical action and closed under block iteration.

Accordingly no cubic AF recurrence or spacing identification is derived here.
The failure is now extensional and kernel-checked, not merely a repository
search result.
-/

end YMGap.Continuum.BF4BlockOperatorExtensionalFence

#print axioms YMGap.Continuum.BF4BlockOperatorExtensionalFence.replaceCouplingFlow
#print axioms YMGap.Continuum.BF4BlockOperatorExtensionalFence.rawBlockKernel_replaceCouplingFlow
#print axioms YMGap.Continuum.BF4BlockOperatorExtensionalFence.constant_spiked_rawBlockKernel_eqv
#print axioms YMGap.Continuum.BF4BlockOperatorExtensionalFence.constant_spiked_couplingFlow_not_eqv
#print axioms YMGap.Continuum.BF4BlockOperatorExtensionalFence.rawBlockKernel_does_not_determine_couplingFlow
