/-
# Actual BF4 retained SU(2) interface Gram

`BF4RetainedPathConditionalOrder` proves positivity conditionally on a
rank-one retained kinetic channel.  The corrected finite SU(2) reflection
slab already contains a concrete instance of that premise:

* endpoints are the literal bounded lower-half face labellings;
* retained channels are the literal bounded fixed cross-plane labellings;
* the half-amplitude is `centralHalfAmplitude`;
* the retained nonnegative weight is `centralBoundaryWeight`.

This file embeds every boundary channel as a singleton retained path.  On
that carrier, the actual production kernel is exactly

    sum_boundary boundaryWeight(boundary)
      * amplitude(left,boundary) * amplitude(right,boundary),

and therefore exactly the retained rank-one Feynman--Kac kernel from
`BF4RetainedPathConditionalOrder`.

The factorization is valid for every finite character cutoff `K`, every slab
half-width, and every nonnegative rational heat nome.  Thus the finite
orientation/phase issue is already resolved: the reflected upper factor is
the same real SU(2) half-amplitude by
`centralUpperFactor_assembled_eq_lowerAmplitude`.  What is not proved here
is a cutoff-free limit of these changing finite carriers, nor an
identification with the continuous five-holonomy Feynman--Kac kernel.

## Dependency gate

Constructive finite lists and exact rational arithmetic only.
-/

import YMGap.Continuum.BF4RetainedPathConditionalOrder
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

namespace YMGap.Continuum.BF4RetainedSU2InterfaceGram

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The actual retained singleton-channel carrier -/

/-- Every fixed cross-plane labelling, retained as a one-element path. -/
def retainedBoundaryPaths (K half : Nat) :
    List (List EdgeLabelling) :=
  (centralBoundaryChannels K half).map
    (fun boundary => [boundary])

/-- Read the physical lower-half amplitude on a singleton retained boundary
path.  Non-singleton values are irrelevant to `retainedBoundaryPaths` and are
set to zero constructively. -/
def retainedBoundaryAmplitude
    (w : Q') (K half : Nat)
    (endpoint : EdgeLabelling) :
    List EdgeLabelling → Q'
  | [boundary] =>
      centralHalfAmplitude w K half endpoint boundary
  | _ => 0

/-- The genuine fixed-interface weight appearing in the production slab
summand. -/
def retainedBoundaryPotential
    (w : Q') (K half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight w K half boundary

/-- The actual retained rank-one kinetic channel. -/
def retainedSU2Kinetic
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling)
    (path : List EdgeLabelling) : Q' :=
  retainedGramKinetic
    (retainedBoundaryAmplitude w K half)
    left right path

/-- The finite retained Feynman--Kac kernel on the literal BF4 interface
carrier. -/
def retainedSU2FeynmanKacKernel
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  feynmanKacPathKernel
    (retainedBoundaryPaths K half)
    (retainedSU2Kinetic w K half)
    (retainedBoundaryPotential w K half)
    left right

/-! ## 2. Singleton retention is exactly the physical weighted Gram -/

/-- Retaining a boundary as a singleton path converts the retained
Feynman--Kac sum into the existing literal physical weighted Gram. -/
theorem retainedSU2FeynmanKacKernel_eq_weightedGram
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) :
    retainedSU2FeynmanKacKernel w K half left right ≈
      weightedGram
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        left right := by
  unfold retainedSU2FeynmanKacKernel
    feynmanKacPathKernel retainedBoundaryPaths
  rw [listQSum_map]
  unfold retainedSU2Kinetic retainedGramKinetic
    retainedBoundaryAmplitude retainedBoundaryPotential
    pathPotentialProduct weightedGram
  apply listQSum_congr_on
  intro boundary _
  let leftAmplitude :=
    centralHalfAmplitude w K half left boundary
  let rightAmplitude :=
    centralHalfAmplitude w K half right boundary
  let boundaryWeight :=
    centralBoundaryWeight w K half boundary
  change
    (leftAmplitude * rightAmplitude) *
        (boundaryWeight * 1) ≈
      boundaryWeight *
        (leftAmplitude * rightAmplitude)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (leftAmplitude * rightAmplitude)
      (boundaryWeight * 1) boundaryWeight
      (Q'.mul_one_eqv boundaryWeight))
    (Q'.mul_comm_eqv
      (leftAmplitude * rightAmplitude)
      boundaryWeight)

/-- **Concrete retained-channel factorization of the production kernel.**
For actual bounded lower states, the complete finite SU(2) reflected slab
kernel is exactly the retained rank-one Feynman--Kac kernel. -/
theorem centralPhysicalReflectedKernel_eq_retainedSU2FeynmanKac
    (w : Q') {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralPhysicalReflectedKernel w K half left right ≈
      retainedSU2FeynmanKacKernel
        w K half left right := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      w hleft hright)
    (Q'.eqv_symm
      (retainedSU2FeynmanKacKernel_eq_weightedGram
        w K half left right))

/-! ## 3. Nonnegativity of the actual retained interface weight -/

private theorem slabFaceFactorOn_nonnegative_all
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      (0 : Q') ≤ slabFaceFactorOn w K physical ids
  | [] => Q'.zero_le_one
  | id :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      apply Q'.mul_nonneg
      · by_cases hspin : physical id < K + 1
        · rw [coeffAt_heatKernelPacket hspin]
          exact coeffW_nonneg hw _
        · have hlarge : K < physical id := by omega
          rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
          exact Q'.le_refl' 0
      · exact slabFaceFactorOn_nonnegative_all
          hw K physical tail

/-- Unlike the bounded-on-carrier lemma used by the original finite Gram,
the retained potential is nonnegative on every labelling.  Out-of-cutoff
face labels simply have zero heat-packet coefficient. -/
theorem retainedBoundaryPotential_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      retainedBoundaryPotential w K half boundary := by
  unfold retainedBoundaryPotential centralBoundaryWeight
    centralFixedWeight
  exact Q'.mul_nonneg _ _
    (slabFaceFactorOn_nonnegative_all
      hw K
      (assembleReflectedSlabLabelling half
        zeroEdgeLabelling boundary zeroEdgeLabelling)
      (centralFixedFaceIds half))
    (ExpNeg.ofNat_nonneg' _)

/-! ## 4. The actual finite quadratic is the retained-path quadratic -/

/-- The retained-path quadratic built from the concrete BF4 amplitudes and
fixed-interface weights. -/
def retainedSU2Quadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling → Q') : Q' :=
  retainedFeynmanKacQuadratic
    (centralHalfStates K half)
    (retainedBoundaryPaths K half)
    (retainedBoundaryAmplitude w K half)
    (retainedBoundaryPotential w K half)
    coefficient

/-- The production reflection quadratic is exactly the concrete retained
rank-one path quadratic. -/
theorem centralPhysicalReflectionQuadratic_eq_retainedSU2
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    centralPhysicalReflectionQuadratic
        w K half coefficient ≈
      retainedSU2Quadratic
        w K half coefficient := by
  unfold centralPhysicalReflectionQuadratic
    retainedSU2Quadratic retainedFeynmanKacQuadratic
    finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left
    (coefficient left * coefficient right) _ _
    (centralPhysicalReflectedKernel_eq_retainedSU2FeynmanKac
      w hleft hright)

/-- The actual finite BF4 reflected slab quadratic is nonnegative directly
through the retained-path Gram theorem. -/
theorem centralPhysicalReflectionQuadratic_nonnegative_via_retained
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralPhysicalReflectionQuadratic
        w K half coefficient := by
  have hretained :
      (0 : Q') ≤
        retainedSU2Quadratic
          w K half coefficient := by
    unfold retainedSU2Quadratic
    exact retainedFeynmanKacQuadratic_nonnegative
      (centralHalfStates K half)
      (retainedBoundaryPaths K half)
      (retainedBoundaryAmplitude w K half)
      (retainedBoundaryPotential w K half)
      (retainedBoundaryPotential_nonnegative hw K half)
      coefficient
  exact Q'.le_trans' _ _ _
    hretained
    (Q'.ge_of_eqv
      (centralPhysicalReflectionQuadratic_eq_retainedSU2
        w K half coefficient))

/-! ## 5. Gram positivity is not scalar retained-path positivity -/

/-- If one actual retained SU(2) channel is negative, then the scalar
nonnegativity field of `RetainedKineticHarnackData` cannot be populated on
the full physical finite carrier.  This is the precise interface between
the Gram result above and the still-missing Harnack input. -/
theorem no_retainedSU2HarnackData_of_negative_channel
    {w : Q'} {K half : Nat}
    {left right boundary : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half)
    (hboundary : boundary ∈ centralBoundaryChannels K half)
    (hnegative :
      retainedSU2Kinetic
        w K half left right [boundary] < (0 : Q')) :
    RetainedKineticHarnackData
        (retainedBoundaryPaths K half)
        (retainedSU2Kinetic w K half)
        (centralHalfStates K half)
        (centralHalfStates K half) → False := by
  intro data
  have hpath :
      [boundary] ∈ retainedBoundaryPaths K half := by
    unfold retainedBoundaryPaths
    exact List.mem_map.mpr
      ⟨boundary, hboundary, rfl⟩
  have hnonnegative :
      (0 : Q') ≤
        retainedSU2Kinetic
          w K half left right [boundary] :=
    data.kinetic_nonnegative
      left hleft right hright [boundary] hpath
  exact (Int.not_lt_of_ge hnonnegative) hnegative

/-! The following two-state exact model shows that the preceding
obstruction is genuinely specific to scalar entrywise order: a rank-one
Gram channel may have a negative off-diagonal entry while every finite
quadratic remains nonnegative. -/

def signedGramFencePaths : List (List Unit) :=
  [[()]]

def signedGramFenceEndpoints : List Nat :=
  [0, 1]

def signedGramFenceAmplitude
    (endpoint : Nat) (_path : List Unit) : Q' :=
  if endpoint = 0 then 1 else -1

def signedGramFenceKinetic
    (left right : Nat) (path : List Unit) : Q' :=
  retainedGramKinetic
    signedGramFenceAmplitude left right path

def signedGramFencePotential (_state : Unit) : Q' :=
  1

/-- The exact rank-one channel with amplitudes `+1` and `-1` has negative
off-diagonal kinetic entry. -/
theorem signedGramFenceKinetic_offDiagonal_negative :
    signedGramFenceKinetic 0 1 [()] < (0 : Q') := by
  decide

/-- Despite that negative entry, every coefficient vector has a
nonnegative retained Feynman--Kac quadratic. -/
theorem signedGramFenceQuadratic_nonnegative
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      retainedFeynmanKacQuadratic
        signedGramFenceEndpoints
        signedGramFencePaths
        signedGramFenceAmplitude
        signedGramFencePotential
        coefficient := by
  exact retainedFeynmanKacQuadratic_nonnegative
    signedGramFenceEndpoints
    signedGramFencePaths
    signedGramFenceAmplitude
    signedGramFencePotential
    (fun _ => Q'.zero_le_one)
    coefficient

/-- Machine fence: rank-one Gram/CP positivity alone does not produce the
entrywise nonnegative kinetic datum required by the scalar Harnack bridge. -/
theorem signedGramFence_has_no_retainedKineticHarnackData :
    RetainedKineticHarnackData
        signedGramFencePaths
        signedGramFenceKinetic
        signedGramFenceEndpoints
        signedGramFenceEndpoints → False := by
  intro data
  have hnonnegative :
      (0 : Q') ≤
        signedGramFenceKinetic 0 1 [()] :=
    data.kinetic_nonnegative
      0 (by decide)
      1 (by decide)
      [()] (by decide)
  exact
    (Int.not_lt_of_ge hnonnegative)
      signedGramFenceKinetic_offDiagonal_negative

end YMGap.Continuum.BF4RetainedSU2InterfaceGram

#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.retainedSU2FeynmanKacKernel_eq_weightedGram
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.centralPhysicalReflectedKernel_eq_retainedSU2FeynmanKac
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.retainedBoundaryPotential_nonnegative
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.centralPhysicalReflectionQuadratic_eq_retainedSU2
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.centralPhysicalReflectionQuadratic_nonnegative_via_retained
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.no_retainedSU2HarnackData_of_negative_channel
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.signedGramFenceKinetic_offDiagonal_negative
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.signedGramFenceQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4RetainedSU2InterfaceGram.signedGramFence_has_no_retainedKineticHarnackData
