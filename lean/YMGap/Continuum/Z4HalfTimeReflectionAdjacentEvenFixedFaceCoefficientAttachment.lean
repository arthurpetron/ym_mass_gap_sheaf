/-
# Physical fixed-face coefficients and the directed-compatibility fence

The incidence contraction previously left the fixed spatial face labels
unsummed.  This file inserts their literal heat-kernel coefficients exactly
once, proves that the resulting bounded physical-label sum is the existing
face-dependent joint-face kernel, and therefore exposes its constructive Gram
and quadratic-form positivity.

The final section audits the tempting next step.  Consecutive post/incoming
channel compatibility is directed.  Its smallest two-state matrix has a
negative rational quadratic form, so the compatibility mask itself is not a
Gram and cannot be attached by a bare Schur-product argument.  This is a fence
against that specific positivity shortcut, not a claim that every structured
reflection-symmetric contraction must fail.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQProduct_pointwise_mul_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    listQProduct (fun item => left item * right item) items ≈
      listQProduct left items * listQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (listQProduct_pointwise_mul_local left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (listQProduct left tail) (listQProduct right tail)

/-! ## 1. Literal physical fixed-face coefficient sum -/

/-- Product of the heat-kernel coefficients of the literal fixed faces. -/
def adjacentEvenFixedFaceCoefficientProduct
    (K radius : Nat) (physical : Nat → Nat) : Q' :=
  eliminateLinks (fun id =>
    coeffAt (heatKernelPacket K anchorCoupling) (physical id))
    (adjacentEvenFixedFaceIds radius)

/-- The fixed-face part of the incidence contraction, with one physical
coefficient per fixed face and the already-regrouped transition product. -/
def adjacentEvenFixedFaceCoefficientTransitionSum
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQSum (fun physical =>
    adjacentEvenFixedFaceCoefficientProduct K radius physical *
      adjacentEvenFaceTransitionProduct
        radius physical source trajectory)
    (boundedEdgeLabellings K (adjacentEvenFixedFaceIds radius))

/-- Pointwise, the product of one coefficient and one four-link transition at
each fixed face is the physical coefficient product times the face-transition
product. -/
theorem adjacentEvenDependentFixedFaceIntegrand_eqv_coefficient_mul_transition
    (K radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    eliminateLinks (fun id =>
        dependentFixedFaceLabelFactor K radius
          (adjacentEvenTrajectoryIncomingField radius source trajectory)
          (adjacentEvenTrajectoryOutgoingField trajectory)
          id (physical id))
        (adjacentEvenFixedFaceIds radius) ≈
      adjacentEvenFixedFaceCoefficientProduct K radius physical *
        adjacentEvenFaceTransitionProduct
          radius physical source trajectory := by
  unfold dependentFixedFaceLabelFactor
    adjacentEvenFixedFaceCoefficientProduct
    adjacentEvenFaceTransitionProduct
    adjacentEvenFaceIncomingFourChannels
    adjacentEvenFaceOutgoingFourChannels
    adjacentEvenTrajectoryIncomingField
    adjacentEvenTrajectoryOutgoingField
  rw [eliminateLinks_eq_listQProduct,
    eliminateLinks_eq_listQProduct]
  exact listQProduct_pointwise_mul_local
    (fun id =>
      coeffAt (heatKernelPacket K anchorCoupling) (physical id))
    (fun id =>
      fourFusionIndicator
        (fixedFaceFourChannels radius id (fun link =>
          adjacentEvenIncidenceIncomingChannel
            radius source trajectory (id, link)))
        (physical id)
        (fixedFaceFourChannels radius id (fun link =>
          trajectory link id)))
    (adjacentEvenFixedFaceIds radius)

/-- The literal physical fixed-face sum is exactly the face-dependent
joint-face kernel on the trajectory predecessor/post-channel fields. -/
theorem adjacentEvenFixedFaceCoefficientTransitionSum_eqv_resummedKernel
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenFixedFaceCoefficientTransitionSum
        K radius source trajectory ≈
      adjacentEvenTrajectoryFixedFaceResummedKernel
        K radius source trajectory := by
  unfold adjacentEvenFixedFaceCoefficientTransitionSum
    adjacentEvenTrajectoryFixedFaceResummedKernel
    adjacentEvenGlobalDependentFixedFaceChannelKernel
  exact Q'.eqv_symm
    (listQSum_congr
      (fun physical =>
        adjacentEvenDependentFixedFaceIntegrand_eqv_coefficient_mul_transition
          K radius physical source trajectory)
      (boundedEdgeLabellings K (adjacentEvenFixedFaceIds radius)))

/-- Consequently, the summed physical fixed-face contraction is the exact
product of the duplicate-free resummed four-channel face blocks. -/
theorem adjacentEvenFixedFaceCoefficientTransitionSum_eqv_blockProduct
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenFixedFaceCoefficientTransitionSum
        K radius source trajectory ≈
      adjacentEvenDependentFixedFaceBlockProduct K radius
        (adjacentEvenTrajectoryIncomingField radius source trajectory)
        (adjacentEvenTrajectoryOutgoingField trajectory) :=
  Q'.eqv_trans _ _ _
    (adjacentEvenFixedFaceCoefficientTransitionSum_eqv_resummedKernel
      K radius source trajectory)
    (adjacentEvenTrajectoryFixedFaceResummedKernel_eqv_blockProduct
      K radius source trajectory)

/-! ## 2. Unconditional positivity retained by the physical face sum -/

/-- Every bounded pullback of the literal physical fixed-face sum has a
nonnegative quadratic form.  The configuration map may encode any finite
source/trajectory enumeration, provided its channels lie in the advertised
window. -/
theorem adjacentEvenGlobalDependentFixedFaceChannelQuadratic_nonnegative
    (faceCutoff channelCutoff radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (hchannel : ∀ configuration id link,
      channelState configuration id link ≤ channelCutoff)
    (coefficient : Nat → Q') (configurationCount : Nat) :
    (0 : Q') ≤ gramQuadForm
      (adjacentEvenGlobalDependentFixedFaceChannelMatrix
        faceCutoff radius channelState)
      coefficient configurationCount :=
  gramPSD_quadForm_nonneg
    (adjacentEvenGlobalDependentFixedFaceChannelGramRep
      faceCutoff channelCutoff radius channelState hchannel)
    coefficient configurationCount

/-- Lower/source amplitudes can be absorbed into the test-vector coordinates
without any sign assumption.  This is the strongest unconditional attachment
available before identifying the directed predecessor/post compatibility with
a single common configuration map. -/
theorem adjacentEvenProductionLowerWeightedQuadratic_nonnegative
    (K radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (hchannel : ∀ configuration id link,
      channelState configuration id link ≤ linkAuxiliaryCutoff K)
    (lowerAmplitude coefficient : Nat → Q')
    (configurationCount : Nat) :
    (0 : Q') ≤ gramQuadForm
      (adjacentEvenGlobalDependentFixedFaceChannelMatrix
        K radius channelState)
      (fun configuration =>
        lowerAmplitude configuration * coefficient configuration)
      configurationCount :=
  gramPSD_quadForm_nonneg
    (adjacentEvenProductionDependentFixedFaceChannelGramRep
      K radius channelState hchannel)
    (fun configuration =>
      lowerAmplitude configuration * coefficient configuration)
    configurationCount

/-! ## 3. Fence: directed consecutive-channel compatibility is not Gram -/

/-- A minimal channel state records the incoming and post-face channels at one
incidence. -/
structure TwoStepChannelState where
  incoming : Nat
  post : Nat
deriving DecidableEq

/-- Directed compatibility from a left incidence to the next incidence:
the next incoming channel must equal the preceding post channel. -/
def twoStepDirectedCompatibility
    (left right : TwoStepChannelState) : Q' :=
  if right.incoming = left.post then 1 else 0

/-- Two concrete states exposing the directed corner. -/
def twoStepCompatibilityTestState : Nat → TwoStepChannelState
  | 0 => ⟨0, 1⟩
  | _ => ⟨1, 1⟩

def twoStepDirectedCompatibilityMatrix (left right : Nat) : Q' :=
  twoStepDirectedCompatibility
    (twoStepCompatibilityTestState left)
    (twoStepCompatibilityTestState right)

def twoStepCompatibilityBadVector (index : Nat) : Q' :=
  if index = 0 then (-2 : Q') else if index = 1 then 1 else 0

/-- The exact `2 × 2` directed corner has quadratic form `-1`. -/
theorem twoStepDirectedCompatibility_not_psd :
    ¬ ((0 : Q') ≤ gramQuadForm
      twoStepDirectedCompatibilityMatrix
      twoStepCompatibilityBadVector 2) := by
  decide

/-- A bare directed predecessor/post compatibility mask is not a Gram.  Thus
the face-dependent Gram cannot be pushed through trajectory compatibility by
simply Schur-multiplying by this mask; a palindromic factorization, commuting
layer decomposition, or another structured mechanism is required. -/
theorem twoStepDirectedCompatibility_not_gramRep :
    GramRep twoStepDirectedCompatibilityMatrix → False :=
  fun rep => twoStepDirectedCompatibility_not_psd
    (gramPSD_quadForm_nonneg rep twoStepCompatibilityBadVector 2)

/-! ## 4. The mixed incoming/outgoing pullback already fails on one face -/

def mixedFaceIncomingTestState : Nat → FourChannels
  | 0 => ⟨0, 0, 0, 0⟩
  | _ => ⟨1, 1, 1, 1⟩

def mixedFaceOutgoingTestState : Nat → FourChannels :=
  fun _ => ⟨1, 1, 1, 1⟩

/-- This is the literal cutoff-one physical fixed-face coefficient sum, but
pulled back along distinct incoming and outgoing configuration maps. -/
def mixedFacePhysicalCoefficientMatrix (left right : Nat) : Q' :=
  anchorJointFourResummedFaceKernel 1
    (mixedFaceIncomingTestState left)
    (mixedFaceOutgoingTestState right)

def mixedFacePhysicalCoefficientBadVector (index : Nat) : Q' :=
  if index = 0 then (2 : Q') else if index = 1 then (-1 : Q') else 0

/-- Even after the literal positive heat-kernel coefficient is summed, the
mixed-map `2 × 2` corner has a strictly negative quadratic form. -/
theorem mixedFacePhysicalCoefficientMatrix_not_psd :
    ¬ ((0 : Q') ≤ gramQuadForm
      mixedFacePhysicalCoefficientMatrix
      mixedFacePhysicalCoefficientBadVector 2) := by
  decide

/-- Distinct predecessor and post-channel maps do not constitute a Gram
pullback merely because the underlying joint-face kernel is a Gram. -/
theorem mixedFacePhysicalCoefficientMatrix_not_gramRep :
    GramRep mixedFacePhysicalCoefficientMatrix → False :=
  fun rep => mixedFacePhysicalCoefficientMatrix_not_psd
    (gramPSD_quadForm_nonneg rep mixedFacePhysicalCoefficientBadVector 2)

#print axioms adjacentEvenDependentFixedFaceIntegrand_eqv_coefficient_mul_transition
#print axioms adjacentEvenFixedFaceCoefficientTransitionSum_eqv_resummedKernel
#print axioms adjacentEvenFixedFaceCoefficientTransitionSum_eqv_blockProduct
#print axioms adjacentEvenGlobalDependentFixedFaceChannelQuadratic_nonnegative
#print axioms adjacentEvenProductionLowerWeightedQuadratic_nonnegative
#print axioms twoStepDirectedCompatibility_not_psd
#print axioms twoStepDirectedCompatibility_not_gramRep
#print axioms mixedFacePhysicalCoefficientMatrix_not_psd
#print axioms mixedFacePhysicalCoefficientMatrix_not_gramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment
