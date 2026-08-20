/-
# Genuine cutoff-two cube Gram integrand

This module joins the production fixed-face heat factor, the production
fixed-link multiplicities, and two copies of the genuine cube half amplitude.
The result is exactly the finite scoped factor graph used by the certified
sparse interface contraction, up to the explicit lower-face scalar squared.

This is a finite cutoff-two, half-extent-zero identity.  It makes no
cutoff-uniform, volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQProduct_append_local
    {Item : Type} (value : Item → Q') : ∀ left right,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_local value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem ofNat_natListProduct_eqv_listQProduct
    {Item : Type} (value : Item → Nat) : ∀ items : List Item,
    Q'.ofNat (natListProduct value items) ≈
      listQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, listQProduct]
      exact Q'.eqv_trans _ _ _
        (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
          (value head) (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_listQProduct value tail))

private theorem q_cube_integrand_rearrange
    (face fixed scalar cube : Q') :
    (face * fixed) * ((scalar * cube) * (scalar * cube)) ≈
      (scalar * scalar) * ((face * (cube * cube)) * fixed) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

def cutoffTwoCubeLowerFaceScalar : Q' :=
  Q'.mkPos 1 4096 (by decide)

def cutoffTwoCubeGramScalar : Q' :=
  cutoffTwoCubeLowerFaceScalar * cutoffTwoCubeLowerFaceScalar

/-! ## 1. The production fixed-link product is the scoped table product -/

theorem cutoffTwoFixedLinkProduct_eqv_scopedProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    Q'.ofNat
        (slabLinkMultiplicityProductOn 2 1
          (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
            zeroEdgeLabelling)
          (centralFixedLinks 0)) ≈
      scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary := by
  refine Q'.eqv_trans _
    (listQProduct
      (fun link =>
        Q'.ofNat
          (slabExplicitLinkMultiplicity 2 1
            (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
              zeroEdgeLabelling) link))
      (centralFixedLinks 0)) _ ?_ ?_
  · unfold slabLinkMultiplicityProductOn
    exact ofNat_natListProduct_eqv_listQProduct _ _
  · unfold scopedFactorProduct cutoffTwoCubeFixedLinkFactors
    rw [listQProduct_map]
    apply listQProduct_congr_eqv
    intro link _
    exact Q'.eqv_symm
      (cutoffTwoFixedLinkTableFactor_eqv_production
        link boundary hboundary)

theorem centralBoundaryWeight_cutoffTwo_eqv_scopedProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary ≈
      slabFaceFactorOn cutoffTwoHalfCoupling 2
          (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
            zeroEdgeLabelling)
          (centralFixedFaceIds 0) *
        scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary := by
  unfold centralBoundaryWeight centralFixedWeight
  exact q_mul_congr
    (Q'.eqv_refl _)
    (cutoffTwoFixedLinkProduct_eqv_scopedProduct boundary hboundary)

/-! ## 2. Complete genuine cube Gram integrand -/

theorem cutoffTwoCubePhysicalGramIntegrand_eqv_scopedProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary *
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            centralLowerCubeState boundary *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            centralLowerCubeState boundary) ≈
      cutoffTwoCubeGramScalar *
        scopedFactorProduct cutoffTwoCubeInterfaceFactors boundary := by
  let face := slabFaceFactorOn cutoffTwoHalfCoupling 2
    (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
      zeroEdgeLabelling)
    (centralFixedFaceIds 0)
  let fixed := scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary
  let cube := scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary
  let scalar := cutoffTwoCubeLowerFaceScalar
  have hweight :
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary ≈
        face * fixed :=
    centralBoundaryWeight_cutoffTwo_eqv_scopedProduct boundary hboundary
  have hamp :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState boundary ≈ scalar * cube := by
    simpa [scalar, cube, cutoffTwoCubeLowerFaceScalar] using
      (centralHalfAmplitude_cutoffTwo_cube_eqv_factorProduct
        boundary hboundary)
  have hunary : face * (cube * cube) ≈
      scopedFactorProduct cutoffTwoCubeInterfaceUnaryFactors boundary := by
    simpa [face, cube] using
      (cutoffTwoCubeFixedFaceAndSupport_eqv_unaryProduct
        boundary hboundary)
  refine Q'.eqv_trans _
    ((face * fixed) * ((scalar * cube) * (scalar * cube))) _
    (q_mul_congr hweight (q_mul_congr hamp hamp)) ?_
  refine Q'.eqv_trans _
    ((scalar * scalar) * ((face * (cube * cube)) * fixed)) _
    (q_cube_integrand_rearrange face fixed scalar cube) ?_
  refine Q'.eqv_trans _
    ((scalar * scalar) *
      (scopedFactorProduct cutoffTwoCubeInterfaceUnaryFactors boundary *
        scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary)) _
    (Q'.mul_eqv_congr_left _ _ _
      (q_mul_congr hunary (Q'.eqv_refl _))) ?_
  unfold cutoffTwoCubeGramScalar cutoffTwoCubeInterfaceFactors
    scopedFactorProduct
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (listQProduct_append_local
        (fun factor : ScopedQFactor => factor.value boundary)
        cutoffTwoCubeInterfaceUnaryFactors
        cutoffTwoCubeFixedLinkFactors))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand.cutoffTwoFixedLinkProduct_eqv_scopedProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand.centralBoundaryWeight_cutoffTwo_eqv_scopedProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand.cutoffTwoCubePhysicalGramIntegrand_eqv_scopedProduct
