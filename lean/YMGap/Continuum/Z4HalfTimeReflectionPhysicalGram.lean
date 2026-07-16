/-
# Exact finite reflection Gram for the corrected Z4 spin-foam slab

This is the finite-volume reflection-positivity specialization.  States are
the literal bounded lower-half face labellings and channels are the literal
bounded fixed cross-plane face labellings.  The amplitude is the derived
lower face/link factor and the channel weight is the derived fixed-interface
factor.  Summing the complete production spin-foam term over interface
labellings is proved equal to `FiniteWeightedGramSOS.weightedGram`.

Consequently the complete finite quadratic form, with arbitrary exact
rational coefficients on the enumerated lower states, is a nonnegative
weighted sum of squares.  No unproved reflection-positive input or measured
normalization constant occurs.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
import YMGap.Continuum.FiniteWeightedGramCRealLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal finite states, channels, amplitudes, and weights -/

def centralHalfStates (K half : Nat) : List EdgeLabelling :=
  boundedEdgeLabellings K (centralLowerFaceIds half)

def centralBoundaryChannels (K half : Nat) : List EdgeLabelling :=
  boundedEdgeLabellings K (centralFixedFaceIds half)

def centralHalfAmplitude
    (w : Q') (K half : Nat)
    (state boundary : EdgeLabelling) : Q' :=
  centralLowerFactor w K half
    (assembleReflectedSlabLabelling half state boundary zeroEdgeLabelling)

def centralBoundaryWeight
    (w : Q') (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  centralFixedWeight w K half
    (assembleReflectedSlabLabelling half zeroEdgeLabelling boundary
      zeroEdgeLabelling)

/-- The physical reflected kernel before Gram identification: for each pair
of lower states, sum the complete production spin-foam summand over every
bounded fixed-interface labelling. -/
def centralPhysicalReflectedKernel
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      slabParametricKPhysicalTerm w K (centralExtent half)
        (assembleReflectedSlabLabelling half left boundary right))
    (centralBoundaryChannels K half)

private theorem zeroEdgeLabelling_mem_bounded (K : Nat) :
    forall ids : List Nat,
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

theorem centralBoundaryWeight_nonnegative_on
    {w : Q'} {K half : Nat} (hw : (0 : Q') <= w) :
    forall boundary,
      boundary ∈ centralBoundaryChannels K half ->
      (0 : Q') <= centralBoundaryWeight w K half boundary := by
  intro boundary hboundary
  unfold centralBoundaryWeight
  apply centralFixedWeight_nonnegative hw
  exact assembleReflectedSlabLabelling_bounded
    (zeroEdgeLabelling_mem_bounded K (centralLowerFaceIds half))
    hboundary
    (zeroEdgeLabelling_mem_bounded K (centralLowerFaceIds half))

/-! ## 2. One complete physical summand is one Gram integrand -/

private theorem rotate_three (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  show (a * (b * c)).num * (((b * (a * c)).den) : Int) =
    (b * (a * c)).num * (((a * (b * c)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

theorem centralPhysicalTerm_eq_gram_integrand
    (w : Q') {K half : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hboundary : boundary ∈ centralBoundaryChannels K half)
    (hright : right ∈ centralHalfStates K half) :
    slabParametricKPhysicalTerm w K (centralExtent half)
        (assembleReflectedSlabLabelling half left boundary right) ≈
      centralBoundaryWeight w K half boundary *
        (centralHalfAmplitude w K half left boundary *
          centralHalfAmplitude w K half right boundary) := by
  let assembled :=
    assembleReflectedSlabLabelling half left boundary right
  refine Q'.eqv_trans _
    (centralLowerFactor w K half assembled *
      (centralFixedWeight w K half assembled *
        centralUpperFactor w K half assembled)) _
    (slabParametricKPhysicalTerm_crossPlane_factorization
      w K half assembled) ?_
  rw [centralLowerFactor_assemble_independent_right
      w K half left boundary right,
    centralFixedWeight_assemble_only_boundary
      w K half left boundary right]
  refine Q'.eqv_trans _
    (centralHalfAmplitude w K half left boundary *
      (centralBoundaryWeight w K half boundary *
        centralHalfAmplitude w K half right boundary)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (centralUpperFactor_assembled_eq_lowerAmplitude
          w hleft hboundary hright))
  · exact rotate_three _ _ _

/-! ## 3. Exact physical kernel = weighted Gram -/

theorem centralPhysicalReflectedKernel_eq_weightedGram
    (w : Q') {K half : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralPhysicalReflectedKernel w K half left right ≈
      weightedGram (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half) left right := by
  unfold centralPhysicalReflectedKernel weightedGram
  apply listQSum_congr_on
  intro boundary hboundary
  exact centralPhysicalTerm_eq_gram_integrand
    w hleft hboundary hright

/-! ## 4. The literal physical quadratic form and finite OS positivity -/

def centralPhysicalReflectionQuadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right => (coefficient left * coefficient right) *
        centralPhysicalReflectedKernel w K half left right)
      (centralHalfStates K half))
    (centralHalfStates K half)

theorem centralPhysicalReflectionQuadratic_eq_weightedGram
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    centralPhysicalReflectionQuadratic w K half coefficient ≈
      weightedGramQuadratic
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        coefficient := by
  unfold centralPhysicalReflectionQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      w hleft hright)

/-- Constructive finite-volume Osterwalder--Schrader positivity for the
complete corrected-slab production weight and every rational function on the
enumerated positive-time states. -/
theorem centralPhysicalReflectionQuadratic_nonnegative
    {w : Q'} {K half : Nat} (hw : (0 : Q') <= w)
    (coefficient : EdgeLabelling -> Q') :
    (0 : Q') <= centralPhysicalReflectionQuadratic w K half coefficient := by
  have hgram : (0 : Q') <=
      weightedGramQuadratic
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        coefficient :=
    weightedGramQuadratic_nonnegative _ _ _ _ _
      (centralBoundaryWeight_nonnegative_on hw)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (centralPhysicalReflectionQuadratic_eq_weightedGram
        w K half coefficient))

end YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.zeroEdgeLabelling_mem_bounded
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.centralBoundaryWeight_nonnegative_on
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.centralPhysicalTerm_eq_gram_integrand
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.centralPhysicalReflectedKernel_eq_weightedGram
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.centralPhysicalReflectionQuadratic_eq_weightedGram
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram.centralPhysicalReflectionQuadratic_nonnegative
