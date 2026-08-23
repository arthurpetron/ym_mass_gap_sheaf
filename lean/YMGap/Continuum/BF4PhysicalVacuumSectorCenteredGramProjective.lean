/-
# Projective control of the BF4 vacuum-sector boundary posteriors

A single cross-ratio bound for the actual sector half-amplitude matrix is
stable under the two positive summations defining the reflected boundary
Gram.  It therefore controls both normalized posterior pairs:

* `target | boundary` versus the sector stationary law; and
* `boundary | source` versus the sector square-amplitude prior.

At the existing squared-spread ceiling `65/64`, each posterior `L1` distance
is at most `1/4`, so their product gives the actual centered-Gram rate
`1/16`.  The cofinal compiler isolates the remaining finite analytic input
as one division-free half-amplitude cross-ratio estimate on the canonical
vacuum component.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
import YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Projective invariance under positive normalization -/

/-- Dividing the left ray by one positive common denominator preserves its
projective spread against an unchanged right ray. -/
theorem projectiveSpreadBound_divPos_left
    {Index : Type} (carrier : List Index)
    (left right : Index → Q') (spread denominator : Q')
    (denominator_pos : (0 : Q') < denominator)
    (projective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread carrier left right) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread carrier
      (fun index => Q'.divPos (left index) denominator denominator_pos)
      right := by
  intro first first_mem second second_mem
  have h := projective first first_mem second second_mem
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ h
    (Q'.le_of_lt (Q'.recipPos_pos denominator denominator_pos))
  unfold Q'.divPos
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
  · q_ring
  · q_ring

/-- Dividing two rays by independent positive common denominators preserves
their projective spread. -/
theorem projectiveSpreadBound_divPos_both
    {Index : Type} (carrier : List Index)
    (left right : Index → Q') (spread leftDen rightDen : Q')
    (leftDen_pos : (0 : Q') < leftDen)
    (rightDen_pos : (0 : Q') < rightDen)
    (projective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread carrier left right) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread carrier
      (fun index => Q'.divPos (left index) leftDen leftDen_pos)
      (fun index => Q'.divPos (right index) rightDen rightDen_pos) := by
  intro first first_mem second second_mem
  have h := projective first first_mem second second_mem
  let scale :=
    Q'.recipPos leftDen leftDen_pos *
      Q'.recipPos rightDen rightDen_pos
  have hscale : (0 : Q') ≤ scale :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (Q'.recipPos_pos leftDen leftDen_pos))
      (Q'.le_of_lt (Q'.recipPos_pos rightDen rightDen_pos))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ h hscale
  unfold Q'.divPos
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
  · dsimp [scale]
    q_ring
  · dsimp [scale]
    q_ring

/-! ## 2. One sector half-amplitude diameter controls both raw rays -/

/-- The half-amplitude cross-ratio bound survives weighted Gram summation
and becomes a raw target-column versus sector stationary-law bound. -/
theorem centralPhysicalFiniteVacuumSector_targetRawProjective
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (spread : Q')
    (crossRatio :
      ∀ left,
        left ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw cutoff half →
          ∀ right,
            right ∈ centralPhysicalFiniteVacuumSectorIndices
                w hw cutoff half →
              ∀ first,
                first ∈ centralBoundaryChannels cutoff half →
                  ∀ second,
                    second ∈ centralBoundaryChannels cutoff half →
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half left first *
                          centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half right second ≤
                        (spread * spread) *
                          (centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half left second *
                            centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half right first))
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (fun target =>
        centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half target boundary)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half) := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let channelWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  have hraw := finiteColumn_projective_gramRowNumerator
    states channels channelWeight amplitude spread
    (fun state _ channel =>
      centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
        hw cutoff half state channel)
    (fun channel channel_mem =>
      centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
        channel channel_mem)
    crossRatio boundary hboundary
  exact projectiveSpreadBound_of_common_scale
    states
    (fun target => amplitude target boundary)
    (finiteGramRowNumerator states channels channelWeight amplitude)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    spread
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    hraw
    (fun state hstate =>
      centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
        hstate)

/-- The same half-amplitude cross-ratio bound survives row summation and
controls the two raw source/prior boundary numerator rays. -/
theorem centralPhysicalFiniteVacuumSector_sourceRawProjective
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (spread : Q')
    (crossRatio :
      ∀ left,
        left ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw cutoff half →
          ∀ right,
            right ∈ centralPhysicalFiniteVacuumSectorIndices
                w hw cutoff half →
              ∀ first,
                first ∈ centralBoundaryChannels cutoff half →
                  ∀ second,
                    second ∈ centralBoundaryChannels cutoff half →
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half left first *
                          centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half right second ≤
                        (spread * spread) *
                          (centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half left second *
                            centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half right first))
    (source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread (centralBoundaryChannels cutoff half)
      (finiteSourceChannelNumerator
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
        source)
      (finiteChannelPriorNumerator
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)) :=
  finiteSourceChannel_projective_channelPrior
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    spread
    (fun state _ channel =>
      centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
        hw cutoff half state channel)
    (fun channel channel_mem =>
      centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
        channel channel_mem)
    crossRatio source hsource

/-! ## 3. Projective diameter gives the two posterior quarters -/

/-- The sector half-amplitude cross-ratio ceiling gives the target-posterior
quarter on every positive boundary channel. -/
theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_quarter_of_crossRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (spread : Q')
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (crossRatio :
      ∀ left,
        left ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw cutoff half →
          ∀ right,
            right ∈ centralPhysicalFiniteVacuumSectorIndices
                w hw cutoff half →
              ∀ first,
                first ∈ centralBoundaryChannels cutoff half →
                  ∀ second,
                    second ∈ centralBoundaryChannels cutoff half →
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half left first *
                          centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half right second ≤
                        (spread * spread) *
                          (centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half left second *
                            centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half right first)) :
    centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
        w hw cutoff half boundary channelTotal_pos ≤ quarter := by
  unfold centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
  apply finiteL1Distance_le_quarter_of_normalized_projective
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w hw cutoff half boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    spread
  · intro target _
    exact centralPhysicalFiniteVacuumSectorTargetGivenBoundary_nonnegative
      hw cutoff half boundary channelTotal_pos target
  · intro target htarget
    exact Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos htarget)
  · exact centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
      channelTotal_pos
  · exact centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half
  · exact spreadSquare_le
  · exact projectiveSpreadBound_divPos_left
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (fun target =>
        centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half target boundary)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half)
      spread
      (centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary)
      channelTotal_pos
      (centralPhysicalFiniteVacuumSector_targetRawProjective
        spread crossRatio boundary hboundary)

/-- The same sector half-amplitude cross-ratio ceiling gives the source-
posterior quarter for every sector source. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_quarter_of_crossRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (spread : Q')
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (crossRatio :
      ∀ left,
        left ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw cutoff half →
          ∀ right,
            right ∈ centralPhysicalFiniteVacuumSectorIndices
                w hw cutoff half →
              ∀ first,
                first ∈ centralBoundaryChannels cutoff half →
                  ∀ second,
                    second ∈ centralBoundaryChannels cutoff half →
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half left first *
                          centralPhysicalFiniteVacuumSectorGramAmplitude
                            w hw cutoff half right second ≤
                        (spread * spread) *
                          (centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half left second *
                            centralPhysicalFiniteVacuumSectorGramAmplitude
                              w hw cutoff half right first)) :
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
        w hw cutoff half source hsource ≤ quarter := by
  unfold centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
  apply finiteL1Distance_le_quarter_of_normalized_projective
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w hw cutoff half)
    spread
  · intro boundary hboundary
    exact centralPhysicalFiniteVacuumSectorBoundaryGivenSource_nonnegative_on
      hw hsource hboundary
  · intro boundary hboundary
    exact centralPhysicalFiniteVacuumSectorBoundaryPrior_nonnegative_on
      hw hboundary
  · exact centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one
      hsource
  · exact centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one
      w hw cutoff half
  · exact spreadSquare_le
  · let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
    let marginal :=
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half
    let rowMass := mass * marginal source
    exact projectiveSpreadBound_divPos_both
      (centralBoundaryChannels cutoff half)
      (finiteSourceChannelNumerator
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
        source)
      (finiteChannelPriorNumerator
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half))
      spread rowMass mass
      (Q'.mul_pos
        (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource))
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      (centralPhysicalFiniteVacuumSector_sourceRawProjective
        spread crossRatio source hsource)

/-! ## 4. Cofinal projective compiler -/

/-- One constructively cofinal half-amplitude cross-ratio field on the
canonical vacuum component.  Its fixed squared-spread ceiling is exactly the
remaining division-free finite analytic obligation on this route. -/
structure FixedNomeCofinalVacuumSectorHalfAmplitudeProjective
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  spread : Nat → Nat → Q'
  spreadSquare_le : ∀ base threshold,
    spread base threshold * spread base threshold ≤
      anchoredProjectiveCeiling
  halfAmplitudeCrossRatio : ∀ base threshold left,
    left ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      ∀ right,
        right ∈ centralPhysicalFiniteVacuumSectorIndices
            w hw (anchor base threshold) half →
          ∀ first,
            first ∈ centralBoundaryChannels (anchor base threshold) half →
              ∀ second,
                second ∈ centralBoundaryChannels
                    (anchor base threshold) half →
                  centralPhysicalFiniteVacuumSectorGramAmplitude
                        w hw (anchor base threshold) half left first *
                      centralPhysicalFiniteVacuumSectorGramAmplitude
                        w hw (anchor base threshold) half right second ≤
                    (spread base threshold * spread base threshold) *
                      (centralPhysicalFiniteVacuumSectorGramAmplitude
                          w hw (anchor base threshold) half left second *
                        centralPhysicalFiniteVacuumSectorGramAmplitude
                          w hw (anchor base threshold) half right first)

namespace FixedNomeCofinalVacuumSectorHalfAmplitudeProjective

/-- The cofinal division-free half-amplitude diameter gives both posterior
quarters. -/
def toPosteriorMixing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorHalfAmplitudeProjective
      w hw half) :
    FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing
      w hw half quarter quarter where
  targetRate_nonnegative := by decide
  sourceRate_nonnegative := by decide
  rateProduct_lt_one := by decide
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  targetPosteriorBound := by
    intro base threshold boundary hboundary channelTotal_pos
    exact
      centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_quarter_of_crossRatio
        hboundary channelTotal_pos
        (family.spread base threshold)
        (family.spreadSquare_le base threshold)
        (family.halfAmplitudeCrossRatio base threshold)
  sourcePosteriorBound := by
    intro base threshold source hsource
    exact
      centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_quarter_of_crossRatio
        hsource
        (family.spread base threshold)
        (family.spreadSquare_le base threshold)
        (family.halfAmplitudeCrossRatio base threshold)

/-- The same cofinal half-amplitude diameter reaches the completed
same-object vacuum-sector strict gap at the semantic rate `1/16`. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorHalfAmplitudeProjective
      w hw half) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (quarter * quarter) :=
  family.toPosteriorMixing.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorHalfAmplitudeProjective

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.projectiveSpreadBound_divPos_left
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.projectiveSpreadBound_divPos_both
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.centralPhysicalFiniteVacuumSector_targetRawProjective
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.centralPhysicalFiniteVacuumSector_sourceRawProjective
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_quarter_of_crossRatio
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_quarter_of_crossRatio
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProjective.FixedNomeCofinalVacuumSectorHalfAmplitudeProjective.toVacuumSectorCenteredStrictGap
