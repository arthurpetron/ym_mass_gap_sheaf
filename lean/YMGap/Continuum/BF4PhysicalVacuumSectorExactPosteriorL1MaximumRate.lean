/-
# The exact finite maximum posterior-L1 rate

The overlap residual is a convenient support-compatible upper bound, but it
need not be the smallest finite scalar controlling the actual physical Bayes
defects.  This module takes the located maxima of the two exact posterior
`L1` distances themselves and multiplies them.  The resulting scalar controls
the literal centered physical Gram, is never larger than the overlap residual,
and vanishes at cutoff one by the exact rank-one amplitude factorization.

A constructively cofinal upper bound below one for this sharper scalar is
sufficient for the completed same-object vacuum-sector gap.  No such bound is
inhabited here.  The cutoff-one zero is not extrapolated to growing cutoffs.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A located maximum seeded at zero -/

/-- Maximum of a finite rational family, with neutral value zero on the
empty list. -/
def finiteMaxZero {A : Type} (value : A → Q') : List A → Q'
  | [] => 0
  | head :: tail => Q'.max' (value head) (finiteMaxZero value tail)

theorem finiteMaxZero_nonnegative {A : Type}
    (value : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      (0 : Q') ≤ finiteMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

theorem le_finiteMaxZero_of_mem {A : Type}
    (value : A → Q') : ∀ (items : List A) {item : A},
    item ∈ items → value item ≤ finiteMaxZero value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.le_max'_left _ _
      · exact Q'.le_trans' _ _ _
          (le_finiteMaxZero_of_mem value tail htail)
          (Q'.le_max'_right _ _)

theorem finiteMaxZero_le {A : Type}
    (value : A → Q') (bound : Q') : ∀ items : List A,
    (0 : Q') ≤ bound →
    (∀ item, item ∈ items → value item ≤ bound) →
      finiteMaxZero value items ≤ bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hvalue => by
      unfold finiteMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hvalue head List.mem_cons_self,
          finiteMaxZero_le value bound tail hbound
            (fun item hitem =>
              hvalue item (List.mem_cons_of_mem head hitem))⟩

private theorem finiteMaxZero_eqv_zero_of_values {A : Type}
    (value : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → value item ≈ 0) →
      finiteMaxZero value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hvalue => by
      have hhead := hvalue head List.mem_cons_self
      have htail := finiteMaxZero_eqv_zero_of_values value tail
        (fun item hitem =>
          hvalue item (List.mem_cons_of_mem head hitem))
      unfold finiteMaxZero Q'.max'
      by_cases hle : value head ≤ finiteMaxZero value tail
      · rw [if_pos hle]
        exact htail
      · rw [if_neg hle]
        exact hhead

/-! ## 2. The two exact finite maxima -/

/-- The actual target-posterior distance on positive channels and zero on
irrelevant zero-total channels. -/
def centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  if htotal :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary then
    centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
      w hw cutoff half boundary htotal
  else 0

/-- The actual source-posterior distance on canonical indices and zero
outside the component. -/
def centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
      w hw cutoff half source hsource
  else 0

def centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteMaxZero
    (centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
      w hw cutoff half)
    (centralBoundaryChannels cutoff half)

def centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteMaxZero
    (centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

/-- The sharp finite product rate supplied by the actual two Bayes `L1`
defects. -/
def centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
      w hw cutoff half *
    centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
      w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
  apply finiteMaxZero_nonnegative
  intro boundary _
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
  by_cases htotal :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary
  · rw [dif_pos htotal]
    exact finiteL1Distance_nonnegative _ _ _
  · rw [dif_neg htotal]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
  apply finiteMaxZero_nonnegative
  intro source _
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
  by_cases hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · rw [dif_pos hsource]
    exact finiteL1Distance_nonnegative _ _ _
  · rw [dif_neg hsource]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_nonnegative
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_nonnegative
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_maximum
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half)
    (channelTotal_pos :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
        w hw cutoff half boundary channelTotal_pos ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
        w hw cutoff half := by
  have hmax := le_finiteMaxZero_of_mem
    (centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
      w hw cutoff half)
    (centralBoundaryChannels cutoff half) hboundary
  simpa [centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum,
    centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero,
    channelTotal_pos] using hmax

theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_maximum
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
        w hw cutoff half source hsource ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w hw cutoff half := by
  have hmax := le_finiteMaxZero_of_mem
    (centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) hsource
  simpa [centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum,
    centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero,
    hsource] using hmax

/-! ## 3. Direct centered-Gram control and cofinal compiler -/

theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactPosteriorL1MaximumRate_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source ≤
      centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
          w hw cutoff half *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
  exact
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight
      (centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_nonnegative
        w hw cutoff half)
      (fun boundary hboundary =>
        centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_of_posteriorL1
          (centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_nonnegative
            w hw cutoff half)
          (fun channelTotal_pos =>
            centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_maximum
              hboundary channelTotal_pos))
      (centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_of_posteriorL1
        hsource
        (centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_maximum
          hsource))

/-- A cofinal upper bound below one for the sharp exact product scalar. -/
structure FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  exactRateBound : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w hw (anchor base threshold) half ≤ rate

namespace FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound

def toCenteredGramMajorant
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  majorantBound := by
    intro base threshold source hsource
    refine Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactPosteriorL1MaximumRate_mul_weight
        hsource) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (family.exactRateBound base threshold)
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toCenteredGramMajorant.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound

/-! ## 4. The sharp rate is below the overlap residual -/

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_le_overlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
  apply finiteMaxZero_le
  · exact
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
        w hw cutoff half
  intro boundary hboundary
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
  by_cases htotal :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary
  · rw [dif_pos htotal]
    exact
      centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_overlapResidualRate
        hboundary htotal
  · rw [dif_neg htotal]
    exact
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
        w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_le_overlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
  apply finiteMaxZero_le
  · exact
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_nonnegative
        w hw cutoff half
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
  rw [dif_pos hsource]
  exact
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_overlapResidualRate
      hsource

theorem centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_le_overlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
    centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
  refine Q'.le_trans' _
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
        w hw cutoff half *
      centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w hw cutoff half) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_le_overlapResidualRate
        w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_nonnegative
        w hw cutoff half)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_le_overlapResidualRate
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
      w hw cutoff half)

/-! ## 5. Exact cutoff-one value -/

private theorem finiteL1Distance_eqv_zero_of_pointwise_eqv
    {A : Type} (items : List A) (left right : A → Q')
    (hpoint : ∀ item, item ∈ items → left item ≈ right item) :
    YMGap.Continuum.BF4PhysicalBoundaryPosterior.finiteL1Distance
        items left right ≈ 0 := by
  unfold YMGap.Continuum.BF4PhysicalBoundaryPosterior.finiteL1Distance
  refine Q'.eqv_trans _
    (listQSum (fun _ : A => (0 : Q')) items) _ ?_ ?_
  · apply listQSum_congr_on
    intro item hitem
    have hzero : left item + (-right item) ≈ 0 :=
      Q'.eqv_trans _ (right item + (-right item)) _
        (Q'.add_eqv_congr_right _ _ _ (hpoint item hitem))
        (Q'.add_neg_self_eqv (right item))
    refine Q'.eqv_trans _ (Q'.abs (0 : Q')) _
      (Q'.abs_eqv_congr hzero) ?_
    exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (Q'.le_refl' 0)
  exact listQSum_zero items

private theorem centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
        w (Q'.le_of_lt hw) 1 0 boundary ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero
  by_cases htotal :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary
  · rw [dif_pos htotal]
    unfold centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
    exact finiteL1Distance_eqv_zero_of_pointwise_eqv _ _ _
      (fun index hindex =>
        centralPhysicalFiniteVacuumSectorTargetGivenBoundary_cutoffOne_eqv_stationary
          hw hboundary htotal hindex)
  · rw [dif_neg htotal]
    exact Q'.eqv_refl 0

private theorem centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
        w (Q'.le_of_lt hw) 1 0 source ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero
  rw [dif_pos hsource]
  unfold centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
  exact finiteL1Distance_eqv_zero_of_pointwise_eqv _ _ _
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorBoundaryGivenSource_cutoffOne_eqv_prior
        hw hsource hboundary)

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum
  exact finiteMaxZero_eqv_zero_of_values _ _
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorTargetPosteriorL1OrZero_cutoffOne_eqv_zero
        hw hboundary)

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
  exact finiteMaxZero_eqv_zero_of_values _ _
    (fun source hsource =>
      centralPhysicalFiniteVacuumSectorSourcePosteriorL1OrZero_cutoffOne_eqv_zero
        hw hsource)

theorem centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate
  refine Q'.eqv_trans _
    ((0 : Q') *
      centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum
        w (Q'.le_of_lt hw) 1 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_cutoffOne_eqv_zero
        hw)
  refine Q'.eqv_trans _ ((0 : Q') * 0) _
    (Q'.mul_eqv_congr_left 0 _ _
      (centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_cutoffOne_eqv_zero
        hw)) (Q'.zero_mul_eqv 0)

end YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.finiteMaxZero_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactPosteriorL1MaximumRate_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_le_overlapResidualRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_cutoffOne_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_cutoffOne_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_cutoffOne_eqv_zero
