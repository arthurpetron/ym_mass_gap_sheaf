/-
# Exact finite minima for BF4 vacuum-sector posterior overlap

Both physical posterior overlaps are positive at each fixed cutoff.  This
module contracts the finitely many pointwise obligations into two exact
scalars.  A capped finite minimum starts from one and folds `Q'.min'` over the
literal carrier.  Zero-total target channels and indices outside the sector
are assigned the neutral value one; on the relevant carriers the conditional
overlaps are used.

The resulting target and source floors lie in `(0,1]` and bound every relevant
posterior overlap at that cutoff.  A cofinal persistence structure now needs
only bound these two scalar floors uniformly.  It compiles through the prior
overlap theorem to the completed same-object sector gap.

No persistence estimate is inhabited here.  In particular, fixed-cutoff
positivity does not prevent the exact minima from tending to zero.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_min_pos {left right : Q'}
    (left_pos : (0 : Q') < left)
    (right_pos : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases hle : left ≤ right
  · rw [if_pos hle]
    exact left_pos
  · rw [if_neg hle]
    exact right_pos

/-! ## 1. Generic capped finite minimum -/

/-- Fold a finite family by `min`, capped above by one even on the empty
list. -/
def finiteCappedMinimum {A : Type}
    (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => Q'.min' (value head) (finiteCappedMinimum value tail)

/-- A finite capped minimum of positive entries is positive. -/
theorem finiteCappedMinimum_pos {A : Type}
    (value : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') < value item) →
      (0 : Q') < finiteCappedMinimum value items
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hpos =>
      q_min_pos
        (hpos head List.mem_cons_self)
        (finiteCappedMinimum_pos value tail
          (fun item hitem =>
            hpos item (List.mem_cons_of_mem head hitem)))

/-- The capped finite minimum never exceeds one. -/
theorem finiteCappedMinimum_le_one {A : Type}
    (value : A → Q') : ∀ items : List A,
      finiteCappedMinimum value items ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | _ :: tail =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (finiteCappedMinimum_le_one value tail)

/-- The capped finite minimum bounds every listed entry. -/
theorem finiteCappedMinimum_le_member {A : Type}
    (value : A → Q') : ∀ (items : List A) {item : A},
      item ∈ items → finiteCappedMinimum value items ≤ value item
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.min_le_left' _ _
      · exact Q'.le_trans' _ _ _
          (Q'.min_le_right' _ _)
          (finiteCappedMinimum_le_member value tail htail)

/-! ## 2. Total functions whose relevant values are actual overlaps -/

/-- Target posterior overlap on positive channels and one on irrelevant
zero-total channels. -/
def centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  if htotal :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary then
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
      w hw cutoff half boundary htotal
  else 1

/-- Source posterior overlap on canonical sector indices and one elsewhere. -/
def centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
      w hw cutoff half source hsource
  else 1

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne
        w hw cutoff half boundary := by
  by_cases htotal :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary
  · simpa [centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne,
      htotal] using
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_pos htotal)
  · simp [centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne,
      htotal]
    exact (by decide : (0 : Q') < 1)

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne
        w hw cutoff half source := by
  by_cases hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · simpa [centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne,
      hsource] using
      (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_pos hsource)
  · simp [centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne,
      hsource]
    exact (by decide : (0 : Q') < 1)

/-! ## 3. The two exact fixed-cutoff floors -/

/-- Exact target overlap floor over the literal boundary carrier. -/
def centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteCappedMinimum
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne
      w hw cutoff half)
    (centralBoundaryChannels cutoff half)

/-- Exact source overlap floor over the literal canonical-sector index list. -/
def centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteCappedMinimum
    (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
  exact finiteCappedMinimum_pos _ _
    (fun boundary _ =>
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne_pos
        w hw cutoff half boundary)

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
  exact finiteCappedMinimum_pos _ _
    (fun source _ =>
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne_pos
        w hw cutoff half source)

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w hw cutoff half ≤ (1 : Q') :=
  finiteCappedMinimum_le_one _ _

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w hw cutoff half ≤ (1 : Q') :=
  finiteCappedMinimum_le_one _ _

/-- The target floor bounds every relevant positive-channel overlap. -/
theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
        w hw cutoff half boundary channelTotal_pos := by
  have hfloor := finiteCappedMinimum_le_member
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne
      w hw cutoff half)
    (centralBoundaryChannels cutoff half) hboundary
  simpa [centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor,
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne,
    channelTotal_pos] using hfloor

/-- The source floor bounds every canonical-sector source overlap. -/
theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
        w hw cutoff half source hsource := by
  have hfloor := finiteCappedMinimum_le_member
    (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) hsource
  simpa [centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor,
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne,
    hsource] using hfloor

/-! ## 4. Cofinal persistence of two scalars is sufficient -/

/-- Uniform persistence of the exact finite target/source floors.  This is a
strictly smaller analytic interface than pointwise posterior estimates. -/
structure FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (targetFloor sourceFloor : Q') : Type 1 where
  targetFloor_nonnegative : (0 : Q') ≤ targetFloor
  sourceFloor_nonnegative : (0 : Q') ≤ sourceFloor
  targetFloor_le_one : targetFloor ≤ (1 : Q')
  sourceFloor_le_one : sourceFloor ≤ (1 : Q')
  residualRateProduct_lt_one :
    ((2 : Q') * (1 + (-targetFloor))) *
        ((2 : Q') * (1 + (-sourceFloor))) < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  targetFloorBound : ∀ base threshold,
    targetFloor ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w hw (anchor base threshold) half
  sourceFloorBound : ∀ base threshold,
    sourceFloor ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w hw (anchor base threshold) half

namespace FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence

/-- Scalar finite-floor persistence produces the pointwise overlap
certificate. -/
def toPosteriorOverlap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetFloor sourceFloor : Q'}
    (family :
      FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence
        w hw half targetFloor sourceFloor) :
    FixedNomeCofinalVacuumSectorPosteriorOverlap
      w hw half targetFloor sourceFloor where
  targetOverlapFloor_nonnegative := family.targetFloor_nonnegative
  sourceOverlapFloor_nonnegative := family.sourceFloor_nonnegative
  targetOverlapFloor_le_one := family.targetFloor_le_one
  sourceOverlapFloor_le_one := family.sourceFloor_le_one
  residualRateProduct_lt_one := family.residualRateProduct_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  targetOverlapBound := by
    intro base threshold boundary hboundary channelTotal_pos
    exact Q'.le_trans' _ _ _
      (family.targetFloorBound base threshold)
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le
        hboundary channelTotal_pos)
  sourceOverlapBound := by
    intro base threshold source hsource
    exact Q'.le_trans' _ _ _
      (family.sourceFloorBound base threshold)
      (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le
        hsource)

/-- Cofinal persistence of the two exact finite minima reaches the completed
same-object vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetFloor sourceFloor : Q'}
    (family :
      FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence
        w hw half targetFloor sourceFloor) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half
      (((2 : Q') * (1 + (-targetFloor))) *
        ((2 : Q') * (1 + (-sourceFloor)))) :=
  family.toPosteriorOverlap.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.finiteCappedMinimum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.finiteCappedMinimum_le_member
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor.FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence.toVacuumSectorCenteredStrictGap
