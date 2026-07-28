/-
# Executable finite heat windows on the matched BF4 trajectory

The direct pointwise-heat interface previously asked for a
`PointwiseHeatTailWindow` at every local BF4 coordinate.  For a finite
retained carrier this is unnecessarily opaque: one can evaluate the same
spacing-shifted prefix and closed tail at every retained class coordinate,
take their rational minimum and maximum, and obtain every local window from
the single finite-list membership proof.

This file implements that reduction.  At scale `s` its two endpoints are
literally folds of

    spacingPointwiseHeatPartial
      (blockedWeight family (coupling s)) x (depth s)
      plus-or-minus spacingClosedTail
      (blockedWeight family (coupling s)) (depth s).

Thus the nome is definitionally the exact observable- or exponent-Gram
matched BF4 output.  There is no auxiliary Padé nome in the window
calculation.  The Padé nome appears only in the already-existing dyadic
same-action bridge, where it proves `blockedWeight < 1`.

The final constructor removes the old pointwise `local_window` assumption.
Its remaining analytic obligations are the two scale-wise executable
rational checks that the finite minimum is positive and the finite maximum
fits under the spacing-cutoff cap.  Its geometric obligation is explicit:
the supplied physical class-coordinate map must land in the displayed
finite retained list.

No claim is made here that the present BF4 block structures already supply
that physical class-coordinate map or its exhaustive finite enumeration.
That identification is the remaining Yang--Mills-specific leaf.

## Constructivity

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory

namespace YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow

open YMGap.Constructive
open YMGap.Continuum.BF4FarautAFCutoffGrowth
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive extrema of a nonempty finite coordinate list -/

/-- A retained list with its nonemptiness carried by construction. -/
structure FiniteClassCoordinateCarrier : Type where
  first : Q'
  rest : List Q'

namespace FiniteClassCoordinateCarrier

/-- The explicit list represented by a nonempty carrier. -/
def coordinates (carrier : FiniteClassCoordinateCarrier) : List Q' :=
  carrier.first :: carrier.rest

theorem first_mem (carrier : FiniteClassCoordinateCarrier) :
    carrier.first ∈ carrier.coordinates :=
  List.mem_cons.mpr (Or.inl rfl)

end FiniteClassCoordinateCarrier

/-- Minimum of `value` over the displayed nonempty list `first :: rest`. -/
def finiteMin
    {α : Type} (value : α → Q') : α → List α → Q'
  | first, [] => value first
  | first, next :: rest =>
      Q'.min' (value first) (finiteMin value next rest)

/-- Maximum of `value` over the displayed nonempty list `first :: rest`. -/
def finiteMax
    {α : Type} (value : α → Q') : α → List α → Q'
  | first, [] => value first
  | first, next :: rest =>
      Q'.max' (value first) (finiteMax value next rest)

/-- The finite minimum is below every explicitly retained value. -/
theorem finiteMin_le_of_mem
    {α : Type} (value : α → Q') :
    ∀ first rest item,
      item ∈ first :: rest →
        finiteMin value first rest ≤ value item
  | first, [], item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.le_refl' _
      · nomatch htail
  | first, next :: rest, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.min_le_left' _ _
      · exact Q'.le_trans' _ _ _
          (Q'.min_le_right' _ _)
          (finiteMin_le_of_mem value next rest item htail)

/-- Every explicitly retained value is below the finite maximum. -/
theorem le_finiteMax_of_mem
    {α : Type} (value : α → Q') :
    ∀ first rest item,
      item ∈ first :: rest →
        value item ≤ finiteMax value first rest
  | first, [], item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.le_refl' _
      · nomatch htail
  | first, next :: rest, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.le_max'_left _ _
      · exact Q'.le_trans' _ _ _
          (le_finiteMax_of_mem value next rest item htail)
          (Q'.le_max'_right _ _)

/-! ## 2. Exact prefix/tail endpoint functions -/

/-- The computable lower endpoint furnished by one shifted prefix. -/
def prefixLowerEndpoint
    (w x : Q') (depth : Nat) : Q' :=
  spacingPointwiseHeatPartial w x depth +
    -spacingClosedTail w depth

/-- The computable upper endpoint furnished by the same shifted prefix. -/
def prefixUpperEndpoint
    (w x : Q') (depth : Nat) : Q' :=
  spacingPointwiseHeatPartial w x depth +
    spacingClosedTail w depth

/-- A prefix-minus-tail endpoint never exceeds its matching
prefix-plus-tail endpoint. -/
theorem prefixLowerEndpoint_le_prefixUpperEndpoint
    {w : Q'} (hw0 : (0 : Q') < w)
    (x : Q') (depth : Nat) :
    prefixLowerEndpoint w x depth ≤
      prefixUpperEndpoint w x depth := by
  have htail :
      (0 : Q') ≤ spacingClosedTail w depth :=
    spacingClosedTail_nonnegative hw0 depth
  have hnegative :
      -spacingClosedTail w depth ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg htail
  exact Q'.add_le_add_left
    (spacingPointwiseHeatPartial w x depth)
    (-spacingClosedTail w depth)
    (spacingClosedTail w depth)
    (Q'.le_trans' _ _ _ hnegative htail)

/-- Common finite lower endpoint on a nonempty retained carrier. -/
def finitePrefixLower
    (w : Q') (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier) : Q' :=
  finiteMin
    (fun x => prefixLowerEndpoint w x depth)
    carrier.first carrier.rest

/-- Common finite upper endpoint on a nonempty retained carrier. -/
def finitePrefixUpper
    (w : Q') (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier) : Q' :=
  finiteMax
    (fun x => prefixUpperEndpoint w x depth)
    carrier.first carrier.rest

/-- Membership alone produces the common finite lower bound. -/
theorem finitePrefixLower_le_of_mem
    (w : Q') (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier)
    (x : Q') (hx : x ∈ carrier.coordinates) :
    finitePrefixLower w depth carrier ≤
      prefixLowerEndpoint w x depth :=
  finiteMin_le_of_mem
    (fun coordinate =>
      prefixLowerEndpoint w coordinate depth)
    carrier.first carrier.rest x hx

/-- Membership alone produces the common finite upper bound. -/
theorem le_finitePrefixUpper_of_mem
    (w : Q') (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier)
    (x : Q') (hx : x ∈ carrier.coordinates) :
    prefixUpperEndpoint w x depth ≤
      finitePrefixUpper w depth carrier :=
  le_finiteMax_of_mem
    (fun coordinate =>
      prefixUpperEndpoint w coordinate depth)
    carrier.first carrier.rest x hx

/-- The two folded endpoints remain ordered.  Nonemptiness is essential and
is witnessed by `carrier.first`. -/
theorem finitePrefixLower_le_finitePrefixUpper
    {w : Q'} (hw0 : (0 : Q') < w)
    (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier) :
    finitePrefixLower w depth carrier ≤
      finitePrefixUpper w depth carrier := by
  exact Q'.le_trans' _ _ _
    (finitePrefixLower_le_of_mem
      w depth carrier carrier.first carrier.first_mem)
    (Q'.le_trans' _ _ _
      (prefixLowerEndpoint_le_prefixUpperEndpoint
        hw0 carrier.first depth)
      (le_finitePrefixUpper_of_mem
        w depth carrier carrier.first carrier.first_mem))

/-- The finite folds themselves construct the local tail-window certificate;
there are no local analytic inequalities left to supply. -/
def finitePointwiseHeatTailWindow
    (w : Q') (depth : Nat)
    (carrier : FiniteClassCoordinateCarrier)
    (x : Q') (hx : x ∈ carrier.coordinates) :
    PointwiseHeatTailWindow
      w x
      (finitePrefixLower w depth carrier)
      (finitePrefixUpper w depth carrier) where
  M := depth
  lower_le_prefix_sub_tail :=
    finitePrefixLower_le_of_mem
      w depth carrier x hx
  prefix_add_tail_le_upper :=
    le_finitePrefixUpper_of_mem
      w depth carrier x hx

/-! ## 3. Explicit finite physical locations and their class coordinates -/

/-- A nonempty, explicit retained list of physical locations.  The type
`Local` is intentionally generic: in the BF4 consumer it can be the complete
source/target/path/factor tuple rather than merely its rational class
coordinate. -/
structure FinitePhysicalLocationCarrier (Local : Type) : Type where
  first : Local
  rest : List Local

namespace FinitePhysicalLocationCarrier

/-- The explicit retained physical-location list. -/
def locations {Local : Type}
    (carrier : FinitePhysicalLocationCarrier Local) : List Local :=
  carrier.first :: carrier.rest

theorem first_mem {Local : Type}
    (carrier : FinitePhysicalLocationCarrier Local) :
    carrier.first ∈ carrier.locations :=
  List.mem_cons.mpr (Or.inl rfl)

/-- The exact finite image of the retained physical locations under a class
coordinate map. -/
def classCoordinates {Local : Type}
    (carrier : FinitePhysicalLocationCarrier Local)
    (x : Local → Q') : FiniteClassCoordinateCarrier where
  first := x carrier.first
  rest := carrier.rest.map x

end FinitePhysicalLocationCarrier

/-- A physical location together with its constructive membership in one
fixed retained list.  Taking this as the downstream `Local` type eliminates
even the exhaustiveness field: every local value carries its membership. -/
structure RetainedPhysicalLocation
    {Local : Type}
    (carrier : FinitePhysicalLocationCarrier Local) : Type where
  value : Local
  retained : value ∈ carrier.locations

/-- Lift a raw scale-dependent class-coordinate map to the retained-location
subtype. -/
def retainedClassCoordinate
    {Local : Type}
    {carrier : FinitePhysicalLocationCarrier Local}
    (x : Nat → Local → Q') :
    Nat → RetainedPhysicalLocation carrier → Q' :=
  fun scale location => x scale location.value

/-- Common lower endpoint obtained by evaluating the actual class-coordinate
map on every displayed physical location. -/
def finitePhysicalPrefixLower
    {Local : Type}
    (w : Q') (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local) : Q' :=
  finiteMin
    (fun location =>
      prefixLowerEndpoint w (x location) depth)
    carrier.first carrier.rest

/-- Common upper endpoint obtained from the same physical-location list. -/
def finitePhysicalPrefixUpper
    {Local : Type}
    (w : Q') (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local) : Q' :=
  finiteMax
    (fun location =>
      prefixUpperEndpoint w (x location) depth)
    carrier.first carrier.rest

theorem finitePhysicalPrefixLower_le_of_mem
    {Local : Type}
    (w : Q') (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local)
    (location : Local)
    (hlocation : location ∈ carrier.locations) :
    finitePhysicalPrefixLower w x depth carrier ≤
      prefixLowerEndpoint w (x location) depth :=
  finiteMin_le_of_mem
    (fun retained =>
      prefixLowerEndpoint w (x retained) depth)
    carrier.first carrier.rest location hlocation

theorem le_finitePhysicalPrefixUpper_of_mem
    {Local : Type}
    (w : Q') (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local)
    (location : Local)
    (hlocation : location ∈ carrier.locations) :
    prefixUpperEndpoint w (x location) depth ≤
      finitePhysicalPrefixUpper w x depth carrier :=
  le_finiteMax_of_mem
    (fun retained =>
      prefixUpperEndpoint w (x retained) depth)
    carrier.first carrier.rest location hlocation

theorem finitePhysicalPrefixLower_le_finitePhysicalPrefixUpper
    {Local : Type} {w : Q'} (hw0 : (0 : Q') < w)
    (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local) :
    finitePhysicalPrefixLower w x depth carrier ≤
      finitePhysicalPrefixUpper w x depth carrier := by
  exact Q'.le_trans' _ _ _
    (finitePhysicalPrefixLower_le_of_mem
      w x depth carrier carrier.first carrier.first_mem)
    (Q'.le_trans' _ _ _
      (prefixLowerEndpoint_le_prefixUpperEndpoint
        hw0 (x carrier.first) depth)
      (le_finitePhysicalPrefixUpper_of_mem
        w x depth carrier carrier.first carrier.first_mem))

/-- One retained physical-location membership proof constructs the local
window at its exact class coordinate. -/
def finitePhysicalPointwiseHeatTailWindow
    {Local : Type}
    (w : Q') (x : Local → Q') (depth : Nat)
    (carrier : FinitePhysicalLocationCarrier Local)
    (location : Local)
    (hlocation : location ∈ carrier.locations) :
    PointwiseHeatTailWindow
      w (x location)
      (finitePhysicalPrefixLower w x depth carrier)
      (finitePhysicalPrefixUpper w x depth carrier) where
  M := depth
  lower_le_prefix_sub_tail :=
    finitePhysicalPrefixLower_le_of_mem
      w x depth carrier location hlocation
  prefix_add_tail_le_upper :=
    le_finitePhysicalPrefixUpper_of_mem
      w x depth carrier location hlocation

/-! ## 4. Definitional specialization to the matched BF4 output -/

/-- The common lower endpoint evaluated at the exact matched blocked nome. -/
def matchedFinitePrefixLower
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FiniteClassCoordinateCarrier)
    (scale : Nat) : Q' :=
  finitePrefixLower
    (blockedWeight family (coupling scale))
    (depth scale) (carrier scale)

/-- The common upper endpoint evaluated at the exact matched blocked nome. -/
def matchedFinitePrefixUpper
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FiniteClassCoordinateCarrier)
    (scale : Nat) : Q' :=
  finitePrefixUpper
    (blockedWeight family (coupling scale))
    (depth scale) (carrier scale)

/-- One physical-coordinate membership proof constructs its exact matched
pointwise tail window. -/
def matchedFinitePointwiseHeatTailWindow
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FiniteClassCoordinateCarrier)
    (scale : Nat) (x : Q')
    (hx : x ∈ (carrier scale).coordinates) :
    PointwiseHeatTailWindow
      (blockedWeight family (coupling scale)) x
      (matchedFinitePrefixLower
        family coupling depth carrier scale)
      (matchedFinitePrefixUpper
        family coupling depth carrier scale) :=
  finitePointwiseHeatTailWindow
    (blockedWeight family (coupling scale))
    (depth scale) (carrier scale) x hx

/-- Finite lower endpoint obtained from an explicit physical-location list
and the exact scale-dependent class-coordinate map. -/
def matchedFinitePhysicalPrefixLower
    {Local : Type}
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FinitePhysicalLocationCarrier Local)
    (scale : Nat) : Q' :=
  finitePhysicalPrefixLower
    (blockedWeight family (coupling scale))
    (x scale) (depth scale) (carrier scale)

/-- Matching finite upper endpoint on the same physical locations. -/
def matchedFinitePhysicalPrefixUpper
    {Local : Type}
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FinitePhysicalLocationCarrier Local)
    (scale : Nat) : Q' :=
  finitePhysicalPrefixUpper
    (blockedWeight family (coupling scale))
    (x scale) (depth scale) (carrier scale)

/-- Exact matched local window obtained from membership in the retained
physical-location list. -/
def matchedFinitePhysicalPointwiseHeatTailWindow
    {Local : Type}
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FinitePhysicalLocationCarrier Local)
    (scale : Nat) (location : Local)
    (hlocation :
      location ∈ (carrier scale).locations) :
    PointwiseHeatTailWindow
      (blockedWeight family (coupling scale))
      (x scale location)
      (matchedFinitePhysicalPrefixLower
        family coupling x depth carrier scale)
      (matchedFinitePhysicalPrefixUpper
        family coupling x depth carrier scale) :=
  finitePhysicalPointwiseHeatTailWindow
    (blockedWeight family (coupling scale))
    (x scale) (depth scale) (carrier scale)
    location hlocation

/-! ## 5. The dyadic bridge supplies the upper nome inequality -/

/-- The explicit dyadic Padé nome is strictly below one at every scale. -/
theorem dyadicPadeNome_lt_one (scale : Nat) :
    dyadicPadeNome scale < (1 : Q') := by
  show
    (dyadicPadeNome scale).num * ((1 : Q').den : Int) <
      (1 : Q').num * ((dyadicPadeNome scale).den : Int)
  rw [dyadicPadeNome_num, dyadicPadeNome_den]
  have honeNum : (1 : Q').num = 1 := rfl
  have honeDen : ((1 : Q').den : Int) = 1 := rfl
  rw [honeNum, honeDen, Int.mul_one, Int.one_mul]
  rw [Int.ofNat_eq_natCast]
  omega

/-- On the physical matched trajectory, `blockedWeight < 1` follows from the
same-action bridge rather than surviving as an independent assumption. -/
theorem matchedPhysicalWeight_lt_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) :
    blockedWeight family (coupling scale) < (1 : Q') := by
  have hnome := bridge.nome scale
  change
    blockedWeight family (coupling scale) ≈
      dyadicPadeNome scale at hnome
  exact Q'.lt_of_le_of_lt
    (Q'.le_of_eqv hnome)
    (dyadicPadeNome_lt_one scale)

/-! ## 6. Finite-carrier constructors for the full same-action window -/

/-- Exact remaining data after finite aggregation.

`coordinate_mem` is geometric: it says the actual physical coordinate map
is exhausted by the explicit retained list.  The last two fields are
scale-wise rational statements about finite expressions, hence can be
proved by `decide` after a concrete trajectory and carrier are supplied.
There is deliberately no pointwise heat-window field. -/
structure MatchedFiniteHeatWindowCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (Local : Type)
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FiniteClassCoordinateCarrier) : Type where
  bridge :
    MatchedDyadicSameActionAFBridge
      family law spacing coupling
  coordinate_mem :
    ∀ scale location,
      x scale location ∈ (carrier scale).coordinates
  finite_lower_pos :
    ∀ scale,
      (0 : Q') <
        matchedFinitePrefixLower
          family coupling depth carrier scale
  finite_upper_le_cutoff_cap :
    ∀ scale,
      matchedFinitePrefixUpper
          family coupling depth carrier scale ≤
        FiveHolonomyPerronCutoff.four ^
            matchedPhysicalSpacingBits
              family coupling scale *
          matchedFinitePrefixLower
            family coupling depth carrier scale

/-- A finite matched certificate inhabits the original same-action window
interface.  Positivity of the nome comes from the exact BF4 argmin;
`w < 1` comes from the dyadic same-action bridge; upper nonnegativity follows
from positivity of the folded lower endpoint and the intrinsic endpoint
order. -/
def MatchedFiniteHeatWindowCertificate.toPointwiseHeatWindows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {Local : Type}
    {x : Nat → Local → Q'}
    {depth : Nat → Nat}
    {carrier : Nat → FiniteClassCoordinateCarrier}
    (certificate :
      MatchedFiniteHeatWindowCertificate
        family law spacing coupling
        Local x depth carrier) :
    MatchedPhysicalPointwiseHeatWindows
      family law spacing coupling Local x
      (matchedFinitePrefixLower
        family coupling depth carrier)
      (matchedFinitePrefixUpper
        family coupling depth carrier) where
  bridge := certificate.bridge
  weight_pos := fun scale =>
    blockedWeight_pos family (coupling scale)
  weight_lt_one := fun scale =>
    matchedPhysicalWeight_lt_one
      certificate.bridge scale
  lower_pos := certificate.finite_lower_pos
  upper_nonnegative := by
    intro scale
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt (certificate.finite_lower_pos scale))
      (finitePrefixLower_le_finitePrefixUpper
        (blockedWeight_pos family (coupling scale))
        (depth scale) (carrier scale))
  upper_le_cutoff_cap :=
    certificate.finite_upper_le_cutoff_cap
  local_window := by
    intro scale location
    exact matchedFinitePointwiseHeatTailWindow
      family coupling depth carrier scale
      (x scale location)
      (certificate.coordinate_mem scale location)

/-- Stronger physical-location form of the finite certificate.  The folds
are taken over the displayed list of `Local` values themselves; `x` is
applied internally, so the aggregation is definitionally the image of the
retained physical carrier rather than a freely supplied coordinate list. -/
structure MatchedFinitePhysicalHeatWindowCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (Local : Type)
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : Nat → FinitePhysicalLocationCarrier Local) : Type where
  bridge :
    MatchedDyadicSameActionAFBridge
      family law spacing coupling
  retained_location_mem :
    ∀ scale location,
      location ∈ (carrier scale).locations
  finite_lower_pos :
    ∀ scale,
      (0 : Q') <
        matchedFinitePhysicalPrefixLower
          family coupling x depth carrier scale
  finite_upper_le_cutoff_cap :
    ∀ scale,
      matchedFinitePhysicalPrefixUpper
          family coupling x depth carrier scale ≤
        FiveHolonomyPerronCutoff.four ^
            matchedPhysicalSpacingBits
              family coupling scale *
          matchedFinitePhysicalPrefixLower
            family coupling x depth carrier scale

/-- The physical-location certificate eliminates the pointwise window field
by a literal finite fold over retained physical locations. -/
def MatchedFinitePhysicalHeatWindowCertificate.toPointwiseHeatWindows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {Local : Type}
    {x : Nat → Local → Q'}
    {depth : Nat → Nat}
    {carrier : Nat → FinitePhysicalLocationCarrier Local}
    (certificate :
      MatchedFinitePhysicalHeatWindowCertificate
        family law spacing coupling
        Local x depth carrier) :
    MatchedPhysicalPointwiseHeatWindows
      family law spacing coupling Local x
      (matchedFinitePhysicalPrefixLower
        family coupling x depth carrier)
      (matchedFinitePhysicalPrefixUpper
        family coupling x depth carrier) where
  bridge := certificate.bridge
  weight_pos := fun scale =>
    blockedWeight_pos family (coupling scale)
  weight_lt_one := fun scale =>
    matchedPhysicalWeight_lt_one
      certificate.bridge scale
  lower_pos := certificate.finite_lower_pos
  upper_nonnegative := by
    intro scale
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt
        (certificate.finite_lower_pos scale))
      (finitePhysicalPrefixLower_le_finitePhysicalPrefixUpper
        (blockedWeight_pos family (coupling scale))
        (x scale) (depth scale) (carrier scale))
  upper_le_cutoff_cap :=
    certificate.finite_upper_le_cutoff_cap
  local_window := by
    intro scale location
    exact matchedFinitePhysicalPointwiseHeatTailWindow
      family coupling x depth carrier scale location
      (certificate.retained_location_mem scale location)

/-- The strongest fixed-carrier form: the downstream local type is the
subtype of a single explicit retained physical-location list.  Hence only
the two rational finite-fold inequalities remain in addition to the
already-required dyadic trajectory bridge. -/
structure MatchedFixedFinitePhysicalHeatWindowCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (Local : Type)
    (x : Nat → Local → Q')
    (depth : Nat → Nat)
    (carrier : FinitePhysicalLocationCarrier Local) : Type where
  bridge :
    MatchedDyadicSameActionAFBridge
      family law spacing coupling
  finite_lower_pos :
    ∀ scale,
      (0 : Q') <
        matchedFinitePhysicalPrefixLower
          family coupling x depth
          (fun _ => carrier) scale
  finite_upper_le_cutoff_cap :
    ∀ scale,
      matchedFinitePhysicalPrefixUpper
          family coupling x depth
          (fun _ => carrier) scale ≤
        FiveHolonomyPerronCutoff.four ^
            matchedPhysicalSpacingBits
              family coupling scale *
          matchedFinitePhysicalPrefixLower
            family coupling x depth
            (fun _ => carrier) scale

/-- A fixed explicit retained carrier produces the original same-action
window family with no local or coordinate-coverage hypothesis. -/
def MatchedFixedFinitePhysicalHeatWindowCertificate.toPointwiseHeatWindows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {Local : Type}
    {x : Nat → Local → Q'}
    {depth : Nat → Nat}
    {carrier : FinitePhysicalLocationCarrier Local}
    (certificate :
      MatchedFixedFinitePhysicalHeatWindowCertificate
        family law spacing coupling
        Local x depth carrier) :
    MatchedPhysicalPointwiseHeatWindows
      family law spacing coupling
      (RetainedPhysicalLocation carrier)
      (retainedClassCoordinate x)
      (matchedFinitePhysicalPrefixLower
        family coupling x depth (fun _ => carrier))
      (matchedFinitePhysicalPrefixUpper
        family coupling x depth (fun _ => carrier)) where
  bridge := certificate.bridge
  weight_pos := fun scale =>
    blockedWeight_pos family (coupling scale)
  weight_lt_one := fun scale =>
    matchedPhysicalWeight_lt_one
      certificate.bridge scale
  lower_pos := certificate.finite_lower_pos
  upper_nonnegative := by
    intro scale
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt
        (certificate.finite_lower_pos scale))
      (finitePhysicalPrefixLower_le_finitePhysicalPrefixUpper
        (blockedWeight_pos family (coupling scale))
        (x scale) (depth scale) carrier)
  upper_le_cutoff_cap :=
    certificate.finite_upper_le_cutoff_cap
  local_window := by
    intro scale location
    exact finitePhysicalPointwiseHeatTailWindow
      (blockedWeight family (coupling scale))
      (x scale) (depth scale) carrier
      location.value location.retained

#print axioms FiniteClassCoordinateCarrier.coordinates
#print axioms FinitePhysicalLocationCarrier.classCoordinates
#print axioms retainedClassCoordinate
#print axioms finiteMin_le_of_mem
#print axioms le_finiteMax_of_mem
#print axioms prefixLowerEndpoint_le_prefixUpperEndpoint
#print axioms finitePrefixLower_le_finitePrefixUpper
#print axioms finitePointwiseHeatTailWindow
#print axioms finitePhysicalPointwiseHeatTailWindow
#print axioms matchedFinitePointwiseHeatTailWindow
#print axioms matchedFinitePhysicalPointwiseHeatTailWindow
#print axioms dyadicPadeNome_lt_one
#print axioms matchedPhysicalWeight_lt_one
#print axioms MatchedFiniteHeatWindowCertificate.toPointwiseHeatWindows
#print axioms MatchedFinitePhysicalHeatWindowCertificate.toPointwiseHeatWindows
#print axioms MatchedFixedFinitePhysicalHeatWindowCertificate.toPointwiseHeatWindows

end YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
