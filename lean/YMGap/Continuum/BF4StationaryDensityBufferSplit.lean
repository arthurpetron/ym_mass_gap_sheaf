/-
# Exact stationary-density splitting for the BF4 Perron buffer

For a finite reference weight `pi`, write kernels as densities relative to
`pi`.  If `L` and `M` preserve constants, `M` and `R` preserve `pi`, and
`pi` has total mass one, then the centered density of

    L ∘ M ∘ R

is exactly the convolution of the three centered densities.  This is the
finite constructive identity

    (L M R - Π) = (L - Π)(M - Π)(R - Π).

The final theorem presents the right-hand side in the literal
buffer--middle--buffer format consumed by
`BF4BufferedPerronRowConvergence`.  Thus a physical identification of the
reflected BF4 joint with a stationary transfer power loses neither a carrier
factor nor a minimum-marginal denominator.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4BufferedPerronRowConvergence
import YMGap.Continuum.BF4PhysicalConditionalDensity

namespace YMGap.Continuum.BF4StationaryDensityBufferSplit

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

/-! ## 1. Weighted density composition -/

/-- Composition of two kernel densities relative to a finite weight. -/
def finiteWeightedDensityCompose
    {State : Type}
    (states : List State) (weight : State → Q')
    (left right : State → State → Q')
    (source target : State) : Q' :=
  listQSum
    (fun middle =>
      (weight middle * left source middle) *
        right middle target)
    states

/-- Density after subtracting the constant vacuum density one. -/
def finiteCenteredDensity
    {State : Type}
    (kernel : State → State → Q')
    (source target : State) : Q' :=
  kernel source target + (-1)

private theorem listQSum_neg_local
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listQSum (fun state => -(value state)) states ≈
        -(listQSum value states)
  | [] => by
      exact Q'.eqv_refl 0
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (-(value head)) _ _
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv
          (value head) (listQSum value tail))

/-- Weighted sums respect pointwise rational equivalence. -/
private theorem listQSum_congr_local
    {State : Type} {left right : State → Q'}
    (pointwise : ∀ state, left state ≈ right state) :
    ∀ states : List State,
      listQSum left states ≈ listQSum right states
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      unfold listQSum
      exact Q'.add_eqv_congr'
        (pointwise head)
        (listQSum_congr_local pointwise tail)

/-! ## 2. Centering commutes with stationary composition -/

/-- The centered density of a two-factor stationary composition is the
composition of the two centered densities.  Only the left row and right
column normalization used by the cancellation are assumed. -/
theorem centered_compose_eq_compose_centered
    {State : Type}
    (states : List State) (weight : State → Q')
    (left right : State → State → Q')
    (weight_total :
      listQSum weight states ≈ 1)
    (left_row :
      ∀ source,
        listQSum
            (fun middle =>
              weight middle * left source middle)
            states ≈
          1)
    (right_column :
      ∀ target,
        listQSum
            (fun middle =>
              weight middle * right middle target)
            states ≈
          1)
    (source target : State) :
    finiteCenteredDensity
        (finiteWeightedDensityCompose
          states weight left right)
        source target ≈
      finiteWeightedDensityCompose
        states weight
        (finiteCenteredDensity left)
        (finiteCenteredDensity right)
        source target := by
  let productTerm : State → Q' := fun middle =>
    (weight middle * left source middle) *
      right middle target
  let leftTerm : State → Q' := fun middle =>
    weight middle * left source middle
  let rightTerm : State → Q' := fun middle =>
    weight middle * right middle target
  have hintegrand :
      ∀ middle,
        (weight middle *
            finiteCenteredDensity left source middle) *
              finiteCenteredDensity right middle target ≈
          ((productTerm middle + (-(leftTerm middle))) +
            (-(rightTerm middle))) +
              weight middle := by
    intro middle
    unfold finiteCenteredDensity productTerm leftTerm rightTerm
    ac_qeqv
  have hexpand :
      finiteWeightedDensityCompose
          states weight
          (finiteCenteredDensity left)
          (finiteCenteredDensity right)
          source target ≈
        ((listQSum productTerm states +
            (-(listQSum leftTerm states))) +
          (-(listQSum rightTerm states))) +
            listQSum weight states := by
    unfold finiteWeightedDensityCompose
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_local hintegrand states) ?_
    refine Q'.eqv_trans _
      (listQSum
          (fun middle =>
            (productTerm middle + (-(leftTerm middle))) +
              (-(rightTerm middle)))
          states +
        listQSum weight states) _ ?_ ?_
    · exact listQSum_add _ _ states
    refine Q'.eqv_trans _
      ((listQSum
          (fun middle =>
            productTerm middle + (-(leftTerm middle)))
          states +
        listQSum
          (fun middle => -(rightTerm middle))
          states) +
        listQSum weight states) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (listQSum_add _ _ states)
    refine Q'.eqv_trans _
      (((listQSum productTerm states +
          listQSum
            (fun middle => -(leftTerm middle))
            states) +
        listQSum
          (fun middle => -(rightTerm middle))
          states) +
        listQSum weight states) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (listQSum_add _ _ states))
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_neg_local leftTerm states))
        (listQSum_neg_local rightTerm states))
  have hcollapse :
      ((listQSum productTerm states +
          (-(listQSum leftTerm states))) +
        (-(listQSum rightTerm states))) +
          listQSum weight states ≈
        listQSum productTerm states + (-1) := by
    refine Q'.eqv_trans _
      (((listQSum productTerm states + (-1)) + (-1)) + 1) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _
              (left_row source)))
          (Q'.neg_eqv_congr _ _
            (right_column target)))
        weight_total
    · ac_qeqv
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hexpand hcollapse)

/-- A stationary column remains normalized after weighted composition. -/
theorem compose_column_normalized
    {State : Type}
    (states : List State) (weight : State → Q')
    (left right : State → State → Q')
    (left_column :
      ∀ middle,
        listQSum
            (fun source =>
              weight source * left source middle)
            states ≈
          1)
    (right_column :
      ∀ target,
        listQSum
            (fun middle =>
              weight middle * right middle target)
            states ≈
          1)
    (target : State) :
    listQSum
        (fun source =>
          weight source *
            finiteWeightedDensityCompose
              states weight left right source target)
        states ≈
      1 := by
  unfold finiteWeightedDensityCompose
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun middle =>
            weight source *
              ((weight middle * left source middle) *
                right middle target))
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_local
    intro source
    exact Q'.eqv_symm
      (listQSum_mul_left
        (weight source)
        (fun middle =>
          (weight middle * left source middle) *
            right middle target)
        states)
  refine Q'.eqv_trans _
    (listQSum
      (fun middle =>
        listQSum
          (fun source =>
            weight source *
              ((weight middle * left source middle) *
                right middle target))
          states)
      states) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source middle =>
          weight source *
            ((weight middle * left source middle) *
              right middle target))
        states states)
  refine Q'.eqv_trans _
    (listQSum
      (fun middle =>
        listQSum
          (fun source =>
            (weight source *
              (weight middle * left source middle)) *
                right middle target)
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_local
    intro middle
    apply listQSum_congr_local
    intro source
    ac_qeqv
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_local
      (fun middle => by
        refine Q'.eqv_trans _
          ((weight middle * right middle target) *
            listQSum
              (fun source =>
                weight source * left source middle)
              states) _ ?_ ?_
        · refine Q'.eqv_trans _
            (listQSum
              (fun source =>
                (weight middle * right middle target) *
                  (weight source * left source middle))
              states) _ ?_ ?_
          · apply listQSum_congr_local
            intro source
            ac_qeqv
          · exact listQSum_mul_left _ _ _
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (left_column middle))
          (Q'.mul_one_eqv _))
      states) ?_
  exact right_column target

/-- Exact three-factor stationary centering identity, already regrouped in
the source-to-target order used by the physical slab. -/
theorem centered_triple_eq_centered_triple
    {State : Type}
    (states : List State) (weight : State → Q')
    (left middle right : State → State → Q')
    (weight_total :
      listQSum weight states ≈ 1)
    (left_row :
      ∀ source,
        listQSum
            (fun state =>
              weight state * left source state)
            states ≈
          1)
    (middle_row :
      ∀ source,
        listQSum
            (fun state =>
              weight state * middle source state)
            states ≈
          1)
    (middle_column :
      ∀ target,
        listQSum
            (fun state =>
              weight state * middle state target)
            states ≈
          1)
    (right_column :
      ∀ target,
        listQSum
            (fun state =>
              weight state * right state target)
            states ≈
          1)
    (source target : State) :
    finiteCenteredDensity
        (finiteWeightedDensityCompose
          states weight left
          (finiteWeightedDensityCompose
            states weight middle right))
        source target ≈
      finiteWeightedDensityCompose
        states weight
        (finiteCenteredDensity left)
        (finiteWeightedDensityCompose
          states weight
          (finiteCenteredDensity middle)
          (finiteCenteredDensity right))
        source target := by
  have hrightComposeColumn :
      ∀ target,
        listQSum
            (fun state =>
              weight state *
                finiteWeightedDensityCompose
                  states weight middle right state target)
            states ≈
          1 :=
    fun nextTarget =>
      compose_column_normalized
        states weight middle right
        middle_column right_column nextTarget
  refine Q'.eqv_trans _ _ _
    (centered_compose_eq_compose_centered
      states weight left
      (finiteWeightedDensityCompose
        states weight middle right)
      weight_total left_row hrightComposeColumn
      source target) ?_
  unfold finiteWeightedDensityCompose
  apply listQSum_congr_local
  intro state
  exact Q'.mul_eqv_congr_left _ _ _
    (centered_compose_eq_compose_centered
      states weight middle right
      weight_total middle_row right_column
      state target)

/-! ## 3. Literal BF4 buffer form -/

/-- The stationary three-factor identity in the exact syntax consumed by
the buffer estimate. -/
theorem centered_triple_eq_finiteBufferedDensity
    {State : Type}
    (states : List State) (weight : State → Q')
    (left middle right : State → State → Q')
    (weight_total :
      listQSum weight states ≈ 1)
    (left_row :
      ∀ source,
        listQSum
            (fun state =>
              weight state * left source state)
            states ≈
          1)
    (middle_row :
      ∀ source,
        listQSum
            (fun state =>
              weight state * middle source state)
            states ≈
          1)
    (middle_column :
      ∀ target,
        listQSum
            (fun state =>
              weight state * middle state target)
            states ≈
          1)
    (right_column :
      ∀ target,
        listQSum
            (fun state =>
              weight state * right state target)
            states ≈
          1)
    (source target : State) :
    finiteCenteredDensity
        (finiteWeightedDensityCompose
          states weight left
          (finiteWeightedDensityCompose
            states weight middle right))
        source target ≈
      finiteBufferedDensity
        states states
        (fun source state =>
          weight state *
            finiteCenteredDensity left source state)
        (fun first second =>
          weight second *
            finiteCenteredDensity middle first second)
        (finiteCenteredDensity right)
        source target := by
  exact centered_triple_eq_centered_triple
    states weight left middle right
    weight_total left_row middle_row
    middle_column right_column source target

/-! ## 4. Physical retained-carrier specialization -/

open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiveHolonomyPerronCutoff

/-- Exact identification of one physical reflected BF4 row with a
three-piece stationary density, together with the three cancellation-free
absolute budgets needed by the Perron argument.

This is not a generic surrogate carrier: every intermediate sum is over the
literal `centralPositiveHalfStates` at the displayed physical cutoff. -/
structure PhysicalBF4StationaryTripleRow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling)
    (left middle right : EdgeLabelling → EdgeLabelling → Q')
    (endpointBound middleBound : Q') : Type where
  endpointBound_nonnegative :
    (0 : Q') ≤ endpointBound
  middleBound_nonnegative :
    (0 : Q') ≤ middleBound
  left_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              left row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  middle_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              middle row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  middle_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              middle state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  right_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              right state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  joint_density :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralNormalizedPhysicalReflectedKernel
            w hw K halfExtent source target ≈
          (centralPhysicalRowMarginal
                w hw K halfExtent source *
            centralPhysicalRowMarginal
                w hw K halfExtent target) *
            finiteWeightedDensityCompose
              (centralPositiveHalfStates
                w hw K halfExtent)
              (centralPhysicalRowMarginal
                w hw K halfExtent)
              left
              (finiteWeightedDensityCompose
                (centralPositiveHalfStates
                  w hw K halfExtent)
                (centralPhysicalRowMarginal
                  w hw K halfExtent)
                middle right)
              source target
  left_bound :
    listQSum
        (fun state =>
          Q'.abs
            (centralPhysicalRowMarginal
                w hw K halfExtent state *
              finiteCenteredDensity left source state))
        (centralPositiveHalfStates
          w hw K halfExtent) ≤
      endpointBound
  middle_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun second =>
              Q'.abs
                (centralPhysicalRowMarginal
                    w hw K halfExtent second *
                  finiteCenteredDensity
                    middle first second))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          middleBound
  right_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun target =>
              centralPhysicalRowMarginal
                  w hw K halfExtent target *
                Q'.abs
                  (finiteCenteredDensity
                    right first target))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          endpointBound

namespace PhysicalBF4StationaryTripleRow

/-- Direct all-label regrouping turns a stationary physical transfer split
into the exact generic BF4 buffer certificate. -/
def toPhysicalBF4BufferedCenteredRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {left middle right :
      EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4StationaryTripleRow
        hw K halfExtent source
        left middle right
        endpointBound middleBound) :
    PhysicalBF4BufferedCenteredRow
      (w := w) (hw := hw)
      (K := K) (halfExtent := halfExtent)
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralPositiveHalfStates
        w hw K halfExtent)
      (fun row state =>
        centralPhysicalRowMarginal
            w hw K halfExtent state *
          finiteCenteredDensity left row state)
      (fun first second =>
        centralPhysicalRowMarginal
            w hw K halfExtent second *
          finiteCenteredDensity middle first second)
      (finiteCenteredDensity right)
      source endpointBound middleBound where
  sourceWeight_nonnegative :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent source
  targetWeight_nonnegative := by
    intro target _
    exact centralPhysicalRowMarginal_nonnegative
      hw K halfExtent target
  endpointBound_nonnegative :=
    data.endpointBound_nonnegative
  middleBound_nonnegative :=
    data.middleBound_nonnegative
  centered_density := by
    intro target htarget
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let weight :=
      centralPhysicalRowMarginal
        w hw K halfExtent
    let triple :=
      finiteWeightedDensityCompose
        states weight left
        (finiteWeightedDensityCompose
          states weight middle right)
    have hjoint :=
      data.joint_density target htarget
    have hcentered :
        finiteCenteredDensity triple source target ≈
          finiteBufferedDensity
            states states
            (fun row state =>
              weight state *
                finiteCenteredDensity left row state)
            (fun first second =>
              weight second *
                finiteCenteredDensity middle first second)
            (finiteCenteredDensity right)
            source target := by
      exact centered_triple_eq_finiteBufferedDensity
        states weight left middle right
        (centralPositiveRowMarginal_total_one
          w hw K halfExtent)
        data.left_row data.middle_row
        data.middle_column data.right_column
        source target
    let sourceTargetWeight :=
      weight source * weight target
    refine Q'.eqv_trans _
      (sourceTargetWeight *
        finiteCenteredDensity triple source target) _ ?_ ?_
    · unfold centralPhysicalVacuumJoint
      refine Q'.eqv_trans _
        ((sourceTargetWeight * triple source target) +
          (-sourceTargetWeight)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          hjoint (Q'.eqv_refl _)
      · unfold finiteCenteredDensity
        ac_qeqv
    · exact Q'.mul_eqv_congr_left
        sourceTargetWeight _ _ hcentered
  left_bound :=
    data.left_bound
  middle_bound :=
    data.middle_bound
  right_bound :=
    data.right_bound

/-- The exact physical stationary split inherits the carrier-free
`C² rho` centered-row estimate. -/
theorem physical_centered_row_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {left middle right :
      EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4StationaryTripleRow
        hw K halfExtent source
        left middle right
        endpointBound middleBound) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      ((endpointBound * endpointBound) * middleBound) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  physicalCenteredPhysicalRowMass_le_of_buffered
    data.toPhysicalBF4BufferedCenteredRow

/-- The sharpened spacing-dependent Faraut depth pays an exact physical
stationary transfer split down to the required `1/16` row. -/
theorem physical_centered_row_le_sixteenth_of_faraut
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {left middle right :
      EdgeLabelling → EdgeLabelling → Q'}
    {bits depth : Nat} {qS : Q'}
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ depth)
    (data :
      PhysicalBF4StationaryTripleRow
        hw K halfExtent source
        left middle right
        (farautRetainedSpread bits)
        (qS ^ (depth - 2))) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  physicalCenteredPhysicalRowMass_le_sixteenth_of_faraut_buffered
    qS_nonnegative qS_le_quarter depth_available
    data.toPhysicalBF4BufferedCenteredRow

end PhysicalBF4StationaryTripleRow

/-! ## 5. A genuine depth-indexed all-label carrier -/

open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.CompactDualFiniteBlockRemainder

/-- All words of an exact length over a finite alphabet.  Unlike the
historical singleton embedding, this carrier has a literal intermediate
state at every transfer step. -/
def finiteWords {State : Type}
    (states : List State) : Nat → List (List State)
  | 0 => [[]]
  | depth + 1 =>
      states.flatMap (fun head =>
        (finiteWords states depth).map
          (fun tail => head :: tail))

/-- Every enumerated word has exactly the requested length. -/
theorem finiteWords_length
    {State : Type} (states : List State) :
    ∀ {depth : Nat} {path : List State},
      path ∈ finiteWords states depth →
        path.length = depth
  | 0, path, hpath => by
      change path ∈ ([[]] : List (List State)) at hpath
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
      subst path
      rfl
  | depth + 1, path, hpath => by
      change
        path ∈
          states.flatMap (fun head =>
            (finiteWords states depth).map
              (fun tail => head :: tail)) at hpath
      obtain ⟨head, _, htailBlock⟩ :=
        List.mem_flatMap.mp hpath
      obtain ⟨tail, htail, rfl⟩ :=
        List.mem_map.mp htailBlock
      simp only [List.length_cons]
      exact congrArg Nat.succ
        (finiteWords_length states htail)

/-- The genuine depth-indexed whole-slab carrier retains every face-channel
field and shared-link fusion witness at every transfer step. -/
def wholeSlabJointCarrierMarkovPaths
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (depth : Nat) :
    List (List (WholeSlabJointCarrierCode S fineState)) :=
  finiteWords
    (wholeSlabJointCarrierCodes S fineState)
    depth

/-- Its path length is definitionally tied to the analytic depth. -/
theorem wholeSlabJointCarrierMarkovPaths_length
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {depth : Nat}
    {path : List (WholeSlabJointCarrierCode S fineState)}
    (hpath :
      path ∈
        wholeSlabJointCarrierMarkovPaths
          S fineState depth) :
    path.length = depth :=
  finiteWords_length
    (wholeSlabJointCarrierCodes S fineState)
    hpath

/-- Diagnostic: the older retained carrier has path length one.  Therefore
its singleton-path membership cannot by itself witness the sharpened Faraut
depth `46 * bits + 5`. -/
theorem oldWholeSlabJointCarrierPath_length_one
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {path : List (WholeSlabJointCarrierCode S fineState)}
    (hpath :
      path ∈ wholeSlabJointCarrierPaths S fineState) :
    path.length = 1 := by
  unfold wholeSlabJointCarrierPaths at hpath
  obtain ⟨code, _, rfl⟩ := List.mem_map.mp hpath
  rfl

/-- The singleton carrier cannot silently discharge the physical depth
premise. -/
theorem oldWholeSlabJointCarrierPath_not_harnack_depth
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {path : List (WholeSlabJointCarrierCode S fineState)}
    (hpath :
      path ∈ wholeSlabJointCarrierPaths S fineState)
    (bits : Nat) :
    ¬ farautHarnackRequiredDepth bits ≤ path.length := by
  intro hdepth
  rw [oldWholeSlabJointCarrierPath_length_one hpath] at hdepth
  unfold farautHarnackRequiredDepth at hdepth
  omega

/-! ## 6. Exact weighted transfer powers and their all-word expansion -/

/-- The density of `steps + 1` consecutive one-step transfers.  Starting
at one step avoids introducing a reciprocal of the stationary weight for
the zero-step identity density. -/
def finiteWeightedDensityPower
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q') :
    Nat → State → State → Q'
  | 0 => kernel
  | steps + 1 =>
      finiteWeightedDensityCompose
        states weight kernel
        (finiteWeightedDensityPower
          states weight kernel steps)

/-- A stationary row remains normalized after weighted composition. -/
theorem compose_row_normalized
    {State : Type}
    (states : List State) (weight : State → Q')
    (left right : State → State → Q')
    (left_row :
      ∀ source,
        listQSum
            (fun middle =>
              weight middle * left source middle)
            states ≈
          1)
    (right_row :
      ∀ middle,
        listQSum
            (fun target =>
              weight target * right middle target)
            states ≈
          1)
    (source : State) :
    listQSum
        (fun target =>
          weight target *
            finiteWeightedDensityCompose
              states weight left right source target)
        states ≈
      1 := by
  unfold finiteWeightedDensityCompose
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun middle =>
            weight target *
              ((weight middle * left source middle) *
                right middle target))
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_local
    intro target
    exact Q'.eqv_symm
      (listQSum_mul_left
        (weight target)
        (fun middle =>
          (weight middle * left source middle) *
            right middle target)
        states)
  refine Q'.eqv_trans _
    (listQSum
      (fun middle =>
        listQSum
          (fun target =>
            weight target *
              ((weight middle * left source middle) *
                right middle target))
          states)
      states) _ ?_ ?_
  · exact listQSum_swap
        (fun middle target =>
          weight target *
            ((weight middle * left source middle) *
              right middle target))
        states states
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_local
      (fun middle => by
        refine Q'.eqv_trans _
          ((weight middle * left source middle) *
            listQSum
              (fun target =>
                weight target * right middle target)
              states) _ ?_ ?_
        · refine Q'.eqv_trans _
            (listQSum
              (fun target =>
                (weight middle * left source middle) *
                  (weight target * right middle target))
              states) _ ?_ ?_
          · apply listQSum_congr_local
            intro target
            ac_qeqv
          · exact listQSum_mul_left _ _ _
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (right_row middle))
          (Q'.mul_one_eqv _))
      states) ?_
  exact left_row source

/-- Every positive-length power of a row-normalized transfer density is
row normalized. -/
theorem finiteWeightedDensityPower_row_normalized
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (kernel_row :
      ∀ source,
        listQSum
            (fun target =>
              weight target * kernel source target)
            states ≈
          1) :
    ∀ steps source,
      listQSum
          (fun target =>
            weight target *
              finiteWeightedDensityPower
                states weight kernel steps source target)
          states ≈
        1
  | 0, source => kernel_row source
  | steps + 1, source => by
      unfold finiteWeightedDensityPower
      exact compose_row_normalized
        states weight kernel
        (finiteWeightedDensityPower
          states weight kernel steps)
        kernel_row
        (finiteWeightedDensityPower_row_normalized
          states weight kernel kernel_row steps)
        source

/-- Every positive-length power of a column-normalized transfer density is
column normalized. -/
theorem finiteWeightedDensityPower_column_normalized
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (kernel_column :
      ∀ target,
        listQSum
            (fun source =>
              weight source * kernel source target)
            states ≈
          1) :
    ∀ steps target,
      listQSum
          (fun source =>
            weight source *
              finiteWeightedDensityPower
                states weight kernel steps source target)
          states ≈
        1
  | 0, target => kernel_column target
  | steps + 1, target => by
      unfold finiteWeightedDensityPower
      exact compose_column_normalized
        states weight kernel
        (finiteWeightedDensityPower
          states weight kernel steps)
        kernel_column
        (finiteWeightedDensityPower_column_normalized
          states weight kernel kernel_column steps)
        target

/-- Product attached to a word of intermediate transfer states.  A word of
length `steps` contains exactly the `steps` internal vertices of a path
with `steps + 1` transfer edges. -/
def finiteWeightedDensityPathProduct
    {State : Type}
    (weight : State → Q')
    (kernel : State → State → Q')
    (source target : State) :
    List State → Q'
  | [] => kernel source target
  | middle :: tail =>
      (weight middle * kernel source middle) *
        finiteWeightedDensityPathProduct
          weight kernel middle target tail

/-- Sum over every exact-length word of intermediate states. -/
def finiteWeightedDensityPathSum
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (steps : Nat) (source target : State) : Q' :=
  listQSum
    (finiteWeightedDensityPathProduct
      weight kernel source target)
    (finiteWords states steps)

/-- The recursive transfer power is exactly the complete all-label path
sum.  No positivity, noduplication, or decidable equality is required. -/
theorem finiteWeightedDensityPathSum_eq_power
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q') :
    ∀ steps source target,
      finiteWeightedDensityPathSum
          states weight kernel steps source target ≈
        finiteWeightedDensityPower
          states weight kernel steps source target
  | 0, source, target => by
      unfold finiteWeightedDensityPathSum finiteWords
      unfold listQSum finiteWeightedDensityPathProduct
      exact Q'.eqv_of_eq (Q'.add_zero' _)
  | steps + 1, source, target => by
      unfold finiteWeightedDensityPathSum
      change
        listQSum
            (finiteWeightedDensityPathProduct
              weight kernel source target)
            (states.flatMap
              (fun middle =>
                (finiteWords states steps).map
                  (fun tail => middle :: tail))) ≈
          finiteWeightedDensityPower
            states weight kernel (steps + 1)
            source target
      refine Q'.eqv_trans _
        (listQSum
          (fun middle =>
            listQSum
              (finiteWeightedDensityPathProduct
                weight kernel source target)
              ((finiteWords states steps).map
                (fun tail => middle :: tail)))
          states) _ ?_ ?_
      · exact listQSum_flatMap
          (finiteWeightedDensityPathProduct
            weight kernel source target)
          (fun middle =>
            (finiteWords states steps).map
              (fun tail => middle :: tail))
          states
      refine Q'.eqv_trans _
        (listQSum
          (fun middle =>
            listQSum
              (fun tail =>
                (weight middle * kernel source middle) *
                  finiteWeightedDensityPathProduct
                    weight kernel middle target tail)
              (finiteWords states steps))
          states) _ ?_ ?_
      · apply listQSum_congr_local
        intro middle
        rw [listQSum_map]
        exact Q'.eqv_refl _
      refine Q'.eqv_trans _
        (listQSum
          (fun middle =>
            (weight middle * kernel source middle) *
              listQSum
                (finiteWeightedDensityPathProduct
                  weight kernel middle target)
                (finiteWords states steps))
          states) _ ?_ ?_
      · apply listQSum_congr_local
        intro middle
        exact listQSum_mul_left
          (weight middle * kernel source middle)
          (finiteWeightedDensityPathProduct
            weight kernel middle target)
          (finiteWords states steps)
      unfold finiteWeightedDensityPower
      unfold finiteWeightedDensityCompose
      apply listQSum_congr_local
      intro middle
      exact Q'.mul_eqv_congr_left
        (weight middle * kernel source middle) _ _
        (finiteWeightedDensityPathSum_eq_power
          states weight kernel steps middle target)

/-! ## 7. Physical one-step transfer constructor -/

/-- A physical BF4 row represented by a single stationary transfer density,
with one endpoint step on either side of its exact all-label middle power.

For physical depth `depth`, the middle has `depth - 3` intermediate words,
hence `depth - 2` transfer edges.  The full sandwich therefore has exactly
`depth` one-step edges.  This structure isolates the remaining Yang--Mills
input to one genuine transfer density, its reflected-joint gluing theorem,
and endpoint/middle quantitative estimates. -/
structure PhysicalBF4TransferPowerRow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling)
    (depth : Nat)
    (oneStep : EdgeLabelling → EdgeLabelling → Q')
    (endpointBound middleBound : Q') : Type where
  depth_at_least_three :
    3 ≤ depth
  endpointBound_nonnegative :
    (0 : Q') ≤ endpointBound
  middleBound_nonnegative :
    (0 : Q') ≤ middleBound
  oneStep_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  oneStep_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  joint_density :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralNormalizedPhysicalReflectedKernel
            w hw K halfExtent source target ≈
          (centralPhysicalRowMarginal
                w hw K halfExtent source *
            centralPhysicalRowMarginal
                w hw K halfExtent target) *
            finiteWeightedDensityCompose
              (centralPositiveHalfStates
                w hw K halfExtent)
              (centralPhysicalRowMarginal
                w hw K halfExtent)
              oneStep
              (finiteWeightedDensityCompose
                (centralPositiveHalfStates
                  w hw K halfExtent)
                (centralPhysicalRowMarginal
                  w hw K halfExtent)
                (finiteWeightedDensityPower
                  (centralPositiveHalfStates
                    w hw K halfExtent)
                  (centralPhysicalRowMarginal
                    w hw K halfExtent)
                  oneStep (depth - 3))
                oneStep)
              source target
  left_bound :
    listQSum
        (fun state =>
          Q'.abs
            (centralPhysicalRowMarginal
                w hw K halfExtent state *
              finiteCenteredDensity
                oneStep source state))
        (centralPositiveHalfStates
          w hw K halfExtent) ≤
      endpointBound
  middle_power_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun second =>
              Q'.abs
                (centralPhysicalRowMarginal
                    w hw K halfExtent second *
                  finiteCenteredDensity
                    (finiteWeightedDensityPower
                      (centralPositiveHalfStates
                        w hw K halfExtent)
                      (centralPhysicalRowMarginal
                        w hw K halfExtent)
                      oneStep (depth - 3))
                    first second))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          middleBound
  right_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun target =>
              centralPhysicalRowMarginal
                  w hw K halfExtent target *
                Q'.abs
                  (finiteCenteredDensity
                    oneStep first target))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          endpointBound

namespace PhysicalBF4TransferPowerRow

/-- A physical transfer-power row supplies the exact three-factor
stationary certificate used by the carrier-free Perron estimate. -/
def toStationaryTripleRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4TransferPowerRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound) :
    PhysicalBF4StationaryTripleRow
      hw K halfExtent source
      oneStep
      (finiteWeightedDensityPower
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralPhysicalRowMarginal
          w hw K halfExtent)
        oneStep (depth - 3))
      oneStep endpointBound middleBound where
  endpointBound_nonnegative :=
    data.endpointBound_nonnegative
  middleBound_nonnegative :=
    data.middleBound_nonnegative
  left_row :=
    data.oneStep_row
  middle_row :=
    finiteWeightedDensityPower_row_normalized
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      oneStep data.oneStep_row (depth - 3)
  middle_column :=
    finiteWeightedDensityPower_column_normalized
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      oneStep data.oneStep_column (depth - 3)
  right_column :=
    data.oneStep_column
  joint_density :=
    data.joint_density
  left_bound :=
    data.left_bound
  middle_bound :=
    data.middle_power_bound
  right_bound :=
    data.right_bound

/-- The middle transfer density is literally the sum over all retained
state words of the required length. -/
theorem middle_power_eq_all_word_path_sum
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4TransferPowerRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound)
    (first second : EdgeLabelling) :
    finiteWeightedDensityPower
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralPhysicalRowMarginal
          w hw K halfExtent)
        oneStep (depth - 3) first second ≈
      finiteWeightedDensityPathSum
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralPhysicalRowMarginal
          w hw K halfExtent)
        oneStep (depth - 3) first second := by
  have _ := data.depth_at_least_three
  exact Q'.eqv_symm
    (finiteWeightedDensityPathSum_eq_power
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      oneStep (depth - 3) first second)

/-- The path/sandwich bookkeeping has exactly the requested physical
depth: `(depth - 3) + 3 = depth`. -/
theorem middle_word_length_plus_endpoints
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4TransferPowerRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound) :
    depth - 3 + 3 = depth := by
  have hdepth := data.depth_at_least_three
  omega

/-- The physical one-step constructor inherits the exact `C² rho` bound. -/
theorem physical_centered_row_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4TransferPowerRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      ((endpointBound * endpointBound) * middleBound) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toStationaryTripleRow.physical_centered_row_le

/-- At the sharpened Faraut depth, a genuine physical one-step transfer
power gives the required `1/16` physical centered row. -/
theorem physical_centered_row_le_sixteenth_of_faraut
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {bits depth : Nat} {qS : Q'}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ depth)
    (data :
      PhysicalBF4TransferPowerRow
        hw K halfExtent source depth oneStep
        (farautRetainedSpread bits)
        (qS ^ (depth - 2))) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toStationaryTripleRow
    |>.physical_centered_row_le_sixteenth_of_faraut
      qS_nonnegative qS_le_quarter depth_available

end PhysicalBF4TransferPowerRow

/-! ## 8. Reduction of physical joint gluing to density gluing -/

/-- A Yang--Mills-specific density gluing certificate.  The physical Choi
joint and both stationary normalizations are no longer assumptions: they
are supplied by `BF4PhysicalConditionalDensity`.  What remains here is the
genuine geometric statement that the whole-slab conditional density is the
endpoint--middle-power--endpoint convolution of a reversible one-step
transfer, together with the three quantitative row budgets. -/
structure PhysicalBF4DensityPowerGluingRow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling)
    (depth : Nat)
    (oneStep : EdgeLabelling → EdgeLabelling → Q')
    (endpointBound middleBound : Q') : Type where
  source_mem :
    source ∈
      centralPositiveHalfStates
        w hw K halfExtent
  depth_at_least_three :
    3 ≤ depth
  endpointBound_nonnegative :
    (0 : Q') ≤ endpointBound
  middleBound_nonnegative :
    (0 : Q') ≤ middleBound
  oneStep_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  oneStep_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  density_gluing :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralPhysicalConditionalDensity
            w hw K halfExtent source target ≈
          finiteWeightedDensityCompose
            (centralPositiveHalfStates
              w hw K halfExtent)
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            oneStep
            (finiteWeightedDensityCompose
              (centralPositiveHalfStates
                w hw K halfExtent)
              (centralPhysicalRowMarginal
                w hw K halfExtent)
              (finiteWeightedDensityPower
                (centralPositiveHalfStates
                  w hw K halfExtent)
                (centralPhysicalRowMarginal
                  w hw K halfExtent)
                oneStep (depth - 3))
              oneStep)
            source target
  left_bound :
    listQSum
        (fun state =>
          Q'.abs
            (centralPhysicalRowMarginal
                w hw K halfExtent state *
              finiteCenteredDensity
                oneStep source state))
        (centralPositiveHalfStates
          w hw K halfExtent) ≤
      endpointBound
  middle_power_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun second =>
              Q'.abs
                (centralPhysicalRowMarginal
                    w hw K halfExtent second *
                  finiteCenteredDensity
                    (finiteWeightedDensityPower
                      (centralPositiveHalfStates
                        w hw K halfExtent)
                      (centralPhysicalRowMarginal
                        w hw K halfExtent)
                      oneStep (depth - 3))
                    first second))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          middleBound
  right_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        listQSum
            (fun target =>
              centralPhysicalRowMarginal
                  w hw K halfExtent target *
                Q'.abs
                  (finiteCenteredDensity
                    oneStep first target))
            (centralPositiveHalfStates
              w hw K halfExtent) ≤
          endpointBound

namespace PhysicalBF4DensityPowerGluingRow

/-- Exact normalized-joint reconstruction turns density gluing into the
one-step transfer-power certificate. -/
def toTransferPowerRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4DensityPowerGluingRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound) :
    PhysicalBF4TransferPowerRow
      hw K halfExtent source depth
      oneStep endpointBound middleBound where
  depth_at_least_three :=
    data.depth_at_least_three
  endpointBound_nonnegative :=
    data.endpointBound_nonnegative
  middleBound_nonnegative :=
    data.middleBound_nonnegative
  oneStep_row :=
    data.oneStep_row
  oneStep_column :=
    data.oneStep_column
  joint_density := by
    intro target htarget
    refine Q'.eqv_trans _
      ((centralPhysicalRowMarginal
            w hw K halfExtent source *
          centralPhysicalRowMarginal
            w hw K halfExtent target) *
        centralPhysicalConditionalDensity
          w hw K halfExtent source target) _ ?_ ?_
    · exact normalizedJoint_eq_marginals_mul_density
        data.source_mem htarget
    · exact Q'.mul_eqv_congr_left
        (centralPhysicalRowMarginal
            w hw K halfExtent source *
          centralPhysicalRowMarginal
            w hw K halfExtent target) _ _
        (data.density_gluing target htarget)
  left_bound :=
    data.left_bound
  middle_power_bound :=
    data.middle_power_bound
  right_bound :=
    data.right_bound

/-- The density-level Yang--Mills certificate reaches the exact physical
`C² rho` row theorem. -/
theorem physical_centered_row_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4DensityPowerGluingRow
        hw K halfExtent source depth
        oneStep endpointBound middleBound) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      ((endpointBound * endpointBound) * middleBound) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toTransferPowerRow.physical_centered_row_le

/-- With the Faraut endpoint spread and a quarter-contracting middle
transfer, density gluing yields the target physical `1/16` row. -/
theorem physical_centered_row_le_sixteenth_of_faraut
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {bits depth : Nat} {qS : Q'}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ depth)
    (data :
      PhysicalBF4DensityPowerGluingRow
        hw K halfExtent source depth oneStep
        (farautRetainedSpread bits)
        (qS ^ (depth - 2))) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toTransferPowerRow
    |>.physical_centered_row_le_sixteenth_of_faraut
      qS_nonnegative qS_le_quarter depth_available

end PhysicalBF4DensityPowerGluingRow

end YMGap.Continuum.BF4StationaryDensityBufferSplit

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_compose_eq_compose_centered
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.compose_column_normalized
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_triple_eq_centered_triple
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_triple_eq_finiteBufferedDensity
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.toPhysicalBF4BufferedCenteredRow
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.physical_centered_row_le
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.physical_centered_row_le_sixteenth_of_faraut
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.finiteWords_length
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.wholeSlabJointCarrierMarkovPaths_length
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.oldWholeSlabJointCarrierPath_not_harnack_depth
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.compose_row_normalized
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.finiteWeightedDensityPower_row_normalized
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.finiteWeightedDensityPower_column_normalized
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.finiteWeightedDensityPathSum_eq_power
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4TransferPowerRow.toStationaryTripleRow
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4TransferPowerRow.middle_power_eq_all_word_path_sum
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4TransferPowerRow.middle_word_length_plus_endpoints
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4TransferPowerRow.physical_centered_row_le_sixteenth_of_faraut
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4DensityPowerGluingRow.toTransferPowerRow
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4DensityPowerGluingRow.physical_centered_row_le_sixteenth_of_faraut
