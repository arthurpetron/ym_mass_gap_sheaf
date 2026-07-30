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

namespace YMGap.Continuum.BF4StationaryDensityBufferSplit

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
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

end YMGap.Continuum.BF4StationaryDensityBufferSplit

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_compose_eq_compose_centered
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.compose_column_normalized
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_triple_eq_centered_triple
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.centered_triple_eq_finiteBufferedDensity
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.toPhysicalBF4BufferedCenteredRow
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.physical_centered_row_le
#print axioms YMGap.Continuum.BF4StationaryDensityBufferSplit.PhysicalBF4StationaryTripleRow.physical_centered_row_le_sixteenth_of_faraut
