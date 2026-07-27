/-
# BF4 fence: aggregate kernel order does not imply retained-path order

`BF4RetainedPathConditionalOrder` proves that a symmetric source comparison
made before path integration passes through arbitrary nonnegative spatial
weights without paying their oscillation.  The missing physical premise is
therefore pathwise, not merely a bound on the grouped path sum.

This module makes that quantifier gap exact.  It constructs two strictly
positive paths and two sources.  At one source the first path has weight

  (height + 1) / (height + 2)

and the second has weight `1 / (height + 2)`; at the other source the two
weights are swapped.  Every grouped kernel entry is exactly one, so its
projective spread is exactly one, uniformly in `height`.  Before summation,
however, symmetric source domination needs spread at least `height + 1`.
For every proposed rational spread an explicit constructive height violates
that bound.

The smallest stronger retained-path certificate is precisely the existing
`RetainedKineticHarnackData.pathwiseDomination`: nonnegative kinetic weights
and one common source-ratio bound for every retained
`(target, complete path)` state.  Aggregate source order is not a substitute.

## Axiom gate

Finite lists, booleans, integers, and exact `Q'` arithmetic only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or placeholder.
-/

import YMGap.Continuum.BF4RetainedPathConditionalOrder

namespace YMGap.Continuum.BF4AggregatePathwiseOrderFence

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two-path hidden-redistribution family -/

/-- The small retained-path weight. -/
def hiddenSmallWeight (height : Nat) : Q' :=
  Q'.mkPos 1 (height + 2) (by omega)

/-- The large retained-path weight. -/
def hiddenLargeWeight (height : Nat) : Q' :=
  Q'.mkPos (Int.ofNat (height + 1))
    (height + 2) (by omega)

/-- The two complete interior paths. -/
def hiddenPaths : List (List Bool) :=
  [[false], [true]]

/-- Both source states. -/
def hiddenSources : List Bool := [false, true]

/-- Both terminal states.  The kinetic family is terminal-independent. -/
def hiddenTargets : List Bool := [false, true]

/-- Swap the large and small path weights between the two sources. -/
def hiddenKineticWeight
    (height : Nat) :
    Bool → Bool → List Bool → Q'
  | false, _, false :: [] => hiddenLargeWeight height
  | false, _, true :: [] => hiddenSmallWeight height
  | true, _, false :: [] => hiddenSmallWeight height
  | true, _, true :: [] => hiddenLargeWeight height
  | _, _, _ => 0

theorem hiddenSmallWeight_pos (height : Nat) :
    (0 : Q') < hiddenSmallWeight height := by
  unfold hiddenSmallWeight
  show (0 : Int) * (height + 2 : Nat) <
    (1 : Int) * (1 : Int)
  simp

theorem hiddenLargeWeight_pos (height : Nat) :
    (0 : Q') < hiddenLargeWeight height := by
  unfold hiddenLargeWeight
  show (0 : Int) * (height + 2 : Nat) <
    ((height + 1 : Nat) : Int) * (1 : Int)
  simp

/-- The large path weight is exactly `(height+1)` times the small one. -/
theorem hiddenLargeWeight_eqv_ofNat_mul_small (height : Nat) :
    hiddenLargeWeight height ≈
      Q'.ofNat (height + 1) * hiddenSmallWeight height := by
  unfold hiddenLargeWeight hiddenSmallWeight
  show
    ((height + 1 : Nat) : Int) *
        (((Q'.ofNat (height + 1) *
          Q'.mkPos 1 (height + 2) (by omega)).den) : Int) =
      (Q'.ofNat (height + 1) *
          Q'.mkPos 1 (height + 2) (by omega)).num *
        ((height + 2 : Nat) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mkPos_num,
    Q'.mkPos_den]
  push_cast
  ac_rfl

/-- The two hidden path weights sum to exactly one. -/
theorem hiddenLarge_add_small_eqv_one (height : Nat) :
    hiddenLargeWeight height + hiddenSmallWeight height ≈
      (1 : Q') := by
  unfold hiddenLargeWeight hiddenSmallWeight
  show
    (Q'.mkPos (Int.ofNat (height + 1))
        (height + 2) (by omega) +
      Q'.mkPos 1 (height + 2) (by omega)).num *
        ((1 : Q').den : Int) =
      (1 : Q').num *
        ((Q'.mkPos (Int.ofNat (height + 1))
          (height + 2) (by omega) +
        Q'.mkPos 1 (height + 2) (by omega)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Q'.mkPos_num, Q'.mkPos_den,
    show (1 : Q').num = 1 from rfl,
    show (1 : Q').den = 1 from rfl]
  push_cast
  simp only [Int.mul_one, Int.one_mul]
  calc
    Int.ofNat (height + 1) * (↑height + 1 + 1) +
          (↑height + 1 + 1) =
        (Int.ofNat (height + 1) + 1) *
          (↑height + 1 + 1) := by
            rw [Int.add_mul, Int.one_mul]
    _ = (↑height + 1 + 1) * (↑height + 1 + 1) := by
      congr 1

theorem hiddenSmall_add_large_eqv_one (height : Nat) :
    hiddenSmallWeight height + hiddenLargeWeight height ≈
      (1 : Q') :=
  Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv _ _)
    (hiddenLarge_add_small_eqv_one height)

/-- Every integrated/grouped entry is exactly one.  The path redistribution
is completely invisible after summation. -/
theorem hiddenGroupedKernel_eqv_one
    (height : Nat) (source target : Bool) :
    groupedPathKernel
        hiddenPaths (hiddenKineticWeight height)
        source target ≈ 1 := by
  cases source <;> cases target
  · change
      hiddenLargeWeight height +
          (hiddenSmallWeight height + 0) ≈ 1
    rw [Q'.add_zero']
    exact hiddenLarge_add_small_eqv_one height
  · change
      hiddenLargeWeight height +
          (hiddenSmallWeight height + 0) ≈ 1
    rw [Q'.add_zero']
    exact hiddenLarge_add_small_eqv_one height
  · change
      hiddenSmallWeight height +
          (hiddenLargeWeight height + 0) ≈ 1
    rw [Q'.add_zero']
    exact hiddenSmall_add_large_eqv_one height
  · change
      hiddenSmallWeight height +
          (hiddenLargeWeight height + 0) ≈ 1
    rw [Q'.add_zero']
    exact hiddenSmall_add_large_eqv_one height

theorem hiddenGroupedKernel_pos
    (height : Nat) (source target : Bool) :
    (0 : Q') <
      groupedPathKernel
        hiddenPaths (hiddenKineticWeight height)
        source target :=
  Q'.pos_of_lt_of_le
    (by decide)
    (Q'.ge_of_eqv
      (hiddenGroupedKernel_eqv_one
        height source target))

private theorem hiddenGroupedProduct_eqv_one
    (height : Nat)
    (first second left right : Bool) :
    groupedPathKernel
          hiddenPaths (hiddenKineticWeight height)
          first left *
        groupedPathKernel
          hiddenPaths (hiddenKineticWeight height)
          second right ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (groupedPathKernel
        hiddenPaths (hiddenKineticWeight height)
        first left)
      1
      (groupedPathKernel
        hiddenPaths (hiddenKineticWeight height)
        second right)
      (hiddenGroupedKernel_eqv_one
        height first left)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      1
      (groupedPathKernel
        hiddenPaths (hiddenKineticWeight height)
        second right)
      1
      (hiddenGroupedKernel_eqv_one
        height second right)) ?_
  exact Q'.one_mul_eqv 1

/-- The aggregate kernel has a genuine spread-one projective certificate,
uniformly in the hidden path height. -/
def hiddenAggregateSpreadOneCertificate (height : Nat) :
    FiniteCrossRatioDiameterCertificate
      (groupedPathKernel
        hiddenPaths (hiddenKineticWeight height))
      hiddenSources hiddenTargets where
  spread := 1
  one_le_spread := Q'.le_refl' 1
  strictlyPositive := by
    intro source _ target _
    exact hiddenGroupedKernel_pos height source target
  crossRatioBound := by
    intro first _ second _ left _ right _
    have hleft :
        groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              first left *
            groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              second right ≈ 1 :=
      hiddenGroupedProduct_eqv_one
        height first second left right
    have hreverse :
        groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              first right *
            groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              second left ≈ 1 :=
      hiddenGroupedProduct_eqv_one
        height first second right left
    have hright :
        ((1 : Q') * 1) *
            (groupedPathKernel
                hiddenPaths (hiddenKineticWeight height)
                first right *
              groupedPathKernel
                hiddenPaths (hiddenKineticWeight height)
                second left) ≈ 1 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          ((1 : Q') * 1)
          1
          (groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              first right *
            groupedPathKernel
              hiddenPaths (hiddenKineticWeight height)
              second left)
          (Q'.mul_one_eqv 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          1 _ 1 hreverse) ?_
      exact Q'.one_mul_eqv 1
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleft)
      (Q'.ge_of_eqv hright)

theorem hiddenAggregateSpreadOneCertificate_spread
    (height : Nat) :
    (hiddenAggregateSpreadOneCertificate height).spread = 1 :=
  rfl

/-! ## 2. Exact retained-path obstruction -/

/-- Every retained kinetic weight in the selected finite family is
nonnegative.  Thus the obstruction below is order-theoretic, not caused by
signed cancellation. -/
theorem hiddenKineticWeight_nonnegative_on (height : Nat) :
    ∀ source, source ∈ hiddenSources →
      ∀ target, target ∈ hiddenTargets →
        ∀ path, path ∈ hiddenPaths →
          (0 : Q') ≤
            hiddenKineticWeight height source target path := by
  intro source _ target _ path hpath
  simp only [hiddenPaths, List.mem_cons, List.not_mem_nil,
    or_false] at hpath
  rcases hpath with hpath | hpath
  · subst path
    cases source <;> cases target
    · exact Q'.le_of_lt (hiddenLargeWeight_pos height)
    · exact Q'.le_of_lt (hiddenLargeWeight_pos height)
    · exact Q'.le_of_lt (hiddenSmallWeight_pos height)
    · exact Q'.le_of_lt (hiddenSmallWeight_pos height)
  · subst path
    cases source <;> cases target
    · exact Q'.le_of_lt (hiddenSmallWeight_pos height)
    · exact Q'.le_of_lt (hiddenSmallWeight_pos height)
    · exact Q'.le_of_lt (hiddenLargeWeight_pos height)
    · exact Q'.le_of_lt (hiddenLargeWeight_pos height)

/-- The exact extra retained-path field needed beyond aggregate order:
one common source-ratio bound before summation, at each fixed
`(target, complete path)`. -/
def SymmetricRetainedPathDomination
    (height : Nat) (spread : Q') : Prop :=
  ∀ first, first ∈ hiddenSources →
    ∀ second, second ∈ hiddenSources →
      ∀ target, target ∈ hiddenTargets →
        ∀ path, path ∈ hiddenPaths →
          hiddenKineticWeight height first target path ≤
            spread *
              hiddenKineticWeight height second target path

/-- Any symmetric retained-path certificate must see the hidden ratio
`height + 1`, although the grouped certificate sees only one. -/
theorem symmetricRetainedPathDomination_forces_height
    (height : Nat) (spread : Q')
    (hdom : SymmetricRetainedPathDomination height spread) :
    Q'.ofNat (height + 1) ≤ spread := by
  have hlargeSmall :
      hiddenLargeWeight height ≤
        spread * hiddenSmallWeight height := by
    exact hdom false (by decide) true (by decide)
      false (by decide) [false] (by decide)
  have hscaled :
      Q'.ofNat (height + 1) *
          hiddenSmallWeight height ≤
        spread * hiddenSmallWeight height :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (hiddenLargeWeight_eqv_ofNat_mul_small height))
      hlargeSmall
  exact
    BakryEmery.le_of_mul_le_mul_right_pos
      (hiddenSmallWeight_pos height) hscaled

/-- Constructive Archimedean height: the numerator of a positive-denominator
rational gives an explicit natural whose successor is strictly larger. -/
private theorem lt_ofNat_toNat_succ_local (bound : Q') :
    bound < Q'.ofNat (bound.num.toNat + 1) := by
  have hdenOne : (1 : Int) ≤ (bound.den : Int) := by
    exact_mod_cast bound.den_pos
  have hnumLe :
      bound.num ≤ (bound.num.toNat : Int) :=
    Int.self_le_toNat bound.num
  have hmultiplierNonnegative :
      (0 : Int) ≤ (bound.num.toNat : Int) + 1 := by
    have hcastNonnegative :
        (0 : Int) ≤ (bound.num.toNat : Int) :=
      Int.natCast_nonneg _
    omega
  have hmul :
      ((bound.num.toNat : Int) + 1) * (1 : Int) ≤
        ((bound.num.toNat : Int) + 1) *
          (bound.den : Int) :=
    Int.mul_le_mul_of_nonneg_left
      hdenOne hmultiplierNonnegative
  rw [Int.mul_one] at hmul
  show
    bound.num *
        ((Q'.ofNat (bound.num.toNat + 1)).den : Int) <
      (Q'.ofNat (bound.num.toNat + 1)).num *
        (bound.den : Int)
  have hden :
      (Q'.ofNat (bound.num.toNat + 1)).den = 1 :=
    rfl
  have hnum :
      (Q'.ofNat (bound.num.toNat + 1)).num =
        ((bound.num.toNat + 1 : Nat) : Int) :=
    rfl
  rw [hden, hnum]
  push_cast
  push_cast at hmul
  omega

private theorem not_reverse_le_of_lt {left right : Q'}
    (hlt : left < right) :
    ¬ right ≤ left := by
  intro hle
  exact (Int.not_lt_of_ge hle) hlt

/-- At the explicit height `spread.num.toNat`, the pathwise source
domination with the proposed rational spread is impossible. -/
theorem symmetricRetainedPathDomination_fails
    (spread : Q') :
    ¬ SymmetricRetainedPathDomination spread.num.toNat spread := by
  intro hdom
  exact not_reverse_le_of_lt
    (lt_ofNat_toNat_succ_local spread)
    (symmetricRetainedPathDomination_forces_height
      spread.num.toNat spread hdom)

/-! ## 3. Aggregate-versus-pathwise fence and minimal repair -/

/-- The existing retained-path data exposes exactly the stronger field:
its `pathwiseDomination` is the minimal pre-integration source-order
certificate defined above. -/
theorem retainedKineticHarnackData_supplies_minimal_certificate
    (height : Nat)
    (data :
      RetainedKineticHarnackData
        hiddenPaths (hiddenKineticWeight height)
        hiddenSources hiddenTargets) :
    SymmetricRetainedPathDomination height data.spread := by
  intro first hfirst second hsecond target htarget path hpath
  exact data.pathwiseDomination
    first hfirst second hsecond target htarget path hpath

/-- Conversely, for this nonnegative finite family, the minimal pathwise
source-order field and `1 ≤ spread` assemble the full retained-path
certificate. -/
def hiddenRetainedKineticHarnackData_of_minimal_certificate
    (height : Nat) (spread : Q')
    (one_le_spread : (1 : Q') ≤ spread)
    (pathwise :
      SymmetricRetainedPathDomination height spread) :
    RetainedKineticHarnackData
      hiddenPaths (hiddenKineticWeight height)
      hiddenSources hiddenTargets where
  spread := spread
  one_le_spread := one_le_spread
  kinetic_nonnegative := hiddenKineticWeight_nonnegative_on height
  pathwiseDomination := pathwise

/-- No retained-path Harnack certificate whose spread is at most the
proposed rational can exist at the explicit Archimedean height.  This is a
bundled version of the fence against the exact certificate consumed by
`BF4RetainedPathConditionalOrder`. -/
theorem no_retainedKineticHarnackData_at_or_below
    (proposedSpread : Q') :
    ¬ ∃ data :
        RetainedKineticHarnackData
          hiddenPaths
          (hiddenKineticWeight proposedSpread.num.toNat)
          hiddenSources hiddenTargets,
        data.spread ≤ proposedSpread := by
  rintro ⟨data, hdata⟩
  have hheightData :
      Q'.ofNat (proposedSpread.num.toNat + 1) ≤ data.spread :=
    symmetricRetainedPathDomination_forces_height
      proposedSpread.num.toNat data.spread
      (retainedKineticHarnackData_supplies_minimal_certificate
        proposedSpread.num.toNat data)
  have hheightProposed :
      Q'.ofNat (proposedSpread.num.toNat + 1) ≤ proposedSpread :=
    Q'.le_trans' _ _ _ hheightData hdata
  exact not_reverse_le_of_lt
    (lt_ofNat_toNat_succ_local proposedSpread)
    hheightProposed

/-- **Exact aggregate-versus-pathwise fence.**  Against every proposed
rational pathwise spread, the explicitly returned height gives:

* a finite nonnegative two-source/two-target/two-path kinetic family;
* a genuine aggregate cross-ratio certificate of spread exactly one;
* every grouped entry equal to one;
* failure of the required symmetric retained-path source domination.

Thus no estimate on the integrated/grouped kernel, even exact equality of
all its entries, can recover a uniform retained-path comparison. -/
theorem aggregate_spread_one_pathwise_exceeds_every_spread
    (proposedSpread : Q') :
    ∃ height : Nat,
      (∀ source, source ∈ hiddenSources →
        ∀ target, target ∈ hiddenTargets →
          ∀ path, path ∈ hiddenPaths →
            (0 : Q') ≤
              hiddenKineticWeight height source target path) ∧
      (hiddenAggregateSpreadOneCertificate height).spread = 1 ∧
      (∀ source target : Bool,
        groupedPathKernel
            hiddenPaths (hiddenKineticWeight height)
            source target ≈ 1) ∧
      ¬ SymmetricRetainedPathDomination
        height proposedSpread := by
  refine ⟨proposedSpread.num.toNat,
    hiddenKineticWeight_nonnegative_on proposedSpread.num.toNat,
    hiddenAggregateSpreadOneCertificate_spread
      proposedSpread.num.toNat,
    ?_, symmetricRetainedPathDomination_fails proposedSpread⟩
  exact hiddenGroupedKernel_eqv_one proposedSpread.num.toNat

/-! ## Axiom audit -/

#print axioms hiddenGroupedKernel_eqv_one
#print axioms hiddenAggregateSpreadOneCertificate
#print axioms hiddenKineticWeight_nonnegative_on
#print axioms symmetricRetainedPathDomination_forces_height
#print axioms symmetricRetainedPathDomination_fails
#print axioms retainedKineticHarnackData_supplies_minimal_certificate
#print axioms hiddenRetainedKineticHarnackData_of_minimal_certificate
#print axioms no_retainedKineticHarnackData_at_or_below
#print axioms aggregate_spread_one_pathwise_exceeds_every_spread

end YMGap.Continuum.BF4AggregatePathwiseOrderFence
