/-
# Quantitative truncation tails for completed BF4 heat products

The spacing-dependent pointwise completion supplies, for every retained
factor, a two-sided rational tail around each finite prefix.  This module
tensorizes that estimate over a finite factor list.

The product argument is sign-safe.  It assumes both the finite prefixes and
the later approximants are nonnegative and share a common nonnegative
ceiling `C`.  A one-factor error `T` then propagates through an `n`-factor
product with the recursive budget

    E(0) = 0,
    E(n+1) = C * E(n) + T * C^n.

Thus `E(n) = n * C^(n-1) * T`; in particular the literal BF4 carrier of
length 23 has error `23 * C^22 * T`.

## Honest scope

The physical specialization below uses one common rational nome `w`, a
factor-dependent class coordinate, and the strong-coupling corridor
`0 < w <= 1/2`.  It is a completed pointwise heat-product theorem, not an
identification with the interacting BF4 spin-foam slab kernel.

## Constructivity

Only structural list induction, exact `Q'` order, and the semantic
`CReal.leRat` / `ExpPos.geRat` predicates are used.  There is no
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
import YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility
import YMGap.Continuum.BF4CompletedHeatRetainedConsumer

namespace YMGap.Continuum.BF4CompletedProductTailBound

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A sign-safe rational finite-product engine -/

/-- Recursive product error budget.  The recurrence is exactly the
one obtained by replacing one bounded factor at a time. -/
def productTailBudget (ceiling tail : Q') : Nat → Q'
  | 0 => 0
  | n + 1 =>
      ceiling * productTailBudget ceiling tail n +
        tail * ceiling ^ n

/-- The recursive product budget is nonnegative when its two inputs are. -/
theorem productTailBudget_nonnegative
    {ceiling tail : Q'}
    (hceiling : (0 : Q') ≤ ceiling)
    (htail : (0 : Q') ≤ tail) :
    ∀ n, (0 : Q') ≤ productTailBudget ceiling tail n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          hceiling
          (productTailBudget_nonnegative
            hceiling htail n))
        (Q'.mul_nonneg _ _
          htail
          (Q'.pow_nonneg ceiling hceiling n))

/-- Commuting the first two factors under a right-associated product. -/
private theorem mul_rotate_eqv (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (a * b) (b * a) c
        (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- Closed form of the recursive budget at every positive length:
`E(n+1) = (n+1) * C^n * T`. -/
theorem productTailBudget_succ_eqv
    (ceiling tail : Q') :
    ∀ n,
      productTailBudget ceiling tail (n + 1) ≈
        (Q'.ofNat (n + 1) * ceiling ^ n) * tail
  | 0 => by
      have hleft :
          productTailBudget ceiling tail 1 ≈ tail := by
        unfold productTailBudget
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            (ceiling * 0) 0 (tail * 1)
            (Q'.mul_zero_eqv ceiling))
          (by
            rw [Q'.zero_add']
            exact Q'.mul_one_eqv tail)
      have hright :
          (Q'.ofNat 1 * ceiling ^ 0) * tail ≈ tail := by
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat 1 * ceiling ^ 0)
            1 tail
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left
                (Q'.ofNat 1) (ceiling ^ 0) 1
                (Q'.eqv_refl 1))
              (Q'.one_mul_eqv 1)))
          (Q'.one_mul_eqv tail)
      exact Q'.eqv_trans _ _ _
        hleft (Q'.eqv_symm hright)
  | n + 1 => by
      have ih :=
        productTailBudget_succ_eqv
          ceiling tail n
      let count := Q'.ofNat (n + 1)
      let power := ceiling ^ (n + 1)
      let atom := power * tail
      have hfirst :
          ceiling *
              productTailBudget ceiling tail (n + 1) ≈
            count * atom := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            ceiling
            (productTailBudget ceiling tail (n + 1))
            ((Q'.ofNat (n + 1) * ceiling ^ n) * tail)
            ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              ceiling
              (Q'.ofNat (n + 1) * ceiling ^ n)
              tail)) ?_
        have hinside :
            ceiling *
                (Q'.ofNat (n + 1) * ceiling ^ n) ≈
              Q'.ofNat (n + 1) *
                (ceiling * ceiling ^ n) :=
          mul_rotate_eqv
            ceiling (Q'.ofNat (n + 1))
            (ceiling ^ n)
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ tail hinside) ?_
        exact Q'.mul_assoc_eqv
          (Q'.ofNat (n + 1))
          (ceiling * ceiling ^ n)
          tail
      have hsecond :
          tail * ceiling ^ (n + 1) ≈ atom := by
        exact Q'.mul_comm_eqv tail power
      have hsum :
          count * atom + atom ≈
            (count + 1) * atom := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left
            (count * atom) atom (1 * atom)
            (Q'.eqv_symm
              (Q'.one_mul_eqv atom))) ?_
        exact Q'.eqv_symm
          (Q'.add_mul_eqv count 1 atom)
      have hcount :
          count + 1 ≈ Q'.ofNat (n + 2) := by
        exact Q'.eqv_symm
          (YMGap.Continuum.HKConvGen.ofNat_succ_eqv
            (n + 1))
      have hclosed :
          (count + 1) * atom ≈
            (Q'.ofNat (n + 2) *
                ceiling ^ (n + 1)) * tail := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (count + 1)
            atom
            (power * tail)
            (Q'.eqv_refl _)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (count + 1)
            (Q'.ofNat (n + 2))
            (power * tail)
            hcount) ?_
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat (n + 2))
            power tail)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right
          _ _ _ hfirst)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left
            _ _ _ hsecond)
        (Q'.eqv_trans _ _ _ hsum hclosed)
        )

/-- One sign-safe product replacement step.  If the first factor changes by
at most `tail`, the remaining product by at most `error`, and the unchanged
factors are bounded by `ceiling` / `remainingCeiling`, then the whole product
changes by at most
`ceiling * error + tail * remainingCeiling`. -/
private theorem product_step_upper
    {x y X Y ceiling remainingCeiling error tail : Q'}
    (hy0 : (0 : Q') ≤ y)
    (hX0 : (0 : Q') ≤ X)
    (herror0 : (0 : Q') ≤ error)
    (htail0 : (0 : Q') ≤ tail)
    (hyCeiling : y ≤ ceiling)
    (hXCeiling : X ≤ remainingCeiling)
    (hxy : x ≤ y + tail)
    (hXY : X ≤ Y + error) :
    x * X ≤
      y * Y +
        (ceiling * error +
          tail * remainingCeiling) := by
  have hfirst :
      x * X ≤ (y + tail) * X :=
    Q'.mul_le_mul_of_nonneg_right
      x (y + tail) X hxy hX0
  have hmain :
      y * X ≤ y * Y + ceiling * error := by
    have hscale :
        y * X ≤ y * (Y + error) :=
      Q'.mul_le_mul_of_nonneg_left
        X (Y + error) y hXY hy0
    have hexpand :
        y * (Y + error) ≈
          y * Y + y * error :=
      Q'.mul_add_eqv y Y error
    have herror :
        y * error ≤ ceiling * error :=
      Q'.mul_le_mul_of_nonneg_right
        y ceiling error hyCeiling herror0
    exact Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hexpand)
        (Q'.add_le_add_left
          (y * Y) (y * error)
          (ceiling * error) herror))
  have hperturbation :
      tail * X ≤ tail * remainingCeiling :=
    Q'.mul_le_mul_of_nonneg_left
      X remainingCeiling tail
      hXCeiling htail0
  have hexpand :
      (y + tail) * X ≈
        y * X + tail * X :=
    Q'.add_mul_eqv y tail X
  have hadd :
      y * X + tail * X ≤
        (y * Y + ceiling * error) +
          tail * remainingCeiling :=
    Q'.add_le_add hmain hperturbation
  have hreassociate :
      (y * Y + ceiling * error) +
          tail * remainingCeiling ≈
        y * Y +
          (ceiling * error +
            tail * remainingCeiling) :=
    Q'.add_assoc_eqv
      (y * Y)
      (ceiling * error)
      (tail * remainingCeiling)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hexpand)
      (Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv hreassociate)))

/-- Upper finite-product truncation bound under a common nonnegative
ceiling and a common two-sided factor error. -/
theorem retainedFactorProduct_tail_upper
    {Factor : Type}
    (later base : Factor → Q')
    (ceiling tail : Q')
    (hceiling0 : (0 : Q') ≤ ceiling)
    (htail0 : (0 : Q') ≤ tail) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        (0 : Q') ≤ later factor) →
      (∀ factor, factor ∈ factors →
        (0 : Q') ≤ base factor) →
      (∀ factor, factor ∈ factors →
        later factor ≤ ceiling) →
      (∀ factor, factor ∈ factors →
        base factor ≤ ceiling) →
      (∀ factor, factor ∈ factors →
        later factor ≤ base factor + tail) →
      retainedFactorProduct later factors ≤
        retainedFactorProduct base factors +
          productTailBudget ceiling tail factors.length
  | [], _, _, _, _, _ =>
      Q'.add_le_self_of_nonneg 1 0
        (Q'.le_refl' 0)
  | factor :: rest,
      later_nonnegative,
      prefix_nonnegative,
      later_upper,
      prefix_upper,
      factor_upper => by
      change
        later factor *
            retainedFactorProduct later rest ≤
          base factor *
              retainedFactorProduct base rest +
            (ceiling *
                productTailBudget ceiling tail rest.length +
              tail * ceiling ^ rest.length)
      apply product_step_upper
      · exact prefix_nonnegative
          factor List.mem_cons_self
      · exact retainedFactorProduct_nonnegative_on
          later rest
          (fun item hitem =>
            later_nonnegative item
              (List.mem_cons_of_mem factor hitem))
      · exact productTailBudget_nonnegative
          hceiling0 htail0 rest.length
      · exact htail0
      · exact prefix_upper factor List.mem_cons_self
      · exact retainedFactorProduct_upper_on
          later ceiling hceiling0 rest
          (fun item hitem =>
            later_nonnegative item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            later_upper item
              (List.mem_cons_of_mem factor hitem))
      · exact factor_upper factor List.mem_cons_self
      · exact retainedFactorProduct_tail_upper
          later base ceiling tail
          hceiling0 htail0 rest
          (fun item hitem =>
            later_nonnegative item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            prefix_nonnegative item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            later_upper item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            prefix_upper item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            factor_upper item
              (List.mem_cons_of_mem factor hitem))

/-- Both signed finite-product differences lie below the same recursive
budget.  The reverse direction reuses the upper theorem with the two factor
families interchanged. -/
theorem retainedFactorProduct_tail_twoSided
    {Factor : Type}
    (later base : Factor → Q')
    (ceiling tail : Q')
    (hceiling0 : (0 : Q') ≤ ceiling)
    (htail0 : (0 : Q') ≤ tail)
    (factors : List Factor)
    (later_nonnegative :
      ∀ factor, factor ∈ factors →
        (0 : Q') ≤ later factor)
    (prefix_nonnegative :
      ∀ factor, factor ∈ factors →
        (0 : Q') ≤ base factor)
    (later_upper :
      ∀ factor, factor ∈ factors →
        later factor ≤ ceiling)
    (prefix_upper :
      ∀ factor, factor ∈ factors →
        base factor ≤ ceiling)
    (later_le_prefix :
      ∀ factor, factor ∈ factors →
        later factor ≤ base factor + tail)
    (prefix_le_later :
      ∀ factor, factor ∈ factors →
        base factor ≤ later factor + tail) :
    retainedFactorProduct later factors +
          -retainedFactorProduct base factors ≤
        productTailBudget ceiling tail factors.length ∧
      retainedFactorProduct base factors +
          -retainedFactorProduct later factors ≤
        productTailBudget ceiling tail factors.length := by
  exact
    ⟨Q'.sub_le_of_le_add
        (retainedFactorProduct_tail_upper
          later base ceiling tail
          hceiling0 htail0 factors
          later_nonnegative prefix_nonnegative
          later_upper prefix_upper
          later_le_prefix),
      Q'.sub_le_of_le_add
        (retainedFactorProduct_tail_upper
          base later ceiling tail
          hceiling0 htail0 factors
          prefix_nonnegative later_nonnegative
          prefix_upper later_upper
          prefix_le_later)⟩

/-! ## 2. Rational and completed spacing-product carriers -/

/-- Simultaneous finite spacing-prefix product.  The extra shift by two lets
the arbitrary-spacing prefix use the exact strong-coupling floor and ceiling
through the proved compatibility bridge. -/
def spacingFiniteFactorProduct
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (M : Nat) : Q' :=
  retainedFactorProduct
    (fun factor =>
      spacingPointwiseHeatPartial
        w (coordinate factor) (2 + M))
    factors

/-- Product of the corresponding completed spacing-dependent pointwise heat
factors. -/
def spacingCompletedFactorProduct
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q')) :
    CReal :=
  completedFactorProduct
    (fun factor =>
      pointwiseHeatCReal
        hw0
        (Q'.lt_of_le_of_lt hw (by decide))
        (coordinate_lower factor)
        (coordinate_upper factor))
    factors

/-- Approximating a completed finite product is exactly the rational product
of the factor approximations. -/
@[simp] theorem completedFactorProduct_approx
    {Factor : Type}
    (value : Factor → CReal) :
    ∀ factors : List Factor, ∀ n : Nat,
      (completedFactorProduct value factors).approx n =
        retainedFactorProduct
          (fun factor => (value factor).approx n)
          factors
  | [], _ => rfl
  | _ :: rest, n => by
      change
        _ * (completedFactorProduct value rest).approx n =
          _ * retainedFactorProduct
            (fun factor => (value factor).approx n)
            rest
      rw [completedFactorProduct_approx value rest n]

/-- Every twice-shifted spacing prefix inherits the exact all-label floor. -/
theorem allLabelHaarFloor_le_spacingPrefix
    {w x : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    allLabelHaarFloor ≤
      spacingPointwiseHeatPartial w x (2 + M) := by
  have hdisplayed :
      allLabelHaarFloor ≤
        pointwiseHeatPartial
          w x (spacingLabelCutoff w + M) :=
    allLabelHaarFloor_le_pointwiseHeatPartial
      (Q'.le_of_lt hw0) hw hxLower hxUpper
      (spacingLabelCutoff w + M)
  exact Q'.le_trans' _ _ _ hdisplayed
    (Q'.ge_of_eqv
      (spacingPointwiseHeatPartial_two_add_eqv
        w x M))

/-- Every twice-shifted spacing prefix inherits the exact all-label ceiling. -/
theorem spacingPrefix_le_allLabelHaarCeiling
    {w x : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    spacingPointwiseHeatPartial w x (2 + M) ≤
      allLabelHaarCeiling := by
  have hdisplayed :
      pointwiseHeatPartial
          w x (spacingLabelCutoff w + M) ≤
        allLabelHaarCeiling :=
    pointwiseHeatPartial_le_allLabelHaarCeiling
      (Q'.le_of_lt hw0) hw hxLower hxUpper
      (spacingLabelCutoff w + M)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (spacingPointwiseHeatPartial_two_add_eqv
        w x M))
    hdisplayed

/-- The new one-factor semantic spacing-tail corridor, specialized at the
twice-shifted prefix used by the product carrier. -/
def spacingFactorSemanticTailCorridor
    {Factor : Type}
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (factor : Factor) (M : Nat) :
    SemanticSpacingTailCorridor
      (pointwiseHeatCReal
        hw0
        (Q'.lt_of_le_of_lt hw (by decide))
        (coordinate_lower factor)
        (coordinate_upper factor))
      w (coordinate factor) (2 + M) :=
  semanticSpacingTailCorridor
    hw0
    (Q'.lt_of_le_of_lt hw (by decide))
    (coordinate_lower factor)
    (coordinate_upper factor)
    (2 + M)

/-! ## 3. Semantic completed-product truncation corridor -/

/-- The completed spacing-product lies below the simultaneous finite prefix
product plus the explicit recursive product-tail budget. -/
theorem spacingCompletedFactorProduct_le_finite_add_tail
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    CReal.leRat
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      (spacingFiniteFactorProduct
          factors w coordinate M +
        productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length) := by
  apply CReal.leRat_of_eventually
  refine ⟨2 + M, fun p hp => ?_⟩
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hp
  unfold spacingCompletedFactorProduct
  rw [completedFactorProduct_approx]
  simp only [pointwiseHeatCReal_approx]
  unfold spacingFiniteFactorProduct
  apply retainedFactorProduct_tail_upper
    (fun factor =>
      spacingPointwiseHeatPartial
        w (coordinate factor) ((2 + M) + L))
    (fun factor =>
      spacingPointwiseHeatPartial
        w (coordinate factor) (2 + M))
    allLabelHaarCeiling
    (spacingClosedTail w (2 + M))
    (Q'.le_of_lt allLabelHaarCeiling_pos)
    (spacingClosedTail_nonnegative hw0 (2 + M))
    factors
  · intro factor hfactor
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt allLabelHaarFloor_pos)
      (by
        rw [Nat.add_assoc]
        exact allLabelHaarFloor_le_spacingPrefix
          hw0 hw
          (coordinate_lower factor)
          (coordinate_upper factor)
          (M + L))
  · intro factor hfactor
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt allLabelHaarFloor_pos)
      (allLabelHaarFloor_le_spacingPrefix
        hw0 hw
        (coordinate_lower factor)
        (coordinate_upper factor)
        M)
  · intro factor hfactor
    rw [Nat.add_assoc]
    exact spacingPrefix_le_allLabelHaarCeiling
      hw0 hw
      (coordinate_lower factor)
      (coordinate_upper factor)
      (M + L)
  · intro factor hfactor
    exact spacingPrefix_le_allLabelHaarCeiling
      hw0 hw
      (coordinate_lower factor)
      (coordinate_upper factor)
      M
  · intro factor hfactor
    exact spacingPointwiseHeatPartial_block_upper
      hw0
      (Q'.lt_of_le_of_lt hw (by decide))
      (coordinate_lower factor)
      (coordinate_upper factor)
      (2 + M) L

/-- The simultaneous finite prefix product minus the same budget lies below
the completed spacing-product. -/
theorem finite_sub_tail_le_spacingCompletedFactorProduct
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    ExpPos.geRat
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      (spacingFiniteFactorProduct
          factors w coordinate M +
        -productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨2 + M, fun p hp => ?_⟩
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hp
  unfold spacingCompletedFactorProduct
  rw [completedFactorProduct_approx]
  simp only [pointwiseHeatCReal_approx]
  unfold spacingFiniteFactorProduct
  have hlower :
      retainedFactorProduct
          (fun factor =>
            spacingPointwiseHeatPartial
              w (coordinate factor) (2 + M))
          factors ≤
        retainedFactorProduct
            (fun factor =>
              spacingPointwiseHeatPartial
                w (coordinate factor) ((2 + M) + L))
            factors +
          productTailBudget
            allLabelHaarCeiling
            (spacingClosedTail w (2 + M))
            factors.length := by
    apply retainedFactorProduct_tail_upper
      (fun factor =>
        spacingPointwiseHeatPartial
          w (coordinate factor) (2 + M))
      (fun factor =>
        spacingPointwiseHeatPartial
          w (coordinate factor) ((2 + M) + L))
      allLabelHaarCeiling
      (spacingClosedTail w (2 + M))
      (Q'.le_of_lt allLabelHaarCeiling_pos)
      (spacingClosedTail_nonnegative hw0 (2 + M))
      factors
    · intro factor hfactor
      exact Q'.le_trans' _ _ _
        (Q'.le_of_lt allLabelHaarFloor_pos)
        (allLabelHaarFloor_le_spacingPrefix
          hw0 hw
          (coordinate_lower factor)
          (coordinate_upper factor)
          M)
    · intro factor hfactor
      exact Q'.le_trans' _ _ _
        (Q'.le_of_lt allLabelHaarFloor_pos)
        (by
          rw [Nat.add_assoc]
          exact allLabelHaarFloor_le_spacingPrefix
            hw0 hw
            (coordinate_lower factor)
            (coordinate_upper factor)
            (M + L))
    · intro factor hfactor
      exact spacingPrefix_le_allLabelHaarCeiling
        hw0 hw
        (coordinate_lower factor)
        (coordinate_upper factor)
        M
    · intro factor hfactor
      rw [Nat.add_assoc]
      exact spacingPrefix_le_allLabelHaarCeiling
        hw0 hw
        (coordinate_lower factor)
        (coordinate_upper factor)
        (M + L)
    · intro factor hfactor
      exact spacingPointwiseHeatPartial_block_lower
        hw0
        (Q'.lt_of_le_of_lt hw (by decide))
        (coordinate_lower factor)
        (coordinate_upper factor)
        (2 + M) L
  have hcomm :
      retainedFactorProduct
          (fun factor =>
            spacingPointwiseHeatPartial
              w (coordinate factor) (2 + M))
          factors ≤
        productTailBudget
            allLabelHaarCeiling
            (spacingClosedTail w (2 + M))
            factors.length +
          retainedFactorProduct
            (fun factor =>
              spacingPointwiseHeatPartial
                w (coordinate factor) ((2 + M) + L))
            factors :=
    Q'.le_trans' _ _ _ hlower
      (Q'.le_of_eqv
        (Q'.add_comm_eqv _ _))
  exact Q'.sub_le_of_le_add hcomm

/-- Type-level aggregate certificate: local semantic corridors together
with the quantitative product semantic corridor. -/
structure SpacingCompletedProductTailCertificate
    {Factor : Type}
    (factors : List Factor)
    (factorValue : Factor → CReal)
    (productValue : CReal)
    (w : Q') (coordinate : Factor → Q')
    (M : Nat) : Type where
  factorCorridor :
    ∀ factor, factor ∈ factors →
      SemanticSpacingTailCorridor
        (factorValue factor)
        w (coordinate factor) (2 + M)
  lower :
    ExpPos.geRat productValue
      (spacingFiniteFactorProduct
          factors w coordinate M +
        -productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length)
  upper :
    CReal.leRat productValue
      (spacingFiniteFactorProduct
          factors w coordinate M +
        productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length)

/-- Construct the aggregate certificate.  Its local component is exactly the
semantic one-factor spacing corridor proved in the preceding module. -/
def spacingCompletedProductTailCertificate
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    SpacingCompletedProductTailCertificate
      factors
      (fun factor =>
        pointwiseHeatCReal
          hw0
          (Q'.lt_of_le_of_lt hw (by decide))
          (coordinate_lower factor)
          (coordinate_upper factor))
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      w coordinate M where
  factorCorridor := by
    intro factor hfactor
    exact spacingFactorSemanticTailCorridor
      w coordinate hw0 hw
      coordinate_lower coordinate_upper
      factor M
  lower :=
    finite_sub_tail_le_spacingCompletedFactorProduct
      factors w coordinate hw0 hw
      coordinate_lower coordinate_upper M
  upper :=
    spacingCompletedFactorProduct_le_finite_add_tail
      factors w coordinate hw0 hw
      coordinate_lower coordinate_upper M

/-! ## 4. Exact literal 23-factor coefficient -/

/-- Closed `n=23` perturbation coefficient.  Parentheses record the literal
`23 * ceiling^22 * tail` carrier. -/
def bf4ProductTail (tail : Q') : Q' :=
  (Q'.ofNat 23 * allLabelHaarCeiling ^ 22) * tail

/-- The recursive error budget on the literal BF4 carrier is exactly
`23 * ceiling^22 * tail`; no safety-factor enlargement is used. -/
theorem productTailBudget_bf4_eqv (tail : Q') :
    productTailBudget
        allLabelHaarCeiling tail
        bf4SpatialCycleCount ≈
      bf4ProductTail tail := by
  simpa [bf4SpatialCycleCount, bf4ProductTail] using
    (productTailBudget_succ_eqv
      allLabelHaarCeiling tail 22)

/-- Exact BF4 completed-product upper truncation bound. -/
theorem spacingCompletedBF4Product_le_finite_add_tail
    {Factor : Type}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    CReal.leRat
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      (spacingFiniteFactorProduct
          factors w coordinate M +
        bf4ProductTail
          (spacingClosedTail w (2 + M))) := by
  have hgeneric :=
    spacingCompletedFactorProduct_le_finite_add_tail
      factors w coordinate hw0 hw
      coordinate_lower coordinate_upper M
  have hbudget :
      productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length ≈
        bf4ProductTail
          (spacingClosedTail w (2 + M)) := by
    rw [factor_count]
    exact productTailBudget_bf4_eqv
      (spacingClosedTail w (2 + M))
  exact CReal.leRat_mono hgeneric
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_left
        (spacingFiniteFactorProduct
          factors w coordinate M)
        _
        _
        hbudget))

/-- Exact BF4 completed-product lower truncation bound. -/
theorem finite_sub_tail_le_spacingCompletedBF4Product
    {Factor : Type}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    ExpPos.geRat
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      (spacingFiniteFactorProduct
          factors w coordinate M +
        -bf4ProductTail
          (spacingClosedTail w (2 + M))) := by
  have hgeneric :=
    finite_sub_tail_le_spacingCompletedFactorProduct
      factors w coordinate hw0 hw
      coordinate_lower coordinate_upper M
  have hbudget :
      productTailBudget
          allLabelHaarCeiling
          (spacingClosedTail w (2 + M))
          factors.length ≈
        bf4ProductTail
          (spacingClosedTail w (2 + M)) := by
    rw [factor_count]
    exact productTailBudget_bf4_eqv
      (spacingClosedTail w (2 + M))
  have hbound :
      spacingFiniteFactorProduct
            factors w coordinate M +
          -bf4ProductTail
            (spacingClosedTail w (2 + M)) ≤
        spacingFiniteFactorProduct
            factors w coordinate M +
          -productTailBudget
            allLabelHaarCeiling
            (spacingClosedTail w (2 + M))
            factors.length :=
    Q'.le_of_eqv
      (Q'.add_eqv_congr_left
        (spacingFiniteFactorProduct
          factors w coordinate M)
        _
        _
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_symm hbudget)))
  exact ExpPos.geRat_mono hgeneric hbound

/-- The exact literal BF4 semantic product corridor. -/
structure BF4SpacingCompletedProductTailCorridor
    (value : CReal)
    {Factor : Type}
    (factors : List Factor)
    (w : Q') (coordinate : Factor → Q')
    (M : Nat) : Type where
  lower :
    ExpPos.geRat value
      (spacingFiniteFactorProduct
          factors w coordinate M +
        -bf4ProductTail
          (spacingClosedTail w (2 + M)))
  upper :
    CReal.leRat value
      (spacingFiniteFactorProduct
          factors w coordinate M +
        bf4ProductTail
          (spacingClosedTail w (2 + M)))

/-- Construct the exact 23-factor semantic corridor. -/
def bf4SpacingCompletedProductTailCorridor
    {Factor : Type}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q') (coordinate : Factor → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ factor, (-(1 : Q')) ≤ coordinate factor)
    (coordinate_upper :
      ∀ factor, coordinate factor ≤ (1 : Q'))
    (M : Nat) :
    BF4SpacingCompletedProductTailCorridor
      (spacingCompletedFactorProduct
        factors w coordinate hw0 hw
        coordinate_lower coordinate_upper)
      factors w coordinate M where
  lower :=
    finite_sub_tail_le_spacingCompletedBF4Product
      factors factor_count w coordinate
      hw0 hw coordinate_lower coordinate_upper M
  upper :=
    spacingCompletedBF4Product_le_finite_add_tail
      factors factor_count w coordinate
      hw0 hw coordinate_lower coordinate_upper M

/-! ## Axiom gates -/

#print axioms productTailBudget_nonnegative
#print axioms productTailBudget_succ_eqv
#print axioms retainedFactorProduct_tail_upper
#print axioms retainedFactorProduct_tail_twoSided
#print axioms completedFactorProduct_approx
#print axioms allLabelHaarFloor_le_spacingPrefix
#print axioms spacingPrefix_le_allLabelHaarCeiling
#print axioms spacingFactorSemanticTailCorridor
#print axioms spacingCompletedFactorProduct_le_finite_add_tail
#print axioms finite_sub_tail_le_spacingCompletedFactorProduct
#print axioms spacingCompletedProductTailCertificate
#print axioms productTailBudget_bf4_eqv
#print axioms spacingCompletedBF4Product_le_finite_add_tail
#print axioms finite_sub_tail_le_spacingCompletedBF4Product
#print axioms bf4SpacingCompletedProductTailCorridor

end YMGap.Continuum.BF4CompletedProductTailBound
