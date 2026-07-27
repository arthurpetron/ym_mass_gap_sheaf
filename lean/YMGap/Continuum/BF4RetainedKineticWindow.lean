/-
# Retained-path kinetic windows imply potential-free BF4 Harnack order

`BF4RetainedPathConditionalOrder` identifies the useful Yang--Mills input:
compare source rows before the complete interior path is integrated out.
This file packages the smallest pointwise certificate that supplies that
comparison.

If every retained kinetic weight on the selected finite rectangle obeys

    lower <= kinetic(source,target,path) <= upper

with `0 < lower` and `upper <= spread * lower`, then any two source rows
obey the symmetric pathwise order with the same `spread`.  Consequently the
full nonconstant Feynman--Kac potential can be conditionally integrated with
no potential-oscillation loss, by the already-proved retained-path theorem.

The BF4 specialization uses the exact arithmetic constants

    lower  = (1055/2272)^23,
    upper  = (3489/2272)^23,
    spread = (3489/1055)^23.

Honest scope: this theorem consumes retained-path bounds.  It does not infer
them from an aggregate grouped-kernel window; that implication is false.
Nor does it identify the abstract retained weights with the physical BF4
all-label slab.

## Axiom gate

Constructive `Q'` order only.  No `Classical.*`, `Real`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4RetainedPathConditionalOrder

namespace YMGap.Continuum.BF4RetainedKineticWindow

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.GroupedAllLabelHaarRefresh

/-! ## 0. Finite products of retained local factors -/

/-- Product of local kinetic factors on a retained factor list. -/
def retainedFactorProduct {Factor : Type}
    (value : Factor → Q') : List Factor → Q'
  | [] => 1
  | factor :: tail =>
      value factor * retainedFactorProduct value tail

/-- Products of nonnegative retained factors are nonnegative. -/
theorem retainedFactorProduct_nonnegative
    {Factor : Type} (value : Factor → Q')
    (value_nonnegative :
      ∀ factor, (0 : Q') ≤ value factor) :
    ∀ factors : List Factor,
      (0 : Q') ≤ retainedFactorProduct value factors
  | [] => Q'.zero_le_one
  | factor :: tail =>
      Q'.mul_nonneg _ _
        (value_nonnegative factor)
        (retainedFactorProduct_nonnegative
          value value_nonnegative tail)

/-- Membership-aware nonnegativity of a retained factor product. -/
theorem retainedFactorProduct_nonnegative_on
    {Factor : Type} (value : Factor → Q') :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        (0 : Q') ≤ value factor) →
        (0 : Q') ≤ retainedFactorProduct value factors
  | [], _ => Q'.zero_le_one
  | factor :: tail, value_nonnegative =>
      Q'.mul_nonneg _ _
        (value_nonnegative factor List.mem_cons_self)
        (retainedFactorProduct_nonnegative_on
          value tail
          (fun item hitem =>
            value_nonnegative item
              (List.mem_cons_of_mem factor hitem)))

/-- A common nonnegative local floor tensorizes over the retained factor
list. -/
theorem retainedFactorProduct_lower
    {Factor : Type} (value : Factor → Q') (lower : Q')
    (lower_nonnegative : (0 : Q') ≤ lower)
    (lower_bound : ∀ factor, lower ≤ value factor) :
    ∀ factors : List Factor,
      lower ^ factors.length ≤
        retainedFactorProduct value factors
  | [] => Q'.le_refl' 1
  | factor :: tail => by
      change
        lower * lower ^ tail.length ≤
          value factor *
            retainedFactorProduct value tail
      have hvalue_nonnegative : (0 : Q') ≤ value factor :=
        Q'.le_trans' _ _ _
          lower_nonnegative (lower_bound factor)
      exact Q'.mul_le_mul_of_nonneg
        (lower_bound factor)
        (retainedFactorProduct_lower
          value lower lower_nonnegative lower_bound tail)
        hvalue_nonnegative
        (Q'.pow_nonneg lower lower_nonnegative tail.length)

/-- A common nonnegative local ceiling tensorizes over the retained factor
list. -/
theorem retainedFactorProduct_upper
    {Factor : Type} (value : Factor → Q') (upper : Q')
    (value_nonnegative :
      ∀ factor, (0 : Q') ≤ value factor)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (upper_bound : ∀ factor, value factor ≤ upper) :
    ∀ factors : List Factor,
      retainedFactorProduct value factors ≤
        upper ^ factors.length
  | [] => Q'.le_refl' 1
  | factor :: tail => by
      change
        value factor *
            retainedFactorProduct value tail ≤
          upper * upper ^ tail.length
      exact Q'.mul_le_mul_of_nonneg
        (upper_bound factor)
        (retainedFactorProduct_upper
          value upper value_nonnegative
          upper_nonnegative upper_bound tail)
        upper_nonnegative
        (retainedFactorProduct_nonnegative
          value value_nonnegative tail)

/-- Membership-aware form of the local-floor product theorem. -/
theorem retainedFactorProduct_lower_on
    {Factor : Type} (value : Factor → Q') (lower : Q')
    (lower_nonnegative : (0 : Q') ≤ lower) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors → lower ≤ value factor) →
        lower ^ factors.length ≤
          retainedFactorProduct value factors
  | [], _ => Q'.le_refl' 1
  | factor :: tail, lower_bound => by
      change
        lower * lower ^ tail.length ≤
          value factor *
            retainedFactorProduct value tail
      have hhead :
          lower ≤ value factor :=
        lower_bound factor List.mem_cons_self
      have htail :
          ∀ item, item ∈ tail → lower ≤ value item :=
        fun item hitem =>
          lower_bound item
            (List.mem_cons_of_mem factor hitem)
      have hvalue_nonnegative : (0 : Q') ≤ value factor :=
        Q'.le_trans' _ _ _ lower_nonnegative hhead
      exact Q'.mul_le_mul_of_nonneg
        hhead
        (retainedFactorProduct_lower_on
          value lower lower_nonnegative tail htail)
        hvalue_nonnegative
        (Q'.pow_nonneg lower lower_nonnegative tail.length)

/-- Membership-aware form of the local-ceiling product theorem. -/
theorem retainedFactorProduct_upper_on
    {Factor : Type} (value : Factor → Q') (upper : Q')
    (upper_nonnegative : (0 : Q') ≤ upper) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        (0 : Q') ≤ value factor) →
      (∀ factor, factor ∈ factors →
        value factor ≤ upper) →
        retainedFactorProduct value factors ≤
          upper ^ factors.length
  | [], _, _ => Q'.le_refl' 1
  | factor :: tail, value_nonnegative, upper_bound => by
      change
        value factor *
            retainedFactorProduct value tail ≤
          upper * upper ^ tail.length
      exact Q'.mul_le_mul_of_nonneg
        (upper_bound factor List.mem_cons_self)
        (retainedFactorProduct_upper_on
          value upper upper_nonnegative tail
          (fun item hitem =>
            value_nonnegative item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            upper_bound item
              (List.mem_cons_of_mem factor hitem)))
        upper_nonnegative
        (retainedFactorProduct_nonnegative_on
          value tail
          (fun item hitem =>
            value_nonnegative item
              (List.mem_cons_of_mem factor hitem)))

/-! ## 1. Generic retained-window constructor -/

/-- A strictly positive retained kinetic window gives the symmetric
pathwise Harnack order required before conditional path integration. -/
def retainedKineticHarnackOfWindow
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (sources : List Source) (targets : List Target)
    (lower upper spread : Q')
    (lower_pos : (0 : Q') < lower)
    (one_le_spread : (1 : Q') ≤ spread)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            lower ≤ kineticWeight source target path)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            kineticWeight source target path ≤ upper)
    (upper_le_spread_lower :
      upper ≤ spread * lower) :
    RetainedKineticHarnackData
      paths kineticWeight sources targets where
  spread := spread
  one_le_spread := one_le_spread
  kinetic_nonnegative := by
    intro source hsource target htarget path hpath
    exact Q'.le_trans' _ _ _
      (Q'.le_of_lt lower_pos)
      (lower_bound source hsource target htarget path hpath)
  pathwiseDomination := by
    intro first hfirst second hsecond target htarget path hpath
    have hspread_nonnegative : (0 : Q') ≤ spread :=
      Q'.le_trans' _ _ _ Q'.zero_le_one one_le_spread
    have hscaled :
        spread * lower ≤
          spread * kineticWeight second target path :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (lower_bound second hsecond target htarget path hpath)
        hspread_nonnegative
    exact Q'.le_trans' _ _ _
      (upper_bound first hfirst target htarget path hpath)
      (Q'.le_trans' _ _ _ upper_le_spread_lower hscaled)

/-! ## 2. Exact BF4 retained-window specialization -/

/-- Package verified retained-path BF4 bounds into the potential-free
Harnack datum with exact spread `(3489/1055)^23`. -/
def bf4RetainedKineticHarnackOfBounds
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (sources : List Source) (targets : List Target)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            bf4KineticFloor ≤
              kineticWeight source target path)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            kineticWeight source target path ≤
              bf4KineticCeiling) :
    RetainedKineticHarnackData
      paths kineticWeight sources targets :=
  retainedKineticHarnackOfWindow
    paths kineticWeight sources targets
    bf4KineticFloor bf4KineticCeiling bf4KineticSpread
    bf4KineticFloor_pos
    bf4KineticSpread_one_le
    lower_bound upper_bound
    bf4KineticCeiling_le_spread_floor

/-- A literal product of 23 retained local factors inherits the BF4 Harnack
datum once every local factor lies in the all-label corridor
`[1055/2272, 3489/2272]`.  This isolates the remaining physical task as a
factorization identity plus two local pointwise inequalities. -/
def bf4RetainedProductKineticHarnackOfLocalBounds
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (localWeight :
      Source → Target → List State → Factor → Q')
    (sources : List Source) (targets : List Target)
    (local_lower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              allLabelHaarFloor ≤
                localWeight source target path factor)
    (local_upper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              localWeight source target path factor ≤
                allLabelHaarCeiling) :
    RetainedKineticHarnackData
      paths
      (fun source target path =>
        retainedFactorProduct
          (localWeight source target path) factors)
      sources targets :=
  bf4RetainedKineticHarnackOfBounds
    paths
    (fun source target path =>
      retainedFactorProduct
        (localWeight source target path) factors)
    sources targets
    (by
      intro source hsource target htarget path hpath
      have hproduct :=
        retainedFactorProduct_lower_on
          (localWeight source target path)
          allLabelHaarFloor
          (Q'.le_of_lt allLabelHaarFloor_pos)
          factors
          (fun factor hfactor =>
            local_lower source hsource
              target htarget path hpath factor
              hfactor)
      rw [factor_count] at hproduct
      simpa only [bf4KineticFloor] using hproduct)
    (by
      intro source hsource target htarget path hpath
      have hproduct :=
        retainedFactorProduct_upper_on
          (localWeight source target path)
          allLabelHaarCeiling
          (Q'.le_of_lt allLabelHaarCeiling_pos)
          factors
          (fun factor hfactor =>
            Q'.le_trans' _ _ _
              (Q'.le_of_lt allLabelHaarFloor_pos)
              (local_lower source hsource
                target htarget path hpath factor
                hfactor))
          (fun factor hfactor =>
            local_upper source hsource
              target htarget path hpath factor
              hfactor)
      rw [factor_count] at hproduct
      simpa only [bf4KineticCeiling] using hproduct)

theorem bf4RetainedKineticHarnackOfBounds_spread
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (sources : List Source) (targets : List Target)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            bf4KineticFloor ≤
              kineticWeight source target path)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            kineticWeight source target path ≤
              bf4KineticCeiling) :
    (bf4RetainedKineticHarnackOfBounds
      paths kineticWeight sources targets
      lower_bound upper_bound).spread =
        bf4KineticSpread :=
  rfl

/-! ## 3. Direct Feynman--Kac consumer -/

/-- **Spacing-uniform order, conditional on retained BF4 bounds.**  Once the
physical retained kinetic weights satisfy the exact BF4 window, every
nonnegative interior spatial potential passes through conditional integration
with spread `(3489/1055)^23` and no factor depending on path length. -/
theorem bf4FeynmanKac_of_retainedWindow
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            bf4KineticFloor ≤
              kineticWeight source target path)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            kineticWeight source target path ≤
              bf4KineticCeiling)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    feynmanKacPathKernel
        paths kineticWeight potential first target ≤
      bf4KineticSpread *
        feynmanKacPathKernel
          paths kineticWeight potential second target := by
  exact feynmanKac_of_retainedKineticDomination
    paths kineticWeight potential sources targets
    (bf4RetainedKineticHarnackOfBounds
      paths kineticWeight sources targets
      lower_bound upper_bound)
    potential_nonnegative
    first hfirst second hsecond target htarget

end YMGap.Continuum.BF4RetainedKineticWindow

#print axioms YMGap.Continuum.BF4RetainedKineticWindow.retainedFactorProduct_lower_on
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.retainedFactorProduct_upper_on
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.retainedKineticHarnackOfWindow
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.bf4RetainedKineticHarnackOfBounds
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.bf4RetainedProductKineticHarnackOfLocalBounds
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.bf4RetainedKineticHarnackOfBounds_spread
#print axioms YMGap.Continuum.BF4RetainedKineticWindow.bf4FeynmanKac_of_retainedWindow
