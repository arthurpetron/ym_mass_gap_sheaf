/-
# Completed one-factor heat corridors imply retained BF4 order

This module is the constructive-real downstream consumer for a completed
one-factor pointwise heat kernel.  Its input is deliberately minimal: each of
the 23 retained factors is a `CReal` whose limit lies in the sound corridor

    1055/2272 <= factor <= 3489/2272

expressed by `ExpPos.geRat` and `CReal.leRat`.  The finite product then lies in

    (1055/2272)^23 <= product <= (3489/2272)^23

and any two retained source rows obey the projective order

    product(first) <= (3489/1055)^23 * product(second)

in the transitive eventual order `CReal.leEv`.

Honest scope: no completed heat kernel is constructed here, and no abstract
factor is identified with an interacting physical BF4 slab factor.  The theorem
only consumes a completed one-factor corridor and a literal 23-factor
factorization.

## Axiom gate

Constructive `CReal` order and exact `Q'` arithmetic only.  No `Classical.*`,
`Real`, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4RetainedKineticWindow
import YMGap.Continuum.BlockSpinModel

namespace YMGap.Continuum.BF4CompletedHeatRetainedConsumer

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh

/-! ## 1. Completed one-factor corridor and finite products -/

/-- The sound rational corridor carried by one completed pointwise heat
factor.  Both fields concern the limit of the `CReal`, not a selected
approximation. -/
structure CompletedOneFactorHeatCorridor (value : CReal) : Type where
  lower : ExpPos.geRat value allLabelHaarFloor
  upper : CReal.leRat value allLabelHaarCeiling

/-- Left-folded finite product of completed heat factors. -/
def completedFactorProduct {Factor : Type}
    (value : Factor → CReal) : List Factor → CReal
  | [] => CReal.ofQ' (1 : Q')
  | factor :: tail =>
      CReal.mul (value factor) (completedFactorProduct value tail)

private theorem geRat_ofQ'_self (q : Q') :
    ExpPos.geRat (CReal.ofQ' q) q :=
  ExpPos.geRat_of_eventually
    ⟨0, fun _ _ => Q'.le_refl' q⟩

private theorem leEv_of_leRat
    {value : CReal} {upper : Q'}
    (h : CReal.leRat value upper) :
    CReal.leEv value (CReal.ofQ' upper) := by
  intro ε hε
  exact h ε hε

private theorem leEv_of_geRat
    {value : CReal} {lower : Q'}
    (h : ExpPos.geRat value lower) :
    CReal.leEv (CReal.ofQ' lower) value := by
  intro ε hε
  exact h ε hε

private theorem completedFactorProduct_nonnegative_on
    {Factor : Type} (value : Factor → CReal) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        ExpPos.geRat (value factor) 0) →
      ExpPos.geRat (completedFactorProduct value factors) 0
  | [], _ =>
      ExpPos.geRat_mono
        (geRat_ofQ'_self 1)
        Q'.zero_le_one
  | factor :: tail, factor_nonnegative =>
      CReal.mul_nonneg
        (factor_nonnegative factor List.mem_cons_self)
        (completedFactorProduct_nonnegative_on
          value tail
          (fun item hitem =>
            factor_nonnegative item
              (List.mem_cons_of_mem factor hitem)))

/-- A common nonnegative completed-factor floor tensorizes over a finite
factor list. -/
theorem completedFactorProduct_lower_on
    {Factor : Type} (value : Factor → CReal) (lower : Q')
    (lower_nonnegative : (0 : Q') ≤ lower) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        ExpPos.geRat (value factor) lower) →
      ExpPos.geRat
        (completedFactorProduct value factors)
        (lower ^ factors.length)
  | [], _ => geRat_ofQ'_self 1
  | factor :: tail, lower_bound => by
      change
        ExpPos.geRat
          (CReal.mul
            (value factor)
            (completedFactorProduct value tail))
          (lower * lower ^ tail.length)
      have hhead :
          ExpPos.geRat (value factor) lower :=
        lower_bound factor List.mem_cons_self
      have htail :
          ExpPos.geRat
            (completedFactorProduct value tail)
            (lower ^ tail.length) :=
        completedFactorProduct_lower_on
          value lower lower_nonnegative tail
          (fun item hitem =>
            lower_bound item
              (List.mem_cons_of_mem factor hitem))
      have htail_nonnegative :
          ExpPos.geRat
            (completedFactorProduct value tail) 0 :=
        ExpPos.geRat_mono htail
          (Q'.pow_nonneg lower lower_nonnegative tail.length)
      exact YMGap.Continuum.geRat_mul
        lower_nonnegative hhead htail htail_nonnegative

/-- A common nonnegative completed-factor ceiling tensorizes over a finite
factor list. -/
theorem completedFactorProduct_upper_on
    {Factor : Type} (value : Factor → CReal)
    (lower upper : Q')
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        ExpPos.geRat (value factor) lower) →
      (∀ factor, factor ∈ factors →
        CReal.leRat (value factor) upper) →
      CReal.leRat
        (completedFactorProduct value factors)
        (upper ^ factors.length)
  | [], _, _ =>
      CReal.leRat_ofQ' (Q'.le_refl' 1)
  | factor :: tail, lower_bound, upper_bound => by
      change
        CReal.leRat
          (CReal.mul
            (value factor)
            (completedFactorProduct value tail))
          (upper * upper ^ tail.length)
      have hhead_nonnegative :
          ExpPos.geRat (value factor) 0 :=
        ExpPos.geRat_mono
          (lower_bound factor List.mem_cons_self)
          lower_nonnegative
      have htail_lower :
          ExpPos.geRat
            (completedFactorProduct value tail)
            (lower ^ tail.length) :=
        completedFactorProduct_lower_on
          value lower lower_nonnegative tail
          (fun item hitem =>
            lower_bound item
              (List.mem_cons_of_mem factor hitem))
      have htail_nonnegative :
          ExpPos.geRat
            (completedFactorProduct value tail) 0 :=
        ExpPos.geRat_mono htail_lower
          (Q'.pow_nonneg lower lower_nonnegative tail.length)
      exact CReal.leRat_mul
        (upper_bound factor List.mem_cons_self)
        (completedFactorProduct_upper_on
          value lower upper
          lower_nonnegative upper_nonnegative
          tail
          (fun item hitem =>
            lower_bound item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            upper_bound item
              (List.mem_cons_of_mem factor hitem)))
        hhead_nonnegative
        htail_nonnegative
        upper_nonnegative
        (Q'.pow_nonneg upper upper_nonnegative tail.length)

/-! ## 2. Exact completed BF4 product window -/

/-- A literal 23-factor product of completed one-factor heat kernels inherits
the exact BF4 lower floor. -/
theorem completedBF4Product_lower
    {Factor : Type}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (value : Factor → CReal)
    (corridor :
      ∀ factor, factor ∈ factors →
        CompletedOneFactorHeatCorridor (value factor)) :
    ExpPos.geRat
      (completedFactorProduct value factors)
      bf4KineticFloor := by
  have h :=
    completedFactorProduct_lower_on
      value allLabelHaarFloor
      (Q'.le_of_lt allLabelHaarFloor_pos)
      factors
      (fun factor hfactor =>
        (corridor factor hfactor).lower)
  rw [factor_count] at h
  simpa only [bf4KineticFloor] using h

/-- A literal 23-factor product of completed one-factor heat kernels inherits
the exact BF4 upper ceiling. -/
theorem completedBF4Product_upper
    {Factor : Type}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (value : Factor → CReal)
    (corridor :
      ∀ factor, factor ∈ factors →
        CompletedOneFactorHeatCorridor (value factor)) :
    CReal.leRat
      (completedFactorProduct value factors)
      bf4KineticCeiling := by
  have h :=
    completedFactorProduct_upper_on
      value allLabelHaarFloor allLabelHaarCeiling
      (Q'.le_of_lt allLabelHaarFloor_pos)
      (Q'.le_of_lt allLabelHaarCeiling_pos)
      factors
      (fun factor hfactor =>
        (corridor factor hfactor).lower)
      (fun factor hfactor =>
        (corridor factor hfactor).upper)
  rw [factor_count] at h
  simpa only [bf4KineticCeiling] using h

private theorem constantBF4Window_order :
    CReal.leEv
      (CReal.ofQ' bf4KineticCeiling)
      (CReal.ofQ'
        (bf4KineticSpread * bf4KineticFloor)) := by
  intro ε hε
  refine ⟨0, fun _ _ => ?_⟩
  exact Q'.le_trans' _ _ _
    bf4KineticCeiling_le_spread_floor
    (Q'.add_le_self_of_nonneg
      (bf4KineticSpread * bf4KineticFloor)
      ε (Q'.le_of_lt hε))

/-- The completed BF4 floor and ceiling imply the same projective order as
the rational retained-path theorem. -/
theorem completedBF4Window_order
    {first second : CReal}
    (first_upper :
      CReal.leRat first bf4KineticCeiling)
    (second_lower :
      ExpPos.geRat second bf4KineticFloor) :
    CReal.leEv first
      (CReal.mul
        (CReal.ofQ' bf4KineticSpread)
        second) := by
  have hscaled :
      ExpPos.geRat
        (CReal.mul
          (CReal.ofQ' bf4KineticSpread)
          second)
        (bf4KineticSpread * bf4KineticFloor) :=
    YMGap.Constructive.SU3CharFactor.geRat_smul_nonneg
      (Q'.le_trans' _ _ _
        Q'.zero_le_one bf4KineticSpread_one_le)
      second_lower
  exact CReal.leEv_trans
    (CReal.leEv_trans
      (leEv_of_leRat first_upper)
      constantBF4Window_order)
    (leEv_of_geRat hscaled)

/-! ## 3. Retained completed-kernel Harnack datum -/

/-- Constructive-real analogue of the retained kinetic Harnack datum.  The
order field uses `CReal.leEv`, the transitive order appropriate to completed
limits. -/
structure CompletedRetainedKineticHarnackData
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → CReal)
    (sources : List Source) (targets : List Target) : Type where
  spread : Q'
  one_le_spread : (1 : Q') ≤ spread
  kinetic_nonnegative :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          ExpPos.geRat (kineticWeight source target path) 0
  lower :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          ExpPos.geRat
            (kineticWeight source target path)
            bf4KineticFloor
  upper :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          CReal.leRat
            (kineticWeight source target path)
            bf4KineticCeiling
  pathwiseDomination :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            CReal.leEv
              (kineticWeight first target path)
              (CReal.mul
                (CReal.ofQ' spread)
                (kineticWeight second target path))

/-- **Completed 23-factor retained BF4 consumer.**  If every completed local
factor lies in the one-factor heat corridor, the literal product has the exact
BF4 floor, ceiling, and pathwise projective spread `(3489/1055)^23`. -/
def completedBF4RetainedKineticHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (localWeight :
      Source → Target → List State → Factor → CReal)
    (sources : List Source) (targets : List Target)
    (local_corridor :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              CompletedOneFactorHeatCorridor
                (localWeight source target path factor)) :
    CompletedRetainedKineticHarnackData
      paths
      (fun source target path =>
        completedFactorProduct
          (localWeight source target path) factors)
      sources targets where
  spread := bf4KineticSpread
  one_le_spread := bf4KineticSpread_one_le
  kinetic_nonnegative := by
    intro source hsource target htarget path hpath
    exact ExpPos.geRat_mono
      (completedBF4Product_lower
        factors factor_count
        (localWeight source target path)
        (fun factor hfactor =>
          local_corridor source hsource target htarget
            path hpath factor hfactor))
      (Q'.le_of_lt bf4KineticFloor_pos)
  lower := by
    intro source hsource target htarget path hpath
    exact completedBF4Product_lower
      factors factor_count
      (localWeight source target path)
      (fun factor hfactor =>
        local_corridor source hsource target htarget
          path hpath factor hfactor)
  upper := by
    intro source hsource target htarget path hpath
    exact completedBF4Product_upper
      factors factor_count
      (localWeight source target path)
      (fun factor hfactor =>
        local_corridor source hsource target htarget
          path hpath factor hfactor)
  pathwiseDomination := by
    intro first hfirst second hsecond target htarget path hpath
    exact completedBF4Window_order
      (completedBF4Product_upper
        factors factor_count
        (localWeight first target path)
        (fun factor hfactor =>
          local_corridor first hfirst target htarget
            path hpath factor hfactor))
      (completedBF4Product_lower
        factors factor_count
        (localWeight second target path)
        (fun factor hfactor =>
          local_corridor second hsecond target htarget
            path hpath factor hfactor))

/-- The completed retained consumer carries exactly the established BF4
spread, with no extra completion loss. -/
theorem completedBF4RetainedKineticHarnack_spread
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (localWeight :
      Source → Target → List State → Factor → CReal)
    (sources : List Source) (targets : List Target)
    (local_corridor :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              CompletedOneFactorHeatCorridor
                (localWeight source target path factor)) :
    (completedBF4RetainedKineticHarnack
      paths factors factor_count localWeight
      sources targets local_corridor).spread =
        bf4KineticSpread :=
  rfl

end YMGap.Continuum.BF4CompletedHeatRetainedConsumer

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedFactorProduct_lower_on
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedFactorProduct_upper_on
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedBF4Product_lower
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedBF4Product_upper
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedBF4Window_order
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedBF4RetainedKineticHarnack
#print axioms YMGap.Continuum.BF4CompletedHeatRetainedConsumer.completedBF4RetainedKineticHarnack_spread
