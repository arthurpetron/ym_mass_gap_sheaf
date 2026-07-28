/-
# Completed retained-path conditional order

`BF4CompletedHeatRetainedConsumer` supplies a pathwise Harnack comparison in
the transitive constructive-real order `CReal.leEv`.  This module proves that
the comparison survives the next physical operation: multiplication by the
same nonnegative rational interior-potential weight and finite conditional
integration over retained paths.

The spread does not grow.  In particular, no
`potentialSpread ^ interiorCount` loss appears: the full path potential is a
common nonnegative scalar on the two source rows before the path coordinate
is forgotten.

The positive pushforward is also exposed entrywise after an arbitrary finite
matrix amplification, and it preserves any pathwise nonnegative quadratic
channel after the quadratic has been formed.  Honest scope: entrywise order
alone is not asserted to imply Loewner/CP order for arbitrary signed
coefficient matrices; a genuine matrix-valued Gram premise is still required
for that stronger conclusion.

## Axiom gate

Constructive `Q'`/`CReal` order and finite list induction only.  There is no
`Classical.*`, `Real`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedHeatRetainedConsumer
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.CRealContinuumAlg
import YMGap.Continuum.GNSDynamics

namespace YMGap.Continuum.BF4CompletedRetainedConditionalOrder

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer

/-! ## 1. Finite `CReal` path integration -/

/-- Finite constructive-real sum over a retained path list. -/
def completedPathSum {Path : Type}
    (weight : Path → CReal) : List Path → CReal
  | [] => CReal.czero
  | path :: tail =>
      CReal.add (weight path) (completedPathSum weight tail)

/-- Termwise `leEv` order survives a finite retained-path sum. -/
theorem completedPathSum_mono_on
    {Path : Type} (lower upper : Path → CReal) :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        CReal.leEv (lower path) (upper path)) →
      CReal.leEv
        (completedPathSum lower paths)
        (completedPathSum upper paths)
  | [], _ => CReal.leEv_refl _
  | path :: tail, horder =>
      CReal.leEv_add
        (horder path List.mem_cons_self)
        (completedPathSum_mono_on
          lower upper tail
          (fun item hitem =>
            horder item
              (List.mem_cons_of_mem path hitem)))

/-- A finite sum of nonnegative completed path channels is nonnegative. -/
theorem completedPathSum_nonnegative_on
    {Path : Type} (weight : Path → CReal) :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        ExpPos.geRat (weight path) 0) →
      ExpPos.geRat (completedPathSum weight paths) 0
  | [], _ => SumOfSquares.geRat_czero
  | path :: tail, hnonnegative => by
      have hhead :=
        hnonnegative path List.mem_cons_self
      have htail :=
        completedPathSum_nonnegative_on
          weight tail
          (fun item hitem =>
            hnonnegative item
              (List.mem_cons_of_mem path hitem))
      have hsum :
          ExpPos.geRat
            (CReal.add
              (weight path)
              (completedPathSum weight tail))
            ((0 : Q') + 0) :=
        SumOfSquares.geRat_add hhead htail
      exact ExpPos.geRat_mono hsum (by decide)

/-- A nonnegative finite path sum retains the lower bound of any explicitly
selected member.  This is the constructive non-vacuity companion to
`completedPathSum_nonnegative_on`: a later physical application cannot obtain
a positive lower bound merely because its carrier happened to be empty. -/
theorem completedPathSum_ge_selected
    {Path : Type} (weight : Path → CReal) :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        ExpPos.geRat (weight path) 0) →
      ∀ selected, selected ∈ paths →
        ∀ floor : Q',
          ExpPos.geRat (weight selected) floor →
          ExpPos.geRat
            (completedPathSum weight paths) floor
  | [], _, selected, hselected, _, _ =>
      False.elim (List.not_mem_nil hselected)
  | head :: tail, hnonnegative, selected, hselected, floor,
      hselectedFloor => by
      rcases List.mem_cons.mp hselected with hhead | htail
      · subst selected
        have htailNonnegative :=
          completedPathSum_nonnegative_on
            weight tail
            (fun path hpath =>
              hnonnegative path
                (List.mem_cons_of_mem head hpath))
        have hsum :=
          SumOfSquares.geRat_add
            hselectedFloor htailNonnegative
        exact ExpPos.geRat_mono hsum
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.eqv_of_eq (Q'.add_zero' floor))))
      · have hheadNonnegative :=
          hnonnegative head List.mem_cons_self
        have htailFloor :=
          completedPathSum_ge_selected
            weight tail
            (fun path hpath =>
              hnonnegative path
                (List.mem_cons_of_mem head hpath))
            selected htail floor hselectedFloor
        have hsum :=
          SumOfSquares.geRat_add
            hheadNonnegative htailFloor
        exact ExpPos.geRat_mono hsum
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.eqv_of_eq (Q'.zero_add' floor))))

/-- A completed scalar pulls through a finite path sum. -/
theorem completedPathSum_const_mul
    {Path : Type} (scale : CReal) (weight : Path → CReal) :
    ∀ paths : List Path,
      CReal.Equiv
        (completedPathSum
          (fun path => CReal.mul scale (weight path))
          paths)
        (CReal.mul scale
          (completedPathSum weight paths))
  | [] =>
      SumOfSquares.Equiv_of_approx_eqv
        (fun n =>
          Q'.eqv_symm
            (Q'.mul_zero_eqv (scale.approx n)))
  | path :: tail => by
      change
        CReal.Equiv
          (CReal.add
            (CReal.mul scale (weight path))
            (completedPathSum
              (fun item => CReal.mul scale (weight item))
              tail))
          (CReal.mul scale
            (CReal.add
              (weight path)
              (completedPathSum weight tail)))
      exact CReal.Equiv.trans
        (YMGap.Continuum.Pivot2.add_congr
          (CReal.Equiv.refl _)
          (completedPathSum_const_mul scale weight tail))
        (CReal.Equiv.symm
          (CReal.mul_add
            scale
            (weight path)
            (completedPathSum weight tail)))

/-! ## 2. Completed Feynman--Kac path weights -/

/-- A completed retained kinetic channel multiplied by the rational product
of all interior potential insertions on its path. -/
def completedRetainedFeynmanKacWeight
    {Source Target State : Type}
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (source : Source) (target : Target)
    (path : List State) : CReal :=
  CReal.mul
    (CReal.ofQ'
      (pathPotentialProduct potential path))
    (kineticWeight source target path)

/-- Finite conditional integration which forgets the retained path while
keeping its terminal target. -/
def completedConditionalPathPushforward
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (source : Source) (target : Target) : CReal :=
  completedPathSum
    (completedRetainedFeynmanKacWeight
      kineticWeight potential source target)
    paths

/-- A completed Feynman--Kac path weight is nonnegative when both its kinetic
channel and every local potential are nonnegative. -/
theorem completedRetainedFeynmanKacWeight_nonnegative
    {Source Target State : Type}
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    {source : Source} {target : Target}
    {path : List State}
    (kinetic_nonnegative :
      ExpPos.geRat
        (kineticWeight source target path) 0) :
    ExpPos.geRat
      (completedRetainedFeynmanKacWeight
        kineticWeight potential source target path)
      0 := by
  exact CReal.mul_nonneg
    (SumOfSquares.geRat_ofQ'_nonneg
      (pathPotentialProduct_nonnegative
        potential_nonnegative path))
    kinetic_nonnegative

/-- Conditional integration of completed retained Feynman--Kac weights stays
in the nonnegative cone. -/
theorem completedConditionalPathPushforward_nonnegative
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (source : Source) (target : Target)
    (kinetic_nonnegative :
      ∀ path, path ∈ paths →
        ExpPos.geRat
          (kineticWeight source target path) 0) :
    ExpPos.geRat
      (completedConditionalPathPushforward
        paths kineticWeight potential source target)
      0 := by
  exact completedPathSum_nonnegative_on
    (completedRetainedFeynmanKacWeight
      kineticWeight potential source target)
    paths
    (fun path hpath =>
      completedRetainedFeynmanKacWeight_nonnegative
        kineticWeight potential potential_nonnegative
        (kinetic_nonnegative path hpath))

private theorem potential_spread_swap
    (potentialWeight spread : Q') (value : CReal) :
    CReal.Equiv
      (CReal.mul
        (CReal.ofQ' potentialWeight)
        (CReal.mul
          (CReal.ofQ' spread) value))
      (CReal.mul
        (CReal.ofQ' spread)
        (CReal.mul
          (CReal.ofQ' potentialWeight) value)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n =>
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            potentialWeight spread
            (value.approx n)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (potentialWeight * spread)
            (spread * potentialWeight)
            (value.approx n)
            (Q'.mul_comm_eqv
              potentialWeight spread))
          (Q'.mul_assoc_eqv
            spread potentialWeight
            (value.approx n))))

/-- **Pathwise completed Feynman--Kac Harnack order.**  Multiplication by the
same nonnegative interior-potential product preserves the retained kinetic
comparison with exactly the original spread. -/
theorem completedRetainedFeynmanKacWeight_pathwiseDomination
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      CompletedRetainedKineticHarnackData
        paths kineticWeight sources targets)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets)
    (path : List State) (hpath : path ∈ paths) :
    CReal.leEv
      (completedRetainedFeynmanKacWeight
        kineticWeight potential first target path)
      (CReal.mul
        (CReal.ofQ' harnack.spread)
        (completedRetainedFeynmanKacWeight
          kineticWeight potential second target path)) := by
  let potentialWeight :=
    pathPotentialProduct potential path
  have hpotential :
      (0 : Q') ≤ potentialWeight :=
    pathPotentialProduct_nonnegative
      potential_nonnegative path
  have hkinetic :=
    harnack.pathwiseDomination
      first hfirst second hsecond
      target htarget path hpath
  have hscaled :=
    CReal.leEv_smul_nonneg
      hpotential hkinetic
  exact
    (CReal.leEv_congr
      (CReal.Equiv.refl _)
      (potential_spread_swap
        potentialWeight harnack.spread
        (kineticWeight second target path))).mp
      hscaled

/-! ## 3. Conditional integration preserves the completed Harnack order -/

/-- **Completed conditional Feynman--Kac order.**  Finite integration over
the full retained path carrier preserves the pathwise Harnack comparison
with no potential-oscillation or path-length loss. -/
theorem completedConditionalPathPushforward_domination
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      CompletedRetainedKineticHarnackData
        paths kineticWeight sources targets)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    CReal.leEv
      (completedConditionalPathPushforward
        paths kineticWeight potential first target)
      (CReal.mul
        (CReal.ofQ' harnack.spread)
        (completedConditionalPathPushforward
          paths kineticWeight potential second target)) := by
  have hsum :
      CReal.leEv
        (completedConditionalPathPushforward
          paths kineticWeight potential first target)
        (completedPathSum
          (fun path =>
            CReal.mul
              (CReal.ofQ' harnack.spread)
              (completedRetainedFeynmanKacWeight
                kineticWeight potential second target path))
          paths) := by
    exact completedPathSum_mono_on
      (completedRetainedFeynmanKacWeight
        kineticWeight potential first target)
      (fun path =>
        CReal.mul
          (CReal.ofQ' harnack.spread)
          (completedRetainedFeynmanKacWeight
            kineticWeight potential second target path))
      paths
      (fun path hpath =>
        completedRetainedFeynmanKacWeight_pathwiseDomination
          paths kineticWeight potential
          potential_nonnegative sources targets harnack
          first hfirst second hsecond
          target htarget path hpath)
  exact
    (CReal.leEv_congr
      (CReal.Equiv.refl _)
      (completedPathSum_const_mul
        (CReal.ofQ' harnack.spread)
        (completedRetainedFeynmanKacWeight
          kineticWeight potential second target)
        paths)).mp
      hsum

/-! ## 4. Finite amplification and quadratic-cone preservation -/

/-- Every finite matrix amplification preserves the completed conditional
order entrywise.  This is the commutative entrywise complete-order statement;
it does not turn entrywise inequalities into a Loewner inequality for signed
coefficient matrices. -/
theorem completedConditionalPathPushforward_amplified_mono
    {Index Target State : Type}
    (paths : List (List State))
    (lower upper :
      Index → Index → Target → List State → CReal)
    (horder :
      ∀ row column target path, path ∈ paths →
        CReal.leEv
          (lower row column target path)
          (upper row column target path))
    (row column : Index) (target : Target) :
    CReal.leEv
      (completedPathSum
        (lower row column target) paths)
      (completedPathSum
        (upper row column target) paths) :=
  completedPathSum_mono_on
    (lower row column target)
    (upper row column target)
    paths
    (horder row column target)

/-- A positive rational path weighting and conditional integration preserve
any already-formed nonnegative completed quadratic channel.  This is the
finite CP/Gram consumer available without asserting that scalar entrywise
Harnack order itself implies matrix Loewner order. -/
theorem completedConditionalQuadratic_nonnegative
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (pathQuadratic : Path → CReal)
    (pathQuadratic_nonnegative :
      ∀ path, path ∈ paths →
        ExpPos.geRat (pathQuadratic path) 0) :
    ExpPos.geRat
      (completedPathSum
        (fun path =>
          CReal.mul
            (CReal.ofQ' (pathWeight path))
            (pathQuadratic path))
        paths)
      0 := by
  exact completedPathSum_nonnegative_on
    (fun path =>
      CReal.mul
        (CReal.ofQ' (pathWeight path))
        (pathQuadratic path))
    paths
    (fun path hpath =>
      CReal.mul_nonneg
        (SumOfSquares.geRat_ofQ'_nonneg
          (pathWeight_nonnegative path hpath))
        (pathQuadratic_nonnegative path hpath))

end YMGap.Continuum.BF4CompletedRetainedConditionalOrder

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedPathSum_mono_on
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedPathSum_nonnegative_on
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedPathSum_ge_selected
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedPathSum_const_mul
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedRetainedFeynmanKacWeight_nonnegative
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedRetainedFeynmanKacWeight_pathwiseDomination
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedConditionalPathPushforward_domination
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedConditionalPathPushforward_amplified_mono
#print axioms YMGap.Continuum.BF4CompletedRetainedConditionalOrder.completedConditionalQuadratic_nonnegative
