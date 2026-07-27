/-
# BF4 retained-path conditional order and finite CP carrier

`BF4GroupedFeynmanKacHarnack` integrates the interior spatial path before
comparing source rows.  A pointwise window on the potential then costs one
oscillation factor per interior insertion.  This file records the strongest
finite theorem available when the carrier is enlarged first:

    retained state = (terminal, complete interior path).

Conditional integration is the positive linear map which forgets the path
coordinate by finite summation.  Consequently:

* pointwise order on the retained carrier survives conditional integration;
* a pathwise kinetic Harnack comparison survives with exactly the same
  spread, because the complete spatial potential product is a common
  nonnegative factor on the two compared retained states;
* if every retained kinetic channel is a rank-one Gram channel, conditional
  integration is a nonnegative weighted Gram sum and preserves every finite
  quadratic form;
* a symmetric pathwise kinetic Harnack bound gives an exact cross-ratio
  certificate for the integrated Feynman--Kac kernel, with no
  `potentialSpread^interiorCount` loss.

Honest scope: no spacing-uniform BF4 conclusion is asserted.  The physical
residual is to construct the actual finite/all-label retained path carrier
and prove a cutoff-, spacing-, and grouping-uniform pathwise kinetic
domination (or Gram factorization) on it.  The aggregate 23-cycle kinetic
window presently in the repository does not imply that pathwise statement.

## Axiom gate

Only exact `Q'` arithmetic and finite list induction are used.  There is no
`Classical.*`, `Real`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedFeynmanKacHarnack
import YMGap.Continuum.FiniteJointKernelPushforward

namespace YMGap.Continuum.BF4RetainedPathConditionalOrder

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The retained carrier and its positive conditional pushforward -/

/-- A terminal together with the complete ordered interior spatial path. -/
abbrev RetainedPathState (Target State : Type) :=
  Target × List State

/-- The finite enlarged carrier before the interior path is forgotten. -/
def retainedPathCarrier
    {Target State : Type}
    (targets : List Target) (paths : List (List State)) :
    List (RetainedPathState Target State) :=
  cartesian targets paths

/-- Forget the interior path but retain the terminal. -/
def retainedPathTerminal
    {Target State : Type} :
    RetainedPathState Target State → Target :=
  fun retained => retained.1

/-- One terminal fiber of the enlarged retained carrier. -/
def retainedPathFiber
    {Target State : Type}
    (target : Target) (paths : List (List State)) :
    List (RetainedPathState Target State) :=
  paths.map (fun path => (target, path))

/-- Positive fiberwise pushforward which conditionally integrates the
complete retained path coordinate. -/
def conditionalPathPushforward
    {Target State : Type}
    (paths : List (List State))
    (retainedWeight : Target → List State → Q')
    (target : Target) : Q' :=
  listQSum (retainedWeight target) paths

/-- The full retained Feynman--Kac weight.  The spatial potential is data on
the retained path, not a scalar absorbed into the kinetic semigroup. -/
def retainedFeynmanKacWeight
    {Source Target State : Type}
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (source : Source) (target : Target) (path : List State) : Q' :=
  kineticWeight source target path *
    pathPotentialProduct potential path

/-- Forgetting the retained path is definitionally the finite
Feynman--Kac kernel. -/
theorem conditionalPathPushforward_retainedFeynmanKac
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (source : Source) (target : Target) :
    conditionalPathPushforward paths
        (retainedFeynmanKacWeight kineticWeight potential source)
        target =
      feynmanKacPathKernel
        paths kineticWeight potential source target :=
  rfl

/-- Conditional path integration is literally deterministic-kernel
pushforward along the forgetful map `(terminal, path) ↦ terminal`, on each
terminal fiber of the retained carrier. -/
theorem conditionalPathPushforward_eq_kernelPushforward
    {Target State : Type} [DecidableEq Target]
    (paths : List (List State))
    (retainedWeight : Target → List State → Q')
    (target : Target) :
    conditionalPathPushforward paths retainedWeight target ≈
      kernelPushforwardWeight
        (retainedPathFiber target paths)
        (fun retained =>
          retainedWeight retained.1 retained.2)
        retainedPathTerminal target := by
  unfold conditionalPathPushforward kernelPushforwardWeight
    retainedPathFiber
  rw [listQSum_map]
  apply listQSum_congr_on
  intro path _
  change retainedWeight target path ≈
    retainedWeight target path *
      deterministicKernel retainedPathTerminal
        (target, path) target
  have hkernel :
      deterministicKernel retainedPathTerminal
          (target, path) target = 1 := by
    simpa only [retainedPathTerminal] using
      (deterministicKernel_on_image
        retainedPathTerminal (target, path))
  rw [hkernel]
  exact Q'.eqv_symm
    (Q'.mul_one_eqv (retainedWeight target path))

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun x hx =>
            hbound x (List.mem_cons_of_mem head hx)))

/-- Conditional path integration preserves the nonnegative cone. -/
theorem conditionalPathPushforward_nonnegative
    {Target State : Type}
    (paths : List (List State))
    (retainedWeight : Target → List State → Q')
    (retained_nonnegative :
      ∀ target path, path ∈ paths →
        (0 : Q') ≤ retainedWeight target path)
    (target : Target) :
    (0 : Q') ≤
      conditionalPathPushforward paths retainedWeight target := by
  unfold conditionalPathPushforward
  exact listQSum_nonnegative_on
    (retainedWeight target) paths
    (retained_nonnegative target)

/-- Conditional path integration is order preserving. -/
theorem conditionalPathPushforward_mono
    {Target State : Type}
    (paths : List (List State))
    (lower upper : Target → List State → Q')
    (horder :
      ∀ target path, path ∈ paths →
        lower target path ≤ upper target path)
    (target : Target) :
    conditionalPathPushforward paths lower target ≤
      conditionalPathPushforward paths upper target := by
  unfold conditionalPathPushforward
  exact listQSum_mono_on
    (lower target) (upper target) paths
    (horder target)

/-- Exact additivity of the conditional pushforward. -/
theorem conditionalPathPushforward_add
    {Target State : Type}
    (paths : List (List State))
    (left right : Target → List State → Q')
    (target : Target) :
    conditionalPathPushforward paths
        (fun terminal path =>
          left terminal path + right terminal path)
        target ≈
      conditionalPathPushforward paths left target +
        conditionalPathPushforward paths right target := by
  unfold conditionalPathPushforward
  exact listQSum_add (left target) (right target) paths

/-- Exact positive-scalar compatibility of the conditional pushforward. -/
theorem conditionalPathPushforward_scale
    {Target State : Type}
    (paths : List (List State))
    (scale : Q')
    (retainedWeight : Target → List State → Q')
    (target : Target) :
    conditionalPathPushforward paths
        (fun terminal path =>
          scale * retainedWeight terminal path)
        target ≈
      scale *
        conditionalPathPushforward paths retainedWeight target := by
  unfold conditionalPathPushforward
  exact listQSum_mul_left scale (retainedWeight target) paths

/-- Every finite matrix amplification preserves entrywise cone order.  This
is the explicit finite commutative complete-order form of positivity; it
does not assert a noncommutative C*-algebra theorem. -/
theorem conditionalPathPushforward_amplified_mono
    {Index Target State : Type}
    (paths : List (List State))
    (lower upper :
      Index → Index → Target → List State → Q')
    (horder :
      ∀ row column target path, path ∈ paths →
        lower row column target path ≤
          upper row column target path)
    (row column : Index) (target : Target) :
    conditionalPathPushforward paths
        (lower row column) target ≤
      conditionalPathPushforward paths
        (upper row column) target :=
  conditionalPathPushforward_mono
    paths (lower row column) (upper row column)
    (horder row column) target

/-! ## 2. Potential-free retained-path Harnack order -/

/-- A symmetric pathwise kinetic comparison on a selected finite rectangle.
The comparison is made before the common spatial potential weight is
integrated out. -/
structure RetainedKineticHarnackData
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (sources : List Source) (targets : List Target) : Type where
  spread : Q'
  one_le_spread : (1 : Q') ≤ spread
  kinetic_nonnegative :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path
  pathwiseDomination :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            kineticWeight first target path ≤
              spread * kineticWeight second target path

namespace RetainedKineticHarnackData

theorem spread_nonnegative
    {Source Target State : Type}
    {paths : List (List State)}
    {kineticWeight : Source → Target → List State → Q'}
    {sources : List Source} {targets : List Target}
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets) :
    (0 : Q') ≤ data.spread :=
  Q'.le_trans' _ _ _ Q'.zero_le_one data.one_le_spread

end RetainedKineticHarnackData

/-- Nonnegativity of every integrated Feynman--Kac entry on the selected
rectangle. -/
theorem retainedPathFeynmanKac_nonnegative
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    (0 : Q') ≤
      feynmanKacPathKernel
        paths kineticWeight potential source target := by
  unfold feynmanKacPathKernel
  apply listQSum_nonnegative_on
  intro path hpath
  exact Q'.mul_nonneg _ _
    (data.kinetic_nonnegative
      source hsource target htarget path hpath)
    (pathPotentialProduct_nonnegative
      potential_nonnegative path)

/-- **Retained-path Harnack/order theorem.**  A pathwise kinetic comparison
passes through the full nonconstant spatial Feynman--Kac weight with exactly
the same spread.  No lower or upper potential window and no interior-count
factor is used. -/
theorem feynmanKac_of_retainedKineticDomination
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    feynmanKacPathKernel
        paths kineticWeight potential first target ≤
      data.spread *
        feynmanKacPathKernel
          paths kineticWeight potential second target := by
  have hsum :
      conditionalPathPushforward paths
          (retainedFeynmanKacWeight
            kineticWeight potential first) target ≤
        conditionalPathPushforward paths
          (fun terminal path =>
            data.spread *
              retainedFeynmanKacWeight
                kineticWeight potential second terminal path)
          target := by
    unfold conditionalPathPushforward
    apply listQSum_mono_on
    intro path hpath
    unfold retainedFeynmanKacWeight
    have hkinetic :=
      data.pathwiseDomination
        first hfirst second hsecond
        target htarget path hpath
    have hproduct :=
      Q'.mul_le_mul_of_nonneg_right
        (kineticWeight first target path)
        (data.spread *
          kineticWeight second target path)
        (pathPotentialProduct potential path)
        hkinetic
        (pathPotentialProduct_nonnegative
          potential_nonnegative path)
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv
          data.spread
          (kineticWeight second target path)
          (pathPotentialProduct potential path)))
  rw [conditionalPathPushforward_retainedFeynmanKac] at hsum
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (conditionalPathPushforward_scale
        paths data.spread
        (retainedFeynmanKacWeight
          kineticWeight potential second)
        target))

private theorem mul_swap4_local (a b c d : Q') :
    (a * b) * (c * d) ≈
      (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    ?_ (Q'.eqv_symm
      (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

/-- **Potential-independent integrated cross-ratio certificate.**  Strict
positivity plus the symmetric retained kinetic comparison gives the same
cross-ratio spread after conditional path integration.  This is useful for a
spacing-uniform Harnack route precisely when `data.spread` is itself proved
uniform for the physical retained kinetic carrier. -/
def retainedPathCrossRatioCertificate
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (strictlyPositive :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') <
            feynmanKacPathKernel
              paths kineticWeight potential source target) :
    FiniteCrossRatioDiameterCertificate
      (feynmanKacPathKernel
        paths kineticWeight potential)
      sources targets where
  spread := data.spread
  one_le_spread := data.one_le_spread
  strictlyPositive := strictlyPositive
  crossRatioBound := by
    intro first hfirst second hsecond
      left hleft right hright
    have hfirstLeft :=
      feynmanKac_of_retainedKineticDomination
        paths kineticWeight potential sources targets
        data potential_nonnegative
        first hfirst second hsecond left hleft
    have hsecondRight :=
      feynmanKac_of_retainedKineticDomination
        paths kineticWeight potential sources targets
        data potential_nonnegative
        second hsecond first hfirst right hright
    have hsecondRightNonnegative :
        (0 : Q') ≤
          feynmanKacPathKernel
            paths kineticWeight potential second right :=
      retainedPathFeynmanKac_nonnegative
        paths kineticWeight potential sources targets
        data potential_nonnegative second hsecond right hright
    have hscaledSecondLeftNonnegative :
        (0 : Q') ≤
          data.spread *
            feynmanKacPathKernel
              paths kineticWeight potential second left :=
      Q'.mul_nonneg _ _
        data.spread_nonnegative
        (retainedPathFeynmanKac_nonnegative
          paths kineticWeight potential sources targets
          data potential_nonnegative second hsecond left hleft)
    have hproduct :
        feynmanKacPathKernel
              paths kineticWeight potential first left *
            feynmanKacPathKernel
              paths kineticWeight potential second right ≤
          (data.spread *
              feynmanKacPathKernel
                paths kineticWeight potential second left) *
            (data.spread *
              feynmanKacPathKernel
                paths kineticWeight potential first right) :=
      Q'.mul_le_mul_of_nonneg
        hfirstLeft hsecondRight
        hscaledSecondLeftNonnegative
        hsecondRightNonnegative
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (mul_swap4_local
            data.spread
            (feynmanKacPathKernel
              paths kineticWeight potential second left)
            data.spread
            (feynmanKacPathKernel
              paths kineticWeight potential first right))
          (Q'.mul_eqv_congr_left
            (data.spread * data.spread) _ _
            (Q'.mul_comm_eqv
              (feynmanKacPathKernel
                paths kineticWeight potential second left)
              (feynmanKacPathKernel
                paths kineticWeight potential first right)))))

/-- The integrated certificate records exactly the retained kinetic spread;
the potential oscillation and path length do not occur. -/
theorem retainedPathCrossRatioCertificate_spread
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (strictlyPositive :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') <
            feynmanKacPathKernel
              paths kineticWeight potential source target) :
    (retainedPathCrossRatioCertificate
      paths kineticWeight potential sources targets
      data potential_nonnegative strictlyPositive).spread =
        data.spread :=
  rfl

/-! ## 3. Finite retained-channel Gram / CP theorem -/

/-- Kinetic path channel represented by one half-amplitude on each endpoint.
This is the exact retained datum needed for Gram positivity. -/
def retainedGramKinetic
    {Endpoint State : Type}
    (amplitude : Endpoint → List State → Q')
    (left right : Endpoint) (path : List State) : Q' :=
  amplitude left path * amplitude right path

/-- Every retained rank-one kinetic channel integrates to the corresponding
nonnegatively weighted Gram entry. -/
theorem feynmanKac_retainedGram_eq_weightedGram
    {Endpoint State : Type}
    (paths : List (List State))
    (amplitude : Endpoint → List State → Q')
    (potential : State → Q')
    (left right : Endpoint) :
    feynmanKacPathKernel paths
        (retainedGramKinetic amplitude) potential left right ≈
      weightedGram paths
        (pathPotentialProduct potential)
        amplitude left right := by
  unfold feynmanKacPathKernel retainedGramKinetic weightedGram
  apply listQSum_congr_on
  intro path _
  exact Q'.mul_comm_eqv
    (amplitude left path * amplitude right path)
    (pathPotentialProduct potential path)

/-- Exact finite quadratic of the conditionally integrated retained Gram
kernel. -/
def retainedFeynmanKacQuadratic
    {Endpoint State : Type}
    (endpoints : List Endpoint)
    (paths : List (List State))
    (amplitude : Endpoint → List State → Q')
    (potential : State → Q')
    (coefficient : Endpoint → Q') : Q' :=
  finiteJointQuadratic endpoints coefficient
    (feynmanKacPathKernel paths
      (retainedGramKinetic amplitude) potential)

/-- Conditional integration of the retained path carrier is exactly the
weighted Gram quadratic. -/
theorem retainedFeynmanKacQuadratic_eq_weightedGram
    {Endpoint State : Type}
    (endpoints : List Endpoint)
    (paths : List (List State))
    (amplitude : Endpoint → List State → Q')
    (potential : State → Q')
    (coefficient : Endpoint → Q') :
    retainedFeynmanKacQuadratic
        endpoints paths amplitude potential coefficient ≈
      weightedGramQuadratic
        endpoints paths
        (pathPotentialProduct potential)
        amplitude coefficient := by
  unfold retainedFeynmanKacQuadratic
    finiteJointQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left _
  apply listQSum_congr_on
  intro right _
  exact Q'.mul_eqv_congr_left
    (coefficient left * coefficient right) _ _
    (feynmanKac_retainedGram_eq_weightedGram
      paths amplitude potential left right)

/-- **Finite CP/Gram preservation.**  For every finite endpoint carrier and
every rational coefficient vector, conditionally integrating the retained
rank-one path channels against an arbitrary nonnegative spatial potential
produces a nonnegative quadratic form. -/
theorem retainedFeynmanKacQuadratic_nonnegative
    {Endpoint State : Type}
    (endpoints : List Endpoint)
    (paths : List (List State))
    (amplitude : Endpoint → List State → Q')
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (coefficient : Endpoint → Q') :
    (0 : Q') ≤
      retainedFeynmanKacQuadratic
        endpoints paths amplitude potential coefficient := by
  have hgram :
      (0 : Q') ≤
        weightedGramQuadratic
          endpoints paths
          (pathPotentialProduct potential)
          amplitude coefficient :=
    weightedGramQuadratic_nonnegative
      endpoints paths
      (pathPotentialProduct potential)
      amplitude coefficient
      (fun path _ =>
        pathPotentialProduct_nonnegative
          potential_nonnegative path)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (retainedFeynmanKacQuadratic_eq_weightedGram
        endpoints paths amplitude potential coefficient))

end YMGap.Continuum.BF4RetainedPathConditionalOrder

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.conditionalPathPushforward_retainedFeynmanKac
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.conditionalPathPushforward_eq_kernelPushforward
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.conditionalPathPushforward_mono
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.conditionalPathPushforward_amplified_mono
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.feynmanKac_of_retainedKineticDomination
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.retainedPathCrossRatioCertificate
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.feynmanKac_retainedGram_eq_weightedGram
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.retainedFeynmanKacQuadratic_eq_weightedGram
#print axioms YMGap.Continuum.BF4RetainedPathConditionalOrder.retainedFeynmanKacQuadratic_nonnegative
