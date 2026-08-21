/-
# Analytic kernel for the completed physical BF4 cutoff inner form

The completed physical carrier already has exact rational module laws, but its
limiting bilinear form still lives only on dense finite-linear presentations.
To take the outer limit `n |-> B(X_n,Y_n)` constructively, every inner
`CReal` must expose a Type-level approximation modulus and the pairing must
obey a quantitative two-sided Cauchy--Schwarz estimate.

This module supplies those prerequisites for the actual physical BF4 form:

* the slab cutoff modulus is retained as `CReal.InnerRegularity` data;
* regularity is propagated through arbitrary signed finite-linear syntax;
* the limiting pairing satisfies a division-free two-sided rational bound;
* the diagonal is identified with squared distance to zero; and
* bilinearity gives the telescope used by the outer Cauchy estimate.

This is fixed nome and fixed finite half-extent.  It does not yet define the
completed inner form, transfer operator, thermodynamic limit, continuum
theory, or mass gap.

## Axiom gate

Only explicit rational moduli, finite-stage physical GNS positivity, and
constructive `CReal` algebra are used.  There is no classical choice,
noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Explicit inner regularity of the physical limiting form -/

/-- The already-proved slab cutoff modulus, retained as Type-level data for
the literal stationary cutoff limit. -/
def centralPhysicalStationaryCutoffLimitInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CReal.InnerRegularity
      (centralPhysicalStationaryCutoffLimit hw0 hw1 half observable) where
  rate epsilon :=
    slabNomeBoundedObservableModulus w (centralExtent half) epsilon
  regular := by
    intro epsilon hepsilon first second hfirst hsecond
    have hslab :=
      slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
        hw0 hw1 (centralExtent half)
        (centralLowerSlabUnitObservable half observable)
        hepsilon hfirst hsecond
    have hfirstBridge :=
      centralPhysicalStationaryMean_eq_slabExpectation
        w (Q'.le_of_lt hw0) first half observable
    have hsecondBridge :=
      centralPhysicalStationaryMean_eq_slabExpectation
        w (Q'.le_of_lt hw0) second half observable
    constructor
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfirstBridge)
        (Q'.le_trans' _ _ _ hslab.1
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_right _ _ epsilon
              (Q'.eqv_symm hsecondBridge))))
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsecondBridge)
        (Q'.le_trans' _ _ _ hslab.2
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_right _ _ epsilon
              (Q'.eqv_symm hfirstBridge))))

/-- Atomic product moments inherit the explicit physical cutoff modulus. -/
def atomInnerLimitInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalUnitObservable) :
    CReal.InnerRegularity (atomInnerLimit hw0 hw1 half left right) :=
  centralPhysicalStationaryCutoffLimitInnerRegularity hw0 hw1 half
    (centralPhysicalUnitObservableMul left right)

/-- Right-linear extension preserves explicit inner regularity, including at
signed rational scalar nodes. -/
def atomLinearInnerLimitInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalUnitObservable) :
    forall right : CentralPhysicalLinearObservable,
      CReal.InnerRegularity
        (atomLinearInnerLimit hw0 hw1 half left right)
  | .zero => CReal.InnerRegularity.ofQ' 0
  | .atom right => atomInnerLimitInnerRegularity hw0 hw1 half left right
  | .add first second =>
      CReal.InnerRegularity.add
        (atomLinearInnerLimitInnerRegularity hw0 hw1 half left first)
        (atomLinearInnerLimitInnerRegularity hw0 hw1 half left second)
  | .smul scalar right =>
      CReal.InnerRegularity.scaleLeftSigned
        (atomLinearInnerLimitInnerRegularity hw0 hw1 half left right) scalar

/-- Every dense physical finite-linear pairing exposes a computable
approximation-index modulus. -/
def innerLimitInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : forall left right : CentralPhysicalLinearObservable,
      CReal.InnerRegularity (innerLimit hw0 hw1 half left right)
  | .zero, _ => CReal.InnerRegularity.ofQ' 0
  | .atom left, right =>
      atomLinearInnerLimitInnerRegularity hw0 hw1 half left right
  | .add first second, right =>
      CReal.InnerRegularity.add
        (innerLimitInnerRegularity hw0 hw1 half first right)
        (innerLimitInnerRegularity hw0 hw1 half second right)
  | .smul scalar left, right =>
      CReal.InnerRegularity.scaleLeftSigned
        (innerLimitInnerRegularity hw0 hw1 half left right) scalar

/-- The induced squared distance has a computable inner approximation
modulus. -/
def physicalLinearDistSqInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.InnerRegularity
      (physicalLinearDistSq hw0 hw1 half left right) :=
  innerLimitInnerRegularity hw0 hw1 half
    (sub left right) (sub left right)

/-! ## 2. Quantitative Cauchy--Schwarz at the limiting physical form -/

/-- A quantitative, division-free two-sided Cauchy--Schwarz bound.

The eventual diagonal bounds are sampled with rational slacks `u` and `1`.
Thus their finite-stage upper bounds are `u+u` and `v+1`; the displayed
product budget is exactly what is needed to bound the absolute cross term by
`e` at every sufficiently late inner approximation. -/
theorem innerLimit_twoSided_leRat
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable)
    (u v e : Q') (hu : (0 : Q') < u) (he : (0 : Q') < e)
    (hleft : CReal.leEv (innerLimit hw0 hw1 half left left)
      (CReal.ofQ' u))
    (hright : CReal.leEv (innerLimit hw0 hw1 half right right)
      (CReal.ofQ' v))
    (hbudget : (u + u) * (v + 1) <= e * e) :
    CReal.leRat (innerLimit hw0 hw1 half left right) e /\
      CReal.leRat (CReal.neg (innerLimit hw0 hw1 half left right)) e := by
  obtain ⟨Nleft, hNleft⟩ := hleft u hu
  have hone : (0 : Q') < 1 := by decide
  obtain ⟨Nright, hNright⟩ := hright 1 hone
  let pair := innerLimit hw0 hw1 half left right
  have habs : ∃ N : Nat, ∀ cutoff : Nat, N <= cutoff ->
      Q'.abs (pair.approx cutoff) <= e := by
    refine ⟨max Nleft Nright, fun cutoff hcutoff => ?_⟩
    have hsleft : Nleft <= cutoff :=
      Nat.le_trans (Nat.le_max_left _ _) hcutoff
    have hsright : Nright <= cutoff :=
      Nat.le_trans (Nat.le_max_right _ _) hcutoff
    have hleftUpper :
        (innerLimit hw0 hw1 half left left).approx cutoff <= u + u := by
      simpa using hNleft cutoff hsleft
    have hrightUpper :
        (innerLimit hw0 hw1 half right right).approx cutoff <= v + 1 := by
      simpa using hNright cutoff hsright
    have hleftNonnegative : (0 : Q') <=
        (innerLimit hw0 hw1 half left left).approx cutoff :=
      innerLimit_self_approx_nonnegative hw0 hw1 half cutoff left
    have hrightNonnegative : (0 : Q') <=
        (innerLimit hw0 hw1 half right right).approx cutoff :=
      innerLimit_self_approx_nonnegative hw0 hw1 half cutoff right
    have huNonnegative : (0 : Q') <= u + u :=
      Q'.zero_le_add u u (Q'.le_of_lt hu) (Q'.le_of_lt hu)
    have hproduct :
        (innerLimit hw0 hw1 half left left).approx cutoff *
            (innerLimit hw0 hw1 half right right).approx cutoff <=
          (u + u) * (v + 1) :=
      Q'.mul_le_mul_of_nonneg hleftUpper hrightUpper
        huNonnegative hrightNonnegative
    have hsquare : pair.approx cutoff * pair.approx cutoff <= e * e :=
      Q'.le_trans' _ _ _
        (innerLimit_approx_cauchy_schwarz
          hw0 hw1 half cutoff left right)
        (Q'.le_trans' _ _ _ hproduct hbudget)
    exact Q'.abs_le_of_sq_le_sq he hsquare
  obtain ⟨N, hN⟩ := habs
  constructor
  · exact CReal.leRat_of_eventually ⟨N, fun cutoff hcutoff =>
      Q'.le_trans' _ _ _ (Q'.le_abs_self (pair.approx cutoff))
        (hN cutoff hcutoff)⟩
  · exact CReal.leRat_of_eventually ⟨N, fun cutoff hcutoff =>
      Q'.le_trans' _ _ _ (Q'.neg_le_abs (pair.approx cutoff))
        (hN cutoff hcutoff)⟩

/-! ## 3. Diagonal geometry and the bilinear telescope -/

/-- The dense diagonal is the squared distance to the presentation zero. -/
theorem innerLimit_self_equiv_distSq_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half observable observable)
      (physicalLinearDistSq hw0 hw1 half observable .zero) := by
  have hsub : Equivalent (sub observable .zero) observable :=
    equivalent_symm
      (equivalent_trans
        (sub_add_right_equivalent observable .zero)
        (equivalent_add_zero (sub observable .zero)))
  exact CReal.Equiv.symm
    (innerLimit_congr hw0 hw1 half hsub hsub)

private theorem ofQ'_neg_one_mul_equiv_neg (value : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' (-1)) value) (CReal.neg value) :=
  Equiv_of_approx_eqv (fun cutoff => by
    change ((-1 : Q') * value.approx cutoff) ≈ (-value.approx cutoff)
    exact Q'.eqv_trans _ _ _
      (Q'.neg_mul_eqv 1 (value.approx cutoff))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (value.approx cutoff))))

/-- Subtraction in the first dense argument becomes subtraction of pairings. -/
theorem innerLimit_sub_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right test : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half (sub left right) test)
      (CReal.add
        (innerLimit hw0 hw1 half left test)
        (CReal.neg (innerLimit hw0 hw1 half right test))) := by
  have hadd := innerLimit_add_left hw0 hw1 half left (neg right) test
  have hsmul := innerLimit_smul_left hw0 hw1 half (-1) right test
  have hneg := CReal.Equiv.trans hsmul
    (ofQ'_neg_one_mul_equiv_neg
      (innerLimit hw0 hw1 half right test))
  exact CReal.Equiv.trans hadd (CReal.add_congr_right hneg)

/-- Bilinear telescope for two endpoint pairs.  This is the exact algebraic
identity used to prove that representative pairings are outer Cauchy. -/
theorem innerLimit_diff_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left left' right right' : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (CReal.add
        (innerLimit hw0 hw1 half left right)
        (CReal.neg (innerLimit hw0 hw1 half left' right')))
      (CReal.add
        (innerLimit hw0 hw1 half (sub left left') right)
        (innerLimit hw0 hw1 half (sub right right') left')) := by
  let P := innerLimit hw0 hw1 half left right
  let Q := innerLimit hw0 hw1 half left' right
  let R := innerLimit hw0 hw1 half left' right'
  have hfirst := innerLimit_sub_left hw0 hw1 half left left' right
  have hsecondRaw := innerLimit_sub_left hw0 hw1 half right right' left'
  have hsecond : CReal.Equiv
      (innerLimit hw0 hw1 half (sub right right') left')
      (CReal.add Q (CReal.neg R)) := by
    have hQ : CReal.Equiv (innerLimit hw0 hw1 half right left') Q :=
      CReal.Equiv.symm (innerLimit_symm hw0 hw1 half left' right)
    have hR : CReal.Equiv (innerLimit hw0 hw1 half right' left') R :=
      innerLimit_symm hw0 hw1 half right' left'
    exact CReal.Equiv.trans hsecondRaw
      (CReal.Equiv.trans (CReal.add_congr_left hQ)
        (CReal.add_congr_right (CReal.neg_congr hR)))
  have hterms : CReal.Equiv
      (CReal.add
        (innerLimit hw0 hw1 half (sub left left') right)
        (innerLimit hw0 hw1 half (sub right right') left'))
      (CReal.add (CReal.add P (CReal.neg Q))
        (CReal.add Q (CReal.neg R))) :=
    CReal.Equiv.trans (CReal.add_congr_left hfirst)
      (CReal.add_congr_right hsecond)
  have htelescope : CReal.Equiv
      (CReal.add (CReal.add P (CReal.neg Q))
        (CReal.add Q (CReal.neg R)))
      (CReal.add P (CReal.neg R)) :=
    Equiv_of_approx_eqv (fun cutoff => by
      refine Q'.eqv_trans _ _ _
        (Q'.rearr_ABXY (P.approx cutoff) (-(Q.approx cutoff))
          (Q.approx cutoff) (-(R.approx cutoff))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0
          (Q'.neg_add_self_eqv (Q.approx cutoff))) ?_
      exact QPoly.q_add_zero_eqv _)
  exact CReal.Equiv.trans (CReal.Equiv.symm htelescope)
    (CReal.Equiv.symm hterms)

/-! ## Axiom audit -/

#print axioms centralPhysicalStationaryCutoffLimitInnerRegularity
#print axioms atomLinearInnerLimitInnerRegularity
#print axioms innerLimitInnerRegularity
#print axioms physicalLinearDistSqInnerRegularity
#print axioms innerLimit_twoSided_leRat
#print axioms innerLimit_self_equiv_distSq_zero
#print axioms innerLimit_sub_left
#print axioms innerLimit_diff_split

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
