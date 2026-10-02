/-
# Local mixed commutator control on the original disjoint-face pair

The mixed first-order angular and quadratic source-flux terms vanish for
literal link-disjoint faces. The full original mixed energy, multiplied by
its unchanged odd partition, is therefore a SIGNED local commutator pairing
times -(1-w)^2, plus the complete mixed cubic and omitted-mode debt.

Haar Cauchy--Schwarz bounds the corrected mixed energy by the two actual
commutator squares. No source Casimir-square budget, extra heat cutoff,
interacting independence, favorable debt sign or scaling bound is assumed.
The squares and signed debt still require control relative to OWN covariance
on a justified changing family. This is not a physical or continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation (squareMass)
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
  (weighted_gamma_finSum family_sourceFirstOrder_gamma)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
  (signedRemainder normalizedRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

private theorem six_congr {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add
            (h 2 3 (by decide) (by decide))))))

private theorem sum_congr {A : Type} (ids : List A) (f g : A → RatPoly)
    (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g)) := by
  induction ids with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons i ids ih => exact (h i).add ih

private theorem sum_add {A : Type} (ids : List A) (f g : A → RatPoly) :
    RatPolyCoeffEqv (polySum (ids.map (fun i => polyAdd (f i) (g i))))
      (polyAdd (polySum (ids.map f)) (polySum (ids.map g))) := by
  induction ids with
  | nil => exact (RatPolyCoeffEqv.add_zero _).symm
  | cons i ids ih =>
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem neg_add (p q : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polyAdd p q)) (polyAdd (polyNeg p) (polyNeg q)) :=
  coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.var 1)))
    (.add (.neg (.var 0)) (.neg (.var 1))) (by decide) (fun | 0 => p | _ => q)

private theorem casimir_congr (active : List Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (activeCasimirPolynomial active f) (activeCasimirPolynomial active g) := by
  apply sum_congr
  intro b
  apply RatPolyCoeffEqv.neg
  apply sum_congr
  intro ij
  exact angularDerivative_congr _ _ (angularDerivative_congr _ _ h)

private theorem casimir_add (active : List Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyAdd f g))
      (polyAdd (activeCasimirPolynomial active f) (activeCasimirPolynomial active g)) := by
  refine (sum_congr active _ _ (fun b => ?_)).trans (sum_add active _ _)
  apply RatPolyCoeffEqv.trans (RatPolyCoeffEqv.neg ?_) (neg_add _ _)
  refine (sum_congr _ _ _ (fun ij => ?_)).trans (sum_add _ _ _)
  exact (angularDerivative_congr _ _ (angularDerivative_add _ _ f g)).trans
    (angularDerivative_add _ _ _ _)

private theorem gamma_congr (active : List Nat) (a : RatPoly) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (activeGamma active a f) (activeGamma active a g) := by
  apply sum_congr
  intro b
  exact six_congr (fun i j _ _ => (angularDerivative_congr _ _ h).mul_left _)

private theorem gamma_add (active : List Nat) (a f g : RatPoly) :
    RatPolyCoeffEqv (activeGamma active a (polyAdd f g))
      (polyAdd (activeGamma active a f) (activeGamma active a g)) := by
  refine (sum_congr active _ _ (fun b => ?_)).trans (sum_add active _ _)
  refine (six_congr (fun i j _ _ => ?_)).trans (six_add _ _)
  exact ((angularDerivative_add _ _ f g).mul_left _).trans
    (RatPolyCoeffEqv.mul_add_right _ _ _)

private theorem commutator_congr (active : List Nat) (a : RatPoly) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (commutatorPolynomial active a f) (commutatorPolynomial active a g) :=
  ((casimir_congr active h).mul_left a).add ((gamma_congr active a h).smul (-2))

private theorem commutator_add (active : List Nat) (a f g : RatPoly) :
    RatPolyCoeffEqv (commutatorPolynomial active a (polyAdd f g))
      (polyAdd (commutatorPolynomial active a f) (commutatorPolynomial active a g)) := by
  refine (((casimir_add active f g).mul_left a).add
    ((gamma_add active a f g).smul (-2))).trans ?_
  exact ((RatPolyCoeffEqv.mul_add_right _ _ _).add
    (RatPolyCoeffEqv.smul_add _ _ _)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem pair_pin (width : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) :
    RatPolyCoeffEqv (spatialSpan width c [p,q])
      (polyAdd (spatialSpan width c [p]) (spatialSpan width c [q])) :=
  (RatPolyCoeffEqv.add_zero _).symm.add (RatPolyCoeffEqv.refl _)

/-- The ACTUAL projected source is differentiated only through the observable's
angular directions. No replacement by a bare or independent source. -/
def sourceCommutator (w : Q') (K width n : Nat) (f : RatPoly) : RatPoly :=
  commutatorPolynomial (List.range (N width))
    (projectedEndpointSource w K width (terminalMessage w K width n)) f

theorem sourceCommutator_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) :
    RatPolyCoeffEqv (sourceCommutator w K width n (spatialSpan width c [p,q]))
      (polyAdd (sourceCommutator w K width n (spatialSpan width c [p]))
        (sourceCommutator w K width n (spatialSpan width c [q]))) :=
  (commutator_congr _ _ (pair_pin width c p q)).trans (commutator_add _ _ _ _)

private theorem commutator_supported (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (sourceCommutator w K width n f) := by
  unfold sourceCommutator commutatorPolynomial
  have hq := source_supported w K width n
  have hs : ∀ i, i ∈ List.range (N width) → i < N width := fun _ hi => List.mem_range.mp hi
  apply supported_add (supported_polyMul hq (activeCasimirPolynomial_supported _ hs hf))
  intro t ht
  obtain ⟨s, hs', rfl⟩ := List.mem_map.mp ht
  exact activeGamma_supported _ hs hq hf s hs'

/-- Entire cubic-minus-omitted term; the omitted term is not assigned a sign
or called uniformly higher order. -/
def sourceDebt (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let a := projectedEndpointSource w K width (terminalMessage w K width n)
  sourceCubic (N width-1) w a f - sourceOmitted (N width-1) w K a f

def mixedDebt (w : Q') (K width n : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) : Q' :=
  (sourceDebt w K width n (spatialSpan width c [p,q]) -
    sourceDebt w K width n (spatialSpan width c [p])) -
    sourceDebt w K width n (spatialSpan width c [q])

/-- Signed local pairing, not asserted nonnegative or statistically independent. -/
def commutatorCross (w : Q') (K width n : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) : Q' :=
  H (N width) (polyMul (sourceCommutator w K width n (spatialSpan width c [p]))
    (sourceCommutator w K width n (spatialSpan width c [q])))

def commutatorSquare (w : Q') (K width n : Nat) (c : Z4Plaq → Q') (p : Z4Plaq) : Q' :=
  let B := sourceCommutator w K width n (spatialSpan width c [p])
  H (N width) (polyMul B B)

/-- Disjointness also cancels the mixed SIGNED change of angular weight. -/
theorem angularWeightDefect_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    angularWeightDefect w K width n (spatialSpan width c [p,q]) ≈
      angularWeightDefect w K width n (spatialSpan width c [p]) +
      angularWeightDefect w K width n (spatialSpan width c [q]) :=
  weightedAngular_pair width _ c hd

private theorem firstOrder_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    let a := projectedEndpointSource w K width (terminalMessage w K width n)
    sourceFirstOrder (N width-1) a (spatialSpan width c [p,q]) ≈
      sourceFirstOrder (N width-1) a (spatialSpan width c [p]) +
      sourceFirstOrder (N width-1) a (spatialSpan width c [q]) := by
  dsimp only
  have hfirst (qs : List Z4Plaq) := Q'.eqv_trans _ _ _
    (family_sourceFirstOrder_gamma w K width n c qs)
    (weighted_gamma_finSum (N width) _ (spatialSpan width c qs))
  exact Q'.eqv_trans _ _ _ (hfirst [p,q])
    (Q'.eqv_trans _ _ _ (weightedAngular_pair width _ c hd)
      (Q'.add_eqv_congr' (hfirst [p]).symm (hfirst [q]).symm))

private theorem flux_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    let a := projectedEndpointSource w K width (terminalMessage w K width n)
    H (N width) (curvatureFlux (List.range (N width)) a (spatialSpan width c [p,q])) ≈
      H (N width) (curvatureFlux (List.range (N width)) a (spatialSpan width c [p])) +
      H (N width) (curvatureFlux (List.range (N width)) a (spatialSpan width c [q])) := by
  dsimp only
  exact Q'.eqv_trans _ _ _ (weighted_gamma_finSum (N width) _ _)
    (Q'.eqv_trans _ _ _ (weightedAngular_pair width _ c hd)
      (Q'.add_eqv_congr' (weighted_gamma_finSum (N width) _ _).symm
        (weighted_gamma_finSum (N width) _ _).symm))

private theorem square_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) :
    H (N width) (polyMul (sourceCommutator w K width n (spatialSpan width c [p,q]))
      (sourceCommutator w K width n (spatialSpan width c [p,q]))) ≈
    commutatorSquare w K width n c p + commutatorSquare w K width n c q +
      2*commutatorCross w K width n c p q := by
  let B := sourceCommutator w K width n (spatialSpan width c [p])
  let C := sourceCommutator w K width n (spatialSpan width c [q])
  have h := sourceCommutator_pair w K width n c p q
  have hpoly : RatPolyCoeffEqv (polyMul (polyAdd B C) (polyAdd B C))
      (polyAdd (polyAdd (polyMul B B) (polyMul C C)) (polySmul 2 (polyMul B C))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.const 2) (.mul (.var 0) (.var 1)))) (by decide) (fun | 0 => B | _ => C)).trans
      ((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((h.mul h).trans hpoly))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (quaternionHaar_append _ _ _) (quaternionHaar_polySmul _ _ _)))

private theorem signed_quadratic (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    let a := projectedEndpointSource w K width (terminalMessage w K width n)
    let h := (1 : Q')-w
    signedRemainder w K width n f ≈
      (HalfPow.half*(h*h))*
        ((-2)*H (N width) (curvatureFlux (List.range (N width)) a f) -
          H (N width) (polyMul (sourceCommutator w K width n f)
            (sourceCommutator w K width n f)) + sourceFirstOrder (N width-1) a f) +
        sourceDebt w K width n f - h*angularWeightDefect w K width n f := by
  dsimp only
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hs := sourceSecondMoment_cancellation (N width-1) _ f
    (by simpa only [hn] using source_supported w K width n)
    (by simpa only [hn] using hf)
  rw [hn] at hs
  have hr := sourceRemainder_secondOrder (N width-1) w K
    (projectedEndpointSource w K width (terminalMessage w K width n)) f
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hr (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hs (Q'.eqv_refl _)))
          (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (Q'.add_eqv_congr' (Q'.add_assoc_eqv _ _ _) (Q'.eqv_refl _)))

private theorem quadratic_mix (k h fp fq sp sq b ap aq epq ep eq dp dq : Q') :
    ((k*((-2)*(fp+fq)-(sp+sq+2*b)+(ap+aq))+epq-h*(dp+dq)) -
      (k*((-2)*fp-sp+ap)+ep-h*dp)) -
      (k*((-2)*fq-sq+aq)+eq-h*dq) ≈
      -(2*k*b)+((epq-ep)-eq) := by
  let F (f s a e d : PolyExpr) : PolyExpr :=
    .add (.add (.mul (.var 0) (.add (.add (.mul (.const (-2)) f) (.neg s)) a)) e)
      (.neg (.mul (.var 1) d))
  exact poly_identity_of_normal_eq
    (.add (.add
      (F (.add (.var 2) (.var 3))
        (.add (.add (.var 4) (.var 5)) (.mul (.const 2) (.var 6)))
        (.add (.var 7) (.var 8)) (.var 9) (.add (.var 12) (.var 13)))
      (.neg (F (.var 2) (.var 4) (.var 7) (.var 10) (.var 12))))
      (.neg (F (.var 3) (.var 5) (.var 8) (.var 11) (.var 13))))
    (.add (.neg (.mul (.mul (.const 2) (.var 0)) (.var 6)))
      (.add (.add (.var 9) (.neg (.var 10))) (.neg (.var 11))))
    (by decide)
    (fun | 0 => k | 1 => h | 2 => fp | 3 => fq | 4 => sp | 5 => sq | 6 => b
         | 7 => ap | 8 => aq | 9 => epq | 10 => ep | 11 => eq | 12 => dp | _ => dq)

private theorem scale_half (h b : Q') :
    (2*(HalfPow.half*(h*h)))*b ≈ (h*h)*b := by
  have halg := poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2))
    (.mul (.mul (.const 2) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
    (by decide) (fun | 0 => HalfPow.half | 1 => h | _ => b)
  exact Q'.eqv_trans _ _ _ halg (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (show (2 : Q')*HalfPow.half ≈ 1 from by decide))
    (Q'.one_mul_eqv _))

/-- Exact ORIGINAL mixed signed remainder: all first-order, angular-weight,
and quadratic source-flux crosses cancel; cubic/cutoff debt remains SIGNED. -/
theorem signedRemainder_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    (signedRemainder w K width n (spatialSpan width c [p,q]) -
      signedRemainder w K width n (spatialSpan width c [p])) -
      signedRemainder w K width n (spatialSpan width c [q]) ≈
    -((((1 : Q')-w)*((1 : Q')-w))*commutatorCross w K width n c p q) +
      mixedDebt w K width n c p q := by
  have ht (qs : List Z4Plaq) := signed_quadratic w K width n
    (spatialSpan width c qs) (spatialSpan_supported width c qs)
  have ht' := ht [p,q]
  have ha := firstOrder_pair w K width n c hd
  have hf := flux_pair w K width n c hd
  have hs := square_pair w K width n c p q
  have hd' := angularWeightDefect_pair w K width n c hd
  have hp := ht [p]
  have hq := ht [q]
  let h : Q' := (1 : Q')-w
  let k : Q' := HalfPow.half*(h*h)
  have he := Q'.add_eqv_congr' (Q'.add_eqv_congr' ht' (Q'.neg_eqv_congr _ _ hp))
    (Q'.neg_eqv_congr _ _ hq)
  have hc := Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left k _ _ (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (-2) _ _ hf)
          (Q'.neg_eqv_congr _ _ hs)) ha))
        (Q'.eqv_refl (sourceDebt w K width n (spatialSpan width c [p,q]))))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left h _ _ hd'))
  refine Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hc (Q'.eqv_refl _)) (Q'.eqv_refl _)) ?_)
  unfold mixedDebt
  exact Q'.eqv_trans _ _ _ (quadratic_mix _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ (scale_half _ _)) (Q'.eqv_refl _))

def mixedEnergy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) : Q' :=
  (normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [p,q]) -
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [p])) -
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [q])

private theorem normalize_mix (a b c z r : Q') (h : z*r ≈ 1) :
    ((a*r-b*r)-c*r)*z ≈ (a-b)-c := by
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.add (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 4))))
      (.neg (.mul (.var 2) (.var 4)))) (.var 3))
    (.mul (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (.mul (.var 3) (.var 4))) (by decide)
    (fun | 0 => a | 1 => b | 2 => c | 3 => z | _ => r)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_one_eqv _)

/-- Direct physical consumer with the SAME original odd partition. Only
strict padding, literal face membership and the original head cutoff occur. -/
theorem mixedEnergy_mass_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K)
    (n : Nat) (c : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    mixedEnergy hw0 hw1 K width hK n c p q * oddMass w K width n ≈
      -((((1 : Q')-w)*((1 : Q')-w))*commutatorCross w K width n c p q) +
        mixedDebt w K width n c p q :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (padded_mixed_energy hw0 hw1 K hwidth hK n c hd hp hq))
    (Q'.eqv_trans _ _ _ (normalize_mix _ _ _ _ _
      (Q'.mul_recipPos_eqv _ (oddMass_positive hw0 hw1 K width hK n)))
      (signedRemainder_pair w K width n c hd))

/-- Sharp bound for the local mixed pairing on the unchanged source. -/
theorem commutatorCross_square_bound (w : Q') (K width n : Nat)
    (c : Z4Plaq → Q') (p q : Z4Plaq) :
    commutatorCross w K width n c p q * commutatorCross w K width n c p q ≤
      commutatorSquare w K width n c p * commutatorSquare w K width n c q :=
  finiteHaar_cauchySchwarz (N width) _ _
    (commutator_supported w K width n _ (spatialSpan_supported width c [p]))
    (commutator_supported w K width n _ (spatialSpan_supported width c [q]))

/-- The full original mixed energy is controlled AFTER subtracting its exact
SIGNED cubic/cutoff debt. No additional sufficientCutoff guard is required.
The source squares are raw Haar quantities, not interacting OWN variance. -/
theorem corrected_mixedEnergy_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    let d := mixedEnergy hw0 hw1 K width hK n c p q * oddMass w K width n -
      mixedDebt w K width n c p q
    let h2 := ((1 : Q')-w)*((1 : Q')-w)
    d*d ≤ (h2*h2)*(commutatorSquare w K width n c p * commutatorSquare w K width n c q) := by
  dsimp only
  have he := Q'.add_eqv_congr' (mixedEnergy_mass_pin hw0 hw1 K hwidth hK n c hd hp hq)
    (Q'.eqv_refl (-mixedDebt w K width n c p q))
  have he' := Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.add (.neg (.mul (.var 0) (.var 1))) (.var 2)) (.neg (.var 2)))
    (.neg (.mul (.var 0) (.var 1))) (by decide)
    (fun | 0 => ((1 : Q')-w)*((1 : Q')-w)
         | 1 => commutatorCross w K width n c p q | _ => mixedDebt w K width n c p q))
  have hs := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he')
    (Q'.mul_eqv_congr_left _ _ _ he')
  have halg := poly_identity_of_normal_eq
    (.mul (.neg (.mul (.var 0) (.var 1))) (.neg (.mul (.var 0) (.var 1))))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
    (fun | 0 => ((1 : Q')-w)*((1 : Q')-w) | _ => commutatorCross w K width n c p q)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hs halg))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (commutatorCross_square_bound w K width n c p q)
      (SumOfSquares.q_mul_self_nonneg _))

#print axioms sourceCommutator
#print axioms sourceCommutator_pair
#print axioms sourceDebt
#print axioms mixedDebt
#print axioms commutatorCross
#print axioms commutatorSquare
#print axioms angularWeightDefect_pair
#print axioms signedRemainder_pair
#print axioms mixedEnergy
#print axioms mixedEnergy_mass_pin
#print axioms commutatorCross_square_bound
#print axioms corrected_mixedEnergy_square_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder
