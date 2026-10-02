/-
# Exact mixed energy for literal link-disjoint original faces

Literal edge disjointness kills the first-order angular cross term, block by
block and before integration. Thus the SAME original odd-marginal angular
energy is additive on the two signed singleton spans. The temporal energy
need not be additive: its entire mixed contribution is the mixed COMPLETE
signed Taylor remainder, including the angular change-of-weight defect.

The finite Wilson-window consumer retains its original cutoff/depth schedule.
No interacting covariance is set to zero; no remainder sign, useful margin,
scaling rate, spatial uniformity or continuum/Clay conclusion is proved.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
import YMGap.Continuum.SU2QuaternionActiveCasimirProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (squareAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (blockGamma)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_add)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks plaquette marginalWeight originalWindowScalar

/-- This is literal link geometry, not probabilistic independence. -/
def LinkDisjoint (p q : Z4Plaq) : Prop :=
  ∀ link, link ∈ edgesOf p → link ∈ edgesOf q → False

/-- A finite, computable test using the four actual edges of each face. -/
def linkDisjoint (p q : Z4Plaq) : Bool :=
  (edgesOf p).all (fun link => decide (link ∉ edgesOf q))

theorem linkDisjoint_correct (p q : Z4Plaq) :
    linkDisjoint p q = true ↔ LinkDisjoint p q := by
  unfold linkDisjoint LinkDisjoint
  constructor
  · intro h link hp hq
    exact (of_decide_eq_true (List.all_eq_true.mp h link hp)) hq
  · intro h
    exact List.all_eq_true.mpr (fun link hp => decide_eq_true (h link hp))

/-- Two disjoint faces cannot both contain the same physical link index. -/
theorem blockRow_separate (width b : Nat) {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    blockRow width b p = false ∨ blockRow width b q = false := by
  cases hp : blockRow width b p with
  | false => exact Or.inl rfl
  | true =>
      cases hq : blockRow width b q with
      | false => exact Or.inr rfl
      | true =>
          obtain ⟨lp, hep, hlp, hip⟩ := (blockRow_iff width b p).mp hp
          obtain ⟨lq, heq, hlq, hiq⟩ := (blockRow_iff width b q).mp hq
          have he : lp = lq := idxOf_injective_on_members hlp hlq (hip.trans hiq.symm)
          exact False.elim (hd lp hep (he.symm ▸ heq))

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

/-- Every mixed angular term vanishes coefficientwise, before weighting.
The guard is the actual physical block range, not all formal indices. -/
theorem blockGamma_zero (width b : Nat) {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hb : b < N width) :
    RatPolyCoeffEqv
      (blockGamma b (characterPolynomial (plaquette width p).scalar 1)
        (characterPolynomial (plaquette width q).scalar 1)) polyZero := by
  unfold blockGamma
  apply six_congr (b := fun _ _ => polyZero)
  intro i j hi hj
  rcases blockRow_separate width b hd with hp | hq
  · exact ((blockRow_derivative_zero width b p hb hp hi hj).mul_right _).trans
      (RatPolyCoeffEqv.mul_zero_left _)
  · exact ((blockRow_derivative_zero width b q hb hq hi hj).mul_left _).trans
      (RatPolyCoeffEqv.mul_zero_right _)

private theorem singleton_pin (width : Nat) (c : Z4Plaq → Q') (p : Z4Plaq) :
    RatPolyCoeffEqv (spatialSpan width c [p])
      (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1)) :=
  RatPolyCoeffEqv.add_zero _

private theorem pair_pin (width : Nat) (c : Z4Plaq → Q') (p q : Z4Plaq) :
    RatPolyCoeffEqv (spatialSpan width c [p,q])
      (polyAdd (spatialSpan width c [p]) (spatialSpan width c [q])) :=
  (singleton_pin width c p).symm.add (RatPolyCoeffEqv.refl _)

private theorem singleton_derivative_zero (width b : Nat) (c : Z4Plaq → Q')
    (p : Z4Plaq) (hb : b < N width) (hoff : blockRow width b p = false)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (blockAngularDerivative b i j (spatialSpan width c [p])) polyZero :=
  (angularDerivative_congr _ _ (singleton_pin width c p)).trans
    ((angularDerivative_smul _ _ _ _).trans
      (((blockRow_derivative_zero width b p hb hoff hi hj).smul (c p)).trans
        (RatPolyCoeffEqv.smul_zero _)))

private theorem square_add_of_zero (u v : RatPoly)
    (hz : RatPolyCoeffEqv u polyZero ∨ RatPolyCoeffEqv v polyZero) :
    RatPolyCoeffEqv (polyMul (polyAdd u v) (polyAdd u v))
      (polyAdd (polyMul u u) (polyMul v v)) := by
  rcases hz with hu | hv
  · have hs := (hu.add (RatPolyCoeffEqv.refl v)).trans (RatPolyCoeffEqv.zero_add v)
    have hsq := (hu.mul hu).trans (RatPolyCoeffEqv.mul_zero_left polyZero)
    exact (hs.mul hs).trans
      ((hsq.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)).symm
  · have hs := ((RatPolyCoeffEqv.refl u).add hv).trans (RatPolyCoeffEqv.add_zero u)
    have hsq := (hv.mul hv).trans (RatPolyCoeffEqv.mul_zero_left polyZero)
    exact (hs.mul hs).trans
      (((RatPolyCoeffEqv.refl _).add hsq).trans (RatPolyCoeffEqv.add_zero _)).symm

/-- Exact additivity of the first-order angular polynomial on each actual
block, for arbitrary signed coefficients. It is NOT temporal-energy additivity. -/
theorem blockAngularSquare_pair (width b : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) (hb : b < N width) :
    RatPolyCoeffEqv (blockAngularSquare b (spatialSpan width c [p,q]))
      (polyAdd (blockAngularSquare b (spatialSpan width c [p]))
        (blockAngularSquare b (spatialSpan width c [q]))) := by
  unfold blockAngularSquare
  refine (six_congr (fun i j hi hj => ?_)).trans (six_add _ _)
  have hder : RatPolyCoeffEqv
      (blockAngularDerivative b i j (spatialSpan width c [p,q]))
      (polyAdd (blockAngularDerivative b i j (spatialSpan width c [p]))
        (blockAngularDerivative b i j (spatialSpan width c [q]))) :=
    (angularDerivative_congr _ _ (pair_pin width c p q)).trans
      (angularDerivative_add _ _ _ _)
  refine (hder.mul hder).trans (square_add_of_zero _ _ ?_)
  rcases blockRow_separate width b hd with hp | hq
  · exact Or.inl (singleton_derivative_zero width b c p hb hp hi hj)
  · exact Or.inr (singleton_derivative_zero width b c q hb hq hi hj)

/-- SAME arbitrary weight on all three spans; no factorization or source
independence is needed. In particular the original Wilson weight is allowed. -/
theorem weightedAngular_pair (width : Nat) (W : RatPoly) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    finSum (fun b => quaternionHaar (N width)
      (polyMul W (blockAngularSquare b (spatialSpan width c [p,q])))) (N width) ≈
      finSum (fun b => quaternionHaar (N width)
        (polyMul W (blockAngularSquare b (spatialSpan width c [p])))) (N width) +
      finSum (fun b => quaternionHaar (N width)
        (polyMul W (blockAngularSquare b (spatialSpan width c [q])))) (N width) := by
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ (N width) (fun b hb => ?_))
    (finSum_add _ _ _)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((blockAngularSquare_pair width b c hd hb).mul_left W))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W _ _))
      (quaternionHaar_append _ _ _))

/-- The literal original density V*g_n*g_(n+1) is unchanged. -/
theorem marginalAngular_pair (w : Q') (K width n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    marginalAngular w K width n (spatialSpan width c [p,q]) ≈
      marginalAngular w K width n (spatialSpan width c [p]) +
      marginalAngular w K width n (spatialSpan width c [q]) :=
  weightedAngular_pair width (marginalWeight w K width n) c hd

/-- All three normalized terms use one original odd partition. -/
theorem normalizedAngular_pair {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    normalizedAngular hw0 hw1 K width hK n (spatialSpan width c [p,q]) ≈
      normalizedAngular hw0 hw1 K width hK n (spatialSpan width c [p]) +
      normalizedAngular hw0 hw1 K width hK n (spatialSpan width c [q]) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (marginalAngular_pair w K width n c hd))
    (Q'.add_mul_eqv _ _ _)

private theorem mixed_cancel (h a b r rp rq : Q') :
    ((h*(a+b)+r)-(h*a+rp))-(h*b+rq) ≈ (r-rp)-rq :=
  poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.neg (.add (.mul (.var 0) (.var 1)) (.var 4))))
      (.neg (.add (.mul (.var 0) (.var 2)) (.var 5))))
    (.add (.add (.var 3) (.neg (.var 4))) (.neg (.var 5)))
    (by decide) (fun | 0 => h | 1 => a | 2 => b | 3 => r | 4 => rp | _ => rq)

/-- The entire ORIGINAL mixed temporal energy is retained as the mixed
complete signed remainder. Literal disjointness does NOT kill this remainder. -/
theorem padded_mixed_energy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K)
    (n : Nat) (c : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    (normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [p,q]) -
      normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [p])) -
      normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c [q]) ≈
    (normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c [p,q]) -
      normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c [p])) -
      normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c [q]) := by
  have hpq : ∀ f, f ∈ [p,q] → f ∈ spatialFaces base := by
    intro f hf
    rcases List.mem_cons.mp hf with he | he
    · exact he.symm ▸ hp
    · exact (List.mem_singleton.mp he).symm ▸ hq
  have hs (f : Z4Plaq) (hf : f ∈ spatialFaces base) :
      ∀ g, g ∈ [f] → g ∈ spatialFaces base :=
    fun g hg => (List.mem_singleton.mp hg).symm ▸ hf
  have e := padded_family_normalized_taylor hw0 hw1 K hwidth hK n [p,q] c hpq
  have ep := padded_family_normalized_taylor hw0 hw1 K hwidth hK n [p] c (hs p hp)
  have eq := padded_family_normalized_taylor hw0 hw1 K hwidth hK n [q] c (hs q hq)
  have a := normalizedAngular_pair hw0 hw1 K width hK n c hd
  have e' := Q'.eqv_trans _ _ _ e
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ a))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' e' (Q'.neg_eqv_congr _ _ ep))
      (Q'.neg_eqv_congr _ _ eq))
    (mixed_cancel _ _ _ _ _ _)

private theorem singleton_faces {base : Nat} (p : Z4Plaq) (hp : p ∈ spatialFaces base) :
    ∀ f, f ∈ [p] → f ∈ spatialFaces base :=
  fun _ hf => (List.mem_singleton.mp hf).symm ▸ hp

private theorem pair_faces {base : Nat} (p q : Z4Plaq)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    ∀ f, f ∈ [p,q] → f ∈ spatialFaces base := by
  intro f hf
  rcases List.mem_cons.mp hf with he | he
  · exact he.symm ▸ hp
  · exact (List.mem_singleton.mp he).symm ▸ hq

private theorem mixed_scale (a b c : Q') :
    ((2 : Q')*a-2*b)-2*c ≈ 2*((a-b)-c) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
      (.neg (.mul (.const 2) (.var 2))))
    (.mul (.const 2) (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

/-- Direct original finite-window consumer. Subtracting the two singleton
squared increments leaves twice the mixed COMPLETE signed remainder, at
the original cutoff headCutoff(w)+stage and the SAME endpoint depth. -/
theorem finite_mixed_increment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) (stage depth : Nat) :
    let ep := familyExpression width [p] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (singleton_faces p hp f hf))
    let eq := familyExpression width [q] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (singleton_faces q hq f hf))
    let epq := familyExpression width [p,q] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (pair_faces p q hp hq f hf))
    (originalWindowScalar hw0 hw1 1 (squareAt epq 1) stage depth depth -
      originalWindowScalar hw0 hw1 1 (squareAt ep 1) stage depth depth) -
      originalWindowScalar hw0 hw1 1 (squareAt eq 1) stage depth depth ≈
    2*((normalizedRemainder hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        depth (spatialSpan width c [p,q]) -
      normalizedRemainder hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        depth (spatialSpan width c [p])) -
      normalizedRemainder hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        depth (spatialSpan width c [q])) := by
  dsimp only
  have ep := BF4WilsonPlaquetteFamilyIncrement.finite_family_increment_pin
    hw0 hw1 width [p] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (singleton_faces p hp f hf)) stage depth
  have eq := BF4WilsonPlaquetteFamilyIncrement.finite_family_increment_pin
    hw0 hw1 width [q] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (singleton_faces q hq f hf)) stage depth
  have epq := BF4WilsonPlaquetteFamilyIncrement.finite_family_increment_pin
    hw0 hw1 width [p,q] c (fun f hf =>
      BF4ExactSlabFixedSpatialBaseInclusion.spatialFaces_mono (Nat.le_of_lt hwidth)
        (pair_faces p q hp hq f hf)) stage depth
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' epq (Q'.neg_eqv_congr _ _ ep))
      (Q'.neg_eqv_congr _ _ eq))
    (Q'.eqv_trans _ _ _ (mixed_scale _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (padded_mixed_energy hw0 hw1 _ hwidth (Nat.le_add_right _ _) depth c hd hp hq)))

/-- A concrete spatial pair in a base-two box. This is a genuine geometric
instance, not a favorable energy, covariance or signed-margin instance. -/
def exampleP : Z4Plaq := ((0,0,0,0), Z4Plane.p01)
def exampleQ : Z4Plaq := ((0,0,1,0), Z4Plane.p01)

theorem example_disjoint : LinkDisjoint exampleP exampleQ :=
  (linkDisjoint_correct exampleP exampleQ).mp (by decide)

theorem example_spatial : exampleP ∈ spatialFaces 2 ∧ exampleQ ∈ spatialFaces 2 :=
  ⟨(spatialFaces_mem_iff 2 exampleP).mpr (by decide),
    (spatialFaces_mem_iff 2 exampleQ).mpr (by decide)⟩

#print axioms LinkDisjoint
#print axioms linkDisjoint
#print axioms linkDisjoint_correct
#print axioms blockRow_separate
#print axioms blockGamma_zero
#print axioms blockAngularSquare_pair
#print axioms weightedAngular_pair
#print axioms marginalAngular_pair
#print axioms normalizedAngular_pair
#print axioms padded_mixed_energy
#print axioms finite_mixed_increment
#print axioms exampleP
#print axioms exampleQ
#print axioms example_disjoint
#print axioms example_spatial

end YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
