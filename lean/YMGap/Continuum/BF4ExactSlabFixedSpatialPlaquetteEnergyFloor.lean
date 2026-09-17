/-
# An original physical plaquette pays a local temporal energy floor

Place the same fundamental spatial character at two adjacent original
times. Its upper copy misses a chosen lower link. The selected-star
prediction theorem therefore bounds their squared difference while
retaining the entire original chain action. The existing signed-window
span pin rejoins this difference to the original terminal-message energy
with exactly its original odd-chain partition.

The floor depends on the nome, but not on width, boundary depth, or late
heat cutoff. It concerns one physical plaquette, not arbitrary linear
combinations, an OS spectral gap, or a continuum Hamiltonian.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def differenceSchedule (p : Z4Plaq) : List (Q' × List (Nat × List FaceFactor)) :=
  [(1, [(0, [(p, [(1, 1)])])]), (-1, [(1, [(p, [(1, 1)])])])]

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv (product C [(p, [(1, 1)])]) (C p 1) :=
  ((((RatPolyCoeffEqv.one_smul (C p 1)).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero (C p 1))).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem two_term_pin {p q r s : RatPoly}
    (hp : RatPolyCoeffEqv p r) (hq : RatPolyCoeffEqv q s) :
    RatPolyCoeffEqv
      (polyAdd (polySmul 1 p) (polyAdd (polySmul (-1) q) polyZero))
      (polyAdd r (polyNeg s)) :=
  ((hp.smul 1).trans (RatPolyCoeffEqv.one_smul r)).add
    ((((hq.smul (-1)).trans (smul_neg s)).add (RatPolyCoeffEqv.refl polyZero)).trans
      (RatPolyCoeffEqv.add_zero (polyNeg s)))

-- Only finite schedule bookkeeping reduces; the literal plaquette words stay opaque.
attribute [local irreducible] plaquette correctedSlabPlaquettePolynomial
  baseLinks windowRatio normalizedEnergy

private theorem single_source (width offset : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (windowProbe width [(offset, [(p, [(1, 1)])])])
      (liftBoundary (offset*(N width)) (characterPolynomial (plaquette width p).scalar 1)) :=
  ((lift_coeff (offset*(N width))
    (singleton_product (fun f spin => characterPolynomial (plaquette width f).scalar spin) p)).mul
      (RatPolyCoeffEqv.refl polyOne)).trans (RatPolyCoeffEqv.mul_one _)

private theorem difference_source (width : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (sourceSpan width (differenceSchedule p))
      (jump width (characterPolynomial (plaquette width p).scalar 1)) := by
  have h0 := single_source width 0 p
  have h1 := single_source width 1 p
  simp only [Nat.zero_mul, Nat.one_mul, liftBoundary] at h0 h1
  exact two_term_pin h0 h1

private theorem single_placed (extent start offset : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (sweptProduct extent 0
      (placeWindowProbes start [(offset, [(p, [(1, 1)])])]))
      (faceCharacter extent (timeShiftPlaquette (start+offset) p)) := by
  rw [swept_zero]
  exact singleton_product
    (fun f spin => characterPolynomial (correctedSlabPlaquettePolynomial extent f).scalar spin)
    (timeShiftPlaquette (start+offset) p)

private theorem difference_placed (extent start : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (placedSpan extent start (differenceSchedule p))
      (polynomialError extent (timeShiftPlaquette start p)
        (faceCharacter extent (timeShiftPlaquette (start+1) p))) := by
  have h0 := single_placed extent start 0 p
  have h1 := single_placed extent start 1 p
  simp only [Nat.add_zero] at h0
  exact two_term_pin h0 h1

private theorem schedule_within (p : Z4Plaq) :
    ∀ x, x ∈ differenceSchedule p → ∀ e, e ∈ x.2 → e.1 ≤ 1 := by
  intro x hx e he
  rcases List.mem_cons.mp hx with rfl | hx
  · have h := List.mem_singleton.mp he
    subst e
    exact Nat.zero_le _
  · have h := List.mem_singleton.mp hx
    subst x
    have h := List.mem_singleton.mp he
    subst e
    exact Nat.le_refl _

private theorem schedule_faces {width : Nat} (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    ∀ x, x ∈ differenceSchedule p → ∀ e, e ∈ x.2 →
      ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
  intro x hx e he f hf
  rcases List.mem_cons.mp hx with rfl | hx
  · have h := List.mem_singleton.mp he
    subst e
    have h := List.mem_singleton.mp hf
    subst f
    exact hp
  · have h := List.mem_singleton.mp hx
    subst x
    have h := List.mem_singleton.mp he
    subst e
    have h := List.mem_singleton.mp hf
    subst f
    exact hp

private theorem lower_link_misses_upper {width : Nat} (p : Z4Plaq)
    (hp : p ∈ spatialFaces width) (n : Nat) :
    ((timeShiftPlaquette n p).1, (dirsOf p.2).1) ∉
      edgesOf (timeShiftPlaquette (n+1) p) := by
  have hd := ((spatialFaces_mem_iff width p).mp hp).2.2.2.2
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  cases plane <;> simp only [dirsOf] at hd <;> try exact False.elim (hd rfl)
  all_goals
    intro hm
    have he := hm
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he
    all_goals
      have ht := congrArg (fun l : Z4Link => l.1.2.2.2) he
      change d+n = d+(n+1) at ht
      omega

private theorem finite_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    finiteValue w hw0 hw1 extent ids hids p stage ≈
      finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_right _))

private theorem normalized_prediction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) (s : RatPoly)
    (h : starRatio w * quaternionHaar (B extent)
        (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids) ≤
      quaternionHaar (B extent)
        (polyMul (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids) s)) :
    starRatio w ≤ finiteValue w hw0 hw1 extent ids hids s stage := by
  let A := polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids
  let z := quaternionHaar (B extent) A
  let r := reciprocalTerm w hw0 hw1 extent ids hids stage
  have hz : (0 : Q') < z := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partitionSample_floor w hw0 hw1 extent ids hids stage)
  have hr : z*r ≈ 1 := by
    exact Q'.mul_recipPos_eqv z hz
  have hrpos : (0 : Q') < r := Q'.recipPos_pos z hz
  have hc : (starRatio w*z)*r ≈ starRatio w :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ r h (Q'.le_of_lt hrpos))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ r
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm A s)))))

private theorem stage_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n stage : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    starRatio w ≤ (2 : Q') * normalizedEnergy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n (characterPolynomial (plaquette width p).scalar 1) := by
  let E := width+(n+(1+n))+1
  let c := characterPolynomial (plaquette width p).scalar 1
  let lower := timeShiftPlaquette n p
  let upper := timeShiftPlaquette (n+1) p
  let q := faceCharacter E upper
  let err := polynomialError E lower q
  let ids := chainIds E width 0 (n+(1+n))
  have hw : width ≤ E := by dsimp [E]; omega
  have ht : 0+(n+(1+n)) ≤ E := by dsimp [E]; omega
  have hface : lower ∈ boundaryCompleteSlabPlaquettes E :=
    spatialFaces_shift_physical (by omega) (by dsimp [E]; omega) hp
  have hl : (lower.1, (dirsOf p.2).1) ∈ edgesOf lower := List.mem_cons_self
  have hpred := polynomial_square_floor hw0 hw1 (headCutoff w+stage) E
    (Nat.le_add_right _ _) ids (fun _ hi => chainIds_physical hi) (chainIds_nodup _ _ _ _)
    hface _ hl q (faceCharacter_supported E upper) (edgesOf upper)
    ((face_scalar_local E upper).character 1) (lower_link_misses_upper p hp n)
  have hfloor := normalized_prediction hw0 hw1 E ids (fun _ hi => chainIds_physical hi)
    stage (polyMul err err) hpred
  have hsource := difference_source width p
  have hplaced := difference_placed E n p
  have hpin : windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      n 1 n (polyMul (jump width c) (jump width c)) ≈
      finiteValue w hw0 hw1 E ids (fun _ hi => chainIds_physical hi) (polyMul err err) stage :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) n 1 n (hsource.mul hsource).symm)
      (Q'.eqv_trans _ _ _
        (windowRatio_span_mul_originalFiniteValue hw0 hw1 (start := 0) (m := n) (L := 1) (n := n)
          hw ht (differenceSchedule p) (differenceSchedule p)
          (schedule_within p) (schedule_faces p hp) (schedule_within p) (schedule_faces p hp) stage)
        (finite_congr hw0 hw1 E ids (fun _ hi => chainIds_physical hi) stage
          (by simpa only [Nat.zero_add] using hplaced.mul hplaced)))
  have he := normalizedEnergy_window hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) n
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1)
  exact Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ he hpin))

/-- The explicit same-action energy floor for every physical spatial plaquette.
The nome-dependent coefficient is independent of width, late cutoff and depth. -/
theorem plaquette_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    starRatio w ≤ (2 : Q') * normalizedEnergy hw0 hw1 K width hK n
      (characterPolynomial (plaquette width p).scalar 1) := by
  have h := stage_energy_floor hw0 hw1 width n (K-headCutoff w) p hp
  simpa only [Nat.add_sub_of_le hK] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.plaquette_energy_floor
