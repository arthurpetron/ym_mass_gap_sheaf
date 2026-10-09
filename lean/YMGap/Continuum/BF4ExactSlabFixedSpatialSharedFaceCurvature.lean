/-
# Local shared-face Casimir frontend

Only finite local/original-carrier consequences are recorded here.  The
eventual `20*Gamma - 6*p*q` identification is intentionally not asserted.
-/
import YMGap.Continuum.QuaternionHaarMixedLinearCasimir
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
import YMGap.Continuum.Z4DistinctPlaquetteIntersection
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.CayleyParentInj
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSharedFaceCurvature
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
  (plaquette_character_degree)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
  (blockRow blockRow_iff blockRow_character_independent blockRow_derivative_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
  (incident_mem_baseLinks)
open YMGap.Continuum.Z4DistinctPlaquetteIntersection
  (common_boundary_links_equal_of_faces_ne)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
  (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm mem_of_mem_erase not_mem_erase)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
  (activeCasimirPolynomial)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
  (character_supported)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
  (activeGamma blockGamma)
open YMGap.Continuum.QuaternionHaarMixedLinearCasimir
  (blockGamma_linear_casimir)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks plaquette

private theorem gamma_perm (f g : RatPoly) {xs ys : List Nat} (h : xs.Perm ys) :
    RatPolyCoeffEqv (activeGamma xs f g) (activeGamma ys f g) := by
  induction h with
  | nil => exact .refl _
  | cons i _ ih => exact (RatPolyCoeffEqv.refl _).add ih
  | swap i j rest =>
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => blockGamma j f g | 1 => blockGamma i f g
             | _ => activeGamma rest f g)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem gamma_zero (f g : RatPoly) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → RatPolyCoeffEqv (blockGamma i f g) polyZero) →
    RatPolyCoeffEqv (activeGamma ids f g) polyZero
  | [], _ => .refl _
  | i::ids, h =>
      ((h i List.mem_cons_self).add
        (gamma_zero f g ids
          (fun j hj => h j (List.mem_cons_of_mem i hj)))).trans
        (RatPolyCoeffEqv.add_zero _)

private theorem off_shared_row
    (width b : Nat) (p q : Z4Plaq) (l : Z4Link)
    (_hp : p ∈ spatialFaces width) (_hq : q ∈ spatialFaces width)
    (hne : p ≠ q) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q)
    (_hb : b < N width) (hidx : (baseLinks width).idxOf l ≠ b) :
    blockRow width b p = false ∨ blockRow width b q = false := by
  by_cases hpr : blockRow width b p = false
  · exact Or.inl hpr
  · right
    cases hqrow : blockRow width b q with
    | false => exact rfl
    | true =>
        have hpr' : blockRow width b p = true := by
          cases h : blockRow width b p with
          | false => exact False.elim (hpr h)
          | true => exact rfl
        obtain ⟨m, hm, hmp, hmb⟩ := (blockRow_iff width b p).mp hpr'
        obtain ⟨n, hn, hnq, hnb⟩ := (blockRow_iff width b q).mp hqrow
        have hmn : m = n := idxOf_injective_on_members hmp hnq
          (hmb.trans hnb.symm)
        subst n
        have hml := common_boundary_links_equal_of_faces_ne p q hne m l
          hm hlp hn hlq
        subst m
        exact False.elim (hidx (hmb.trans rfl))

private theorem off_shared_gamma
    (width b : Nat) (p q : Z4Plaq) (l : Z4Link)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width)
    (hne : p ≠ q) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q)
    (hb : b < N width) (hidx : (baseLinks width).idxOf l ≠ b) :
    RatPolyCoeffEqv
      (blockGamma b
        (characterPolynomial (plaquette width p).scalar 1)
        (characterPolynomial (plaquette width q).scalar 1)) polyZero := by
  have hoff := off_shared_row width b p q l hp hq hne hlp hlq hb hidx
  unfold blockGamma six
  have hz (i j : Nat) (hi : i < 4) (hj : j < 4) :
      RatPolyCoeffEqv
        (polyMul (blockAngularDerivative b i j
          (characterPolynomial (plaquette width p).scalar 1))
          (blockAngularDerivative b i j
            (characterPolynomial (plaquette width q).scalar 1))) polyZero := by
    rcases hoff with hpoff | hqoff
    · exact ((blockRow_derivative_zero width b p hb hpoff hi hj).mul_right _).trans
        (RatPolyCoeffEqv.mul_zero_left _)
    · exact ((blockRow_derivative_zero width b q hb hqoff hi hj).mul_left _).trans
        (RatPolyCoeffEqv.mul_zero_right _)
  exact ((hz 0 1 (by decide) (by decide)).add
    ((hz 0 2 (by decide) (by decide)).add
      ((hz 0 3 (by decide) (by decide)).add
        ((hz 1 2 (by decide) (by decide)).add
          ((hz 1 3 (by decide) (by decide)).add
            (hz 2 3 (by decide) (by decide))))))).trans
      (RatPolyCoeffEqv.refl _)

/-- Singleton shared-block Casimir law for two actual incident characters. -/
theorem incident_pair_gamma_casimir
    (width : Nat) (p q : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width)
    (l : Z4Link) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q) :
    let fp := characterPolynomial (plaquette width p).scalar 1
    let fq := characterPolynomial (plaquette width q).scalar 1
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial [((baseLinks width).idxOf l)]
        (blockGamma ((baseLinks width).idxOf l) fp fq))
      (polyAdd (polySmul 2 (blockGamma ((baseLinks width).idxOf l) fp fq))
        (polySmul (-6) (polyMul fp fq))) := by
  dsimp only
  let s := (baseLinks width).idxOf l
  have hsl : s < N width := List.idxOf_lt_length_of_mem
    (incident_mem_baseLinks hp hlp)
  have hps : SupportedQuaternionBlocks (N width)
      (characterPolynomial (plaquette width p).scalar 1) :=
    character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1
  have hqs : SupportedQuaternionBlocks (N width)
      (characterPolynomial (plaquette width q).scalar 1) :=
    character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) q).scalar 1
  exact blockGamma_linear_casimir hsl _ _ hps hqs
    (plaquette_character_degree width hp hlp)
    (plaquette_character_degree width hq hlq)

/-- For distinct faces sharing `l`, active Gamma localizes to the shared
physical block.  No full shared-face polynomial formula is claimed. -/
theorem distinct_pair_activeGamma_localizes
    (width : Nat) (p q : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width)
    (hne : p ≠ q) (l : Z4Link)
    (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q) :
    let fp := characterPolynomial (plaquette width p).scalar 1
    let fq := characterPolynomial (plaquette width q).scalar 1
    HaarCarrierEqv (N width)
      (activeGamma (List.range (N width)) fp fq)
      (blockGamma ((baseLinks width).idxOf l) fp fq) := by
  dsimp only
  let fp := characterPolynomial (plaquette width p).scalar 1
  let fq := characterPolynomial (plaquette width q).scalar 1
  let s := (baseLinks width).idxOf l
  have hs : s < N width := List.idxOf_lt_length_of_mem
    (incident_mem_baseLinks hp hlp)
  have hperm := select_perm s (List.mem_range.mpr hs)
  have hz := gamma_zero fp fq (eraseIndex s (List.range (N width)))
    (fun b hb => off_shared_gamma width b p q l hp hq hne hlp hlq
      (List.mem_range.mp (mem_of_mem_erase s hb))
      (fun hsb => by
        have hmem : s ∈ eraseIndex s (List.range (N width)) := by
          cases hsb
          exact hb
        exact (not_mem_erase s (ids := List.range (N width))
          (YMGap.Continuum.CayleyParentInj.range_nodup _)) hmem))
  exact (RatPolyCoeffEqv.haarCarrier (gamma_perm fp fq hperm)).trans
    (((RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add hz))).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)))

#print axioms incident_pair_gamma_casimir
#print axioms distinct_pair_activeGamma_localizes
end YMGap.Continuum.BF4ExactSlabFixedSpatialSharedFaceCurvature
