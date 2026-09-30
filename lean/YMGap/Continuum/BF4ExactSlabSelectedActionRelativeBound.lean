/-
# Relative angular bound for the original selected physical action

The supplied finite physical face list is retained exactly.  The selected
link is moved to the Haar head, its incident heat factors are bounded one at
a time, and the complementary product is kept with zero head derivative.
The six-face constant comes from the physical link star and the explicit
late-cutoff condition remains visible.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.BF4ExactSlabHeatAngularInterval
import YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_slabPlaquette)
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection (linkLocal_degree_zero)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headProduct_certificate)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (degree_zero_independent)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (prefixInterval)
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "blockCount" extent:arg =>
  List.length (boundaryCompleteSlabLinks extent)

attribute [local irreducible] correctedSlabPlaquettePolynomial boundaryCompleteSlabLinks

private theorem supported_reindex {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (p : PolyQuaternion) : Supported blocks (reindexPolyQuaternion s p) :=
  ⟨reindex_supported s p.scalar, reindex_supported s p.iPart,
    reindex_supported s p.jPart, reindex_supported s p.kPart⟩

private theorem supported_polyQuaternionNorm {blocks : Nat} {p : PolyQuaternion}
    (hp : Supported blocks p) : SupportedQuaternionBlocks blocks (polyQuaternionNorm p) := by
  unfold polyQuaternionNorm
  exact supported_add (supported_polyMul hp.scalar hp.scalar)
    (supported_add (supported_polyMul hp.iPart hp.iPart)
      (supported_add (supported_polyMul hp.jPart hp.jPart)
        (supported_polyMul hp.kPart hp.kPart)))

private theorem norm_reindex {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (p : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (reindexPolyQuaternion s p))
      (reindexQuaternionPolynomial s (polyQuaternionNorm p)) := by
  unfold polyQuaternionNorm reindexPolyQuaternion
  simp only [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul]
  exact RatPolyCoeffEqv.refl _

private theorem reindex_scalar_unit {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {p : PolyQuaternion} (hp : Supported blocks p)
    (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv blocks (polyQuaternionNorm (reindexPolyQuaternion s p)) polyOne := by
  have hn := RatPolyCoeffEqv.haarCarrier (blocks := blocks) (norm_reindex s p)
  have hr := reindex_carrier s (supported_polyQuaternionNorm hp)
    (supported_one blocks) hu
  have hOne : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s polyOne) polyOne :=
    carrierOfPrefix (reindex_supported s polyOne) (supported_one blocks)
      (reindex_polyOne_prefix s)
  exact hn.trans (hr.trans hOne)

private theorem reindexHeatPrefixPrefix {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (w : Q') (x : RatPoly) : ∀ ids : List Nat,
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (finitePolySum
        (fun d => polySmul (coeffW w d) (characterPolynomial x d)) ids))
      (finitePolySum
        (fun d => polySmul (coeffW w d)
          (characterPolynomial (reindexQuaternionPolynomial s x) d)) ids)
  | [] => .nil
  | d :: ids => by
      change QuaternionPrefixPolynomialEqv blocks
        (reindexQuaternionPolynomial s (polyAdd
          (polySmul (coeffW w d) (characterPolynomial x d))
          (finitePolySum (fun k => polySmul (coeffW w k)
            (characterPolynomial x k)) ids))) _
      rw [reindexQuaternionPolynomial_add]
      apply QuaternionPrefixPolynomialEqv.append
      · rw [reindexQuaternionPolynomial_smul]
        exact QuaternionPrefixPolynomialEqv.smul (coeffW w d)
          (reindexQuaternionPolynomial_character_prefix s x d)
      · exact reindexHeatPrefixPrefix s w x ids

private theorem reindexProductPrefix {A : Type} {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) (f : A → RatPoly) : ∀ ids : List A,
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (polynomialProduct f ids))
      (polynomialProduct (fun a => reindexQuaternionPolynomial s (f a)) ids)
  | [] => reindex_polyOne_prefix s
  | a :: ids => by
      change QuaternionPrefixPolynomialEqv blocks
        (reindexQuaternionPolynomial s (polyMul (f a) (polynomialProduct f ids))) _
      rw [reindexQuaternionPolynomial_mul]
      exact (QuaternionPrefixPolynomialEqv.refl blocks _).mul
        (reindexProductPrefix s f ids)

private theorem supportedProduct {A : Type} {blocks : Nat} (f : A → RatPoly) :
    ∀ ids : List A, (∀ a, a ∈ ids → SupportedQuaternionBlocks blocks (f a)) →
      SupportedQuaternionBlocks blocks (polynomialProduct f ids)
  | [], _ => supported_one blocks
  | a :: ids, hf => by
      change SupportedQuaternionBlocks blocks (polyMul (f a) (polynomialProduct f ids))
      exact supported_polyMul (hf a List.mem_cons_self)
        (supportedProduct f ids (fun b hb => hf b (List.mem_cons_of_mem a hb)))

private def carrier_relative {blocks i j : Nat} {p q : RatPoly} {c : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : SupportedQuaternionBlocks blocks p)
    (h : HaarCarrierEqv blocks p q)
    (P : RelativeBound blocks i j q c) : RelativeBound blocks i j p c := by
  let hd := angularDerivative_carrier hb hi hj h
  exact {
    positive := .transport h P.positive
    nonnegative := P.nonnegative
    upper := .transport
      (HaarCarrierEqv.add (HaarCarrierEqv.mul_left (cap c) h)
        (HaarCarrierEqv.neg hd)) P.upper
    lower := .transport
      (HaarCarrierEqv.add (HaarCarrierEqv.mul_left (cap c) h) hd) P.lower
  }

private def reindexedHeatRelativeBound {blocks i j : Nat} {w : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : QuaternionBlockInvolution blocks) (q : PolyQuaternion)
    (hq : Supported blocks q) (hunit : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne)
    (DX : QuaternionHaarPolynomialInterval.Interval blocks
      (angularDerivative i j (reindexQuaternionPolynomial s q.scalar)) 2048)
    (K : Nat) (hK : relativeCutoff w 2048 ≤ K) :
    RelativeBound blocks i j (reindexQuaternionPolynomial s (heatPrefix w K q.scalar))
      (relativeCap w 2048) := by
  have hqr : Supported blocks (reindexPolyQuaternion s q) := supported_reindex s q
  have hur := reindex_scalar_unit s hq hunit
  have P := heatPrefixRelativeBoundAt hw0 hw1 (by omega) (by omega)
    hqr hur DX K hK
  have hprefix : QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (heatPrefix w K q.scalar))
      (heatPrefix w K (reindexQuaternionPolynomial s q.scalar)) :=
    reindexHeatPrefixPrefix s w q.scalar (List.range (K+1))
  have hsupp := reindex_supported s (heatPrefix w K q.scalar)
  have hpsupp := (prefixInterval hw0 hw1
    (SquareBound.scalar hqr hur) K).support
  have hc := carrierOfPrefix hsupp hpsupp hprefix
  exact carrier_relative hb hi hj hsupp hc P

/-- A single literal physical face heat factor retains the original relative
constant. The generic witness keeps its large dependent word opaque. -/
private def selectedFaceRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : relativeCutoff w 2048 ≤ K)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (blockCount extent) i j
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (faceHeatPolynomial w K extent id)) (relativeCap w 2048) := by
  have hb := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  rw [faceHeatPolynomial_eq_sum]
  exact reindexedHeatRelativeBound hb hi hj hw0 hw1 (linkHeadSwap extent link hl)
    (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id))
    (supported_slabPlaquette extent (slabPlaquetteAt extent id))
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hid))
    (selectedPlaquetteAngularInterval hi hj extent link hl (slabPlaquetteAt extent id)) K hK

private theorem star_mem {extent : Nat} {ids : List Nat} {link : Z4Link} {id : Nat}
    (h : id ∈ selectedStar extent ids link) :
    id ∈ ids ∧ link ∈ edgesOf (slabPlaquetteAt extent id) := by
  simpa only [selectedStar, List.mem_filter, decide_eq_true_eq] using h

private theorem rest_mem {extent : Nat} {ids : List Nat} {link : Z4Link} {id : Nat}
    (h : id ∈ selectedRest extent ids link) :
    id ∈ ids ∧ link ∉ edgesOf (slabPlaquetteAt extent id) := by
  simpa only [selectedRest, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] using h

private def incidentRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : relativeCutoff w 2048 ≤ K)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    (∀ id, id ∈ ids → link ∈ edgesOf (slabPlaquetteAt extent id)) →
    RelativeBound (blockCount extent) i j
      (polynomialProduct (fun id =>
        reindexQuaternionPolynomial (linkHeadSwap extent link hl)
          (faceHeatPolynomial w K extent id)) ids)
      (Q'.ofNat ids.length * relativeCap w 2048)
  | [], _, _ =>
      (RelativeBound.ofCoeff (RatPolyCoeffEqv.one_smul polyOne).symm
        (RelativeBound.constant (blockCount extent) _ _ 1 Q'.zero_le_one)).changeCap
          (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | id :: ids, hids, hinc => by
      have F := selectedFaceRelativeBound hw0 hw1 K extent hK link hl id
        (hids id List.mem_cons_self) hi hj
      have T := incidentRelativeBound hw0 hw1 K extent hK link hl hi hj ids
        (fun k hk => hids k (List.mem_cons_of_mem id hk))
        (fun k hk => hinc k (List.mem_cons_of_mem id hk))
      have hpoly := poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.var 1) (.const 1)) (.var 0)) (by decide)
        (fun | 0 => relativeCap w 2048 | _ => Q'.ofNat ids.length)
      have hnat : Q'.eqv (Q'.ofNat ids.length + 1) (Q'.ofNat (id :: ids).length) := by
        simpa only [List.length_cons, Nat.succ_eq_add_one] using
          Q'.eqv_symm (Q'.ofNat_add_eqv ids.length 1)
      exact (F.mul T).changeCap (Q'.eqv_trans _ _ _ hpoly
        (Q'.mul_eqv_congr_right _ _ _ hnat))

/-- The actual physical action on the supplied list of IDs, reindexed to
the selected link's head. Repetitions are excluded explicitly because the
six-face count is a geometric count of distinct faces. -/
def selectedActionRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : relativeCutoff w 2048 ≤ K)
    (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (blockCount extent) i j
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (polynomialProduct (faceHeatPolynomial w K extent) ids))
      (6 * relativeCap w 2048) := by
  let s := linkHeadSwap extent link hl
  have hb : 0 < blockCount extent :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  let I := selectedStar extent ids link
  let C := selectedRest extent ids link
  have hI := incidentRelativeBound hw0 hw1 K extent hK link hl hi hj I
    (fun id hi => hids id (star_mem hi).1)
    (fun id hi => (star_mem hi).2)
  have hIcap : Q'.ofNat I.length * relativeCap w 2048 ≤
      6 * relativeCap w 2048 := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (CReal.ofNat_le_ofNat (selectedStar_length_le_six extent ids hids hnodup link))
      (Q'.le_of_lt (relativeCap_positive hw0 (by decide)))
  have hI' := hI.weaken hIcap
  have hCphys : ∀ id, id ∈ C → id ∈ slabPhysicalFaceEdges extent :=
    fun id hi => hids id (rest_mem hi).1
  have hCcertificate := headProduct_certificate hw0 hw1 K extent
    (Nat.le_trans (headCutoff_le_relativeCutoff w 2048) hK) C hCphys
  have hfree : link ∉ faceLinks extent C := by
    intro hm
    obtain ⟨id, hi, hedge⟩ := List.mem_flatMap.mp hm
    exact (rest_mem hi).2 hedge
  have hlocal := heatProduct_local w K extent C
  have hdegree := linkLocal_degree_zero hlocal link hl hfree
  have hdegreeHead := blockDegree_reindex s (by omega)
    (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl)) hdegree
  have hindependent := degree_zero_independent hdegreeHead
  have hD := angularDerivative_blockIndependent_zero hi hj hindependent
  have hC : RelativeBound (blockCount extent) i j
      (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) C)) 0 :=
    RelativeBound.ofZeroDerivative (reindex_certificate s
      (heatProduct_supported w K extent C) hCcertificate) (by
        simpa [Nat.zero_mul, Nat.zero_add] using hD)
  have hprod := hI'.mul hC
  have hsum : Q'.eqv (6 * relativeCap w 2048 + 0) (6 * relativeCap w 2048) :=
    QPoly.q_add_zero_eqv (6 * relativeCap w 2048)
  have hprod' := hprod.changeCap hsum
  have hpart : HaarCarrierEqv (blockCount extent)
      (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) ids))
      (polyMul
        (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) I))
        (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) C))) := by
    have hp := RatPolyCoeffEqv.reindex s (selected_heat_partition w K extent ids link)
    rw [reindexQuaternionPolynomial_mul] at hp
    exact RatPolyCoeffEqv.haarCarrier hp
  have hstar : HaarCarrierEqv (blockCount extent)
      (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) I))
      (polynomialProduct (fun id => reindexQuaternionPolynomial s
        (faceHeatPolynomial w K extent id)) I) := by
    apply carrierOfPrefix
    · exact reindex_supported s _
    · exact supportedProduct _ I (fun id hi => reindex_supported s _)
    · exact reindexProductPrefix s (faceHeatPolynomial w K extent) I
  have hcombined : HaarCarrierEqv (blockCount extent)
      (reindexQuaternionPolynomial s (polynomialProduct (faceHeatPolynomial w K extent) ids))
      (polyMul
        (polynomialProduct (fun id => reindexQuaternionPolynomial s
          (faceHeatPolynomial w K extent id)) I)
        (reindexQuaternionPolynomial s
          (polynomialProduct (faceHeatPolynomial w K extent) C))) := by
    exact hpart.trans (HaarCarrierEqv.mul hstar (HaarCarrierEqv.refl _ _))
  exact carrier_relative (by omega) hi hj (reindex_supported s
    (polynomialProduct (faceHeatPolynomial w K extent) ids)) hcombined hprod'

#print axioms selectedActionRelativeBound

end YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound
