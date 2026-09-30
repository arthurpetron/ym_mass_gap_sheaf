/-
# One-link relative energy for the original signed plaquette source

The full signed observable is split at a physical link into its incident
head-linear part and its nonincident head-free predictor. The original
selected-face action is retained in the Haar integral. This is a one-edge
angular-energy estimate, not a two-edge or OS-time variance bound.
-/

import YMGap.Continuum.QuaternionHaarRelativePredictionEnergy
import YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
import YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4ExactSlabSignedSourceRelativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection (linkLocal_degree_zero)
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff relativeCap relativeCap_positive)
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePredictionEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarHeadFubini (headSwapBlockInvolution_map_zero)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarAngularCarrier (carrierOfPrefix)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

/-- The exact nonincident summands, still on the original finite carrier. -/
def complementSource (extent : Nat) (link : Z4Link) (c : Nat → Q') : RatPoly :=
  finitePolySum (term extent c) (complementIds extent link)

private theorem finitePolySum_append_local {A : Type} (f : A → RatPoly) :
    ∀ xs ys : List A,
      finitePolySum f (xs ++ ys) =
        polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by
      simp only [List.cons_append, finitePolySum, finitePolySum_append_local f xs ys,
        polyAdd, List.append_assoc]

private theorem finitePolySum_perm_local {A : Type} (f : A → RatPoly)
    {xs ys : List A} (h : xs.Perm ys) :
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum f ys) := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons a h ih => exact (RatPolyCoeffEqv.refl (f a)).add ih
  | swap a b xs =>
      exact (RatPolyCoeffEqv.add_assoc (f b) (f a) (finitePolySum f xs)).symm.trans
        (((RatPolyCoeffEqv.add_comm (f b) (f a)).add
          (RatPolyCoeffEqv.refl (finitePolySum f xs))).trans
          (RatPolyCoeffEqv.add_assoc (f a) (f b) (finitePolySum f xs)))
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem source_partition (extent : Nat) (link : Z4Link) (c : Nat → Q') :
    RatPolyCoeffEqv (observable extent c)
      (polyAdd (incidentObservable extent link c) (complementSource extent link c)) := by
  refine (finitePolySum_perm_local (term extent c)
    (face_partition extent link).symm).trans ?_
  rw [finitePolySum_append_local]
  exact RatPolyCoeffEqv.refl _

private theorem complementSource_local (extent : Nat) (link : Z4Link)
    (c : Nat → Q') :
    LinkLocal extent (faceLinks extent (complementIds extent link))
      (complementSource extent link c) := by
  apply BlockLocal.finiteSum
  intro id hid
  have hterm : LinkLocal extent (edgesOf (slabPlaquetteAt extent id))
      (term extent c id) := by
    unfold term faceCharacter
    exact ((face_scalar_local extent (slabPlaquetteAt extent id)).character 1).smul (c id)
  exact hterm.mono (fun other hother =>
    List.mem_flatMap.mpr ⟨id, hid, hother⟩)

/-- The literal complementary predictor is independent of the selected link
after moving that link to the head. -/
theorem complementSource_head_degree_zero (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') :
    HasQuaternionBlockDegree 0 0
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (complementSource extent link c)) := by
  let s := linkHeadSwap extent link hl
  apply blockDegree_reindex s
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
    (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl))
  exact linkLocal_degree_zero (complementSource_local extent link c)
    link hl (link_not_mem_complement extent link)

/-- The actual complementary predictor also carries the rational center.
Its head degree is literally zero; no cancellation of head-linear terms is
used to establish that syntactic fact. -/
def centeredPredictor (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q')
    (m : Q') : RatPoly :=
  polyAdd
    (polySmul (-1) (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
      (complementSource extent link c)))
    (polySmul m polyOne)

theorem centeredPredictor_supported (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') (m : Q') :
    SupportedQuaternionBlocks (blocks extent)
      (centeredPredictor extent link hl c m) := by
  unfold centeredPredictor
  exact supported_add
    (polySmul_supported
      (reindex_supported (linkHeadSwap extent link hl)
        (complementSource extent link c)) (-1))
    (polySmul_supported (supported_one (blocks extent)) m)

theorem centeredPredictor_head_degree_zero (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') (m : Q') :
    HasQuaternionBlockDegree 0 0 (centeredPredictor extent link hl c m) := by
  unfold centeredPredictor
  exact ((complementSource_head_degree_zero extent link hl c).smul (-1)).add
    ((hasQuaternionBlockDegree_one 0).smul m)

private theorem square_derivative_incident (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') :
    RatPolyCoeffEqv
      (angularSquare (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (observable extent c)))
      (angularSquare (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (incidentObservable extent link c))) := by
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :=
    observable_derivative_incident extent link hl hi hj c
  unfold angularSquare six
  exact ((hd 0 1 (by decide) (by decide)).mul
    (hd 0 1 (by decide) (by decide))).add
    (((hd 0 2 (by decide) (by decide)).mul
      (hd 0 2 (by decide) (by decide))).add
      (((hd 0 3 (by decide) (by decide)).mul
        (hd 0 3 (by decide) (by decide))).add
        (((hd 1 2 (by decide) (by decide)).mul
          (hd 1 2 (by decide) (by decide))).add
          (((hd 1 3 (by decide) (by decide)).mul
            (hd 1 3 (by decide) (by decide))).add
            ((hd 2 3 (by decide) (by decide)).mul
              (hd 2 3 (by decide) (by decide)))))))

/-- The literal, centered whole signed source, pulled to the selected-link
head. This is not a predictor or an incident-only observable. -/
def centeredHeadSource (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q')
    (m : Q') : RatPoly :=
  reindexQuaternionPolynomial (linkHeadSwap extent link hl)
    (shifted (observable extent c) m)

private theorem centered_error_coeff (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') (m : Q') :
    let s := linkHeadSwap extent link hl
    let f := reindexQuaternionPolynomial s (incidentObservable extent link c)
    RatPolyCoeffEqv
      (polyAdd f (polySmul (-1) (centeredPredictor extent link hl c m)))
      (polyAdd (polySmul 1 (reindexQuaternionPolynomial s (observable extent c)))
        (polySmul (-m) polyOne)) := by
  dsimp only
  let s := linkHeadSwap extent link hl
  let f := reindexQuaternionPolynomial s (incidentObservable extent link c)
  let g := reindexQuaternionPolynomial s (complementSource extent link c)
  let M := polySmul m polyOne
  have hdouble : RatPolyCoeffEqv (polySmul (-1) (polySmul (-1) g)) g :=
    (RatPolyCoeffEqv.smul_assoc (-1) (-1) g).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide : ((-1 : Q') * -1) ≈ 1) g).trans
        (RatPolyCoeffEqv.one_smul g))
  have hminus : RatPolyCoeffEqv (polySmul (-1) M) (polySmul (-m) polyOne) :=
    (RatPolyCoeffEqv.smul_assoc (-1) m polyOne).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv 1 m)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv m))) polyOne)
  have hpart : RatPolyCoeffEqv
      (polyAdd f g) (reindexQuaternionPolynomial s (observable extent c)) := by
    have hp := RatPolyCoeffEqv.reindex s (source_partition extent link c)
    rw [reindexQuaternionPolynomial_add] at hp
    exact hp.symm
  change RatPolyCoeffEqv
    (polyAdd f (polySmul (-1) (polyAdd (polySmul (-1) g) M)))
    (polyAdd (polySmul 1 (reindexQuaternionPolynomial s (observable extent c)))
      (polySmul (-m) polyOne))
  exact ((RatPolyCoeffEqv.refl f).add
      ((RatPolyCoeffEqv.smul_add (-1) (polySmul (-1) g) M).trans
        (hdouble.add hminus))).trans
    ((RatPolyCoeffEqv.add_assoc f g (polySmul (-m) polyOne)).symm.trans
      ((hpart.add (RatPolyCoeffEqv.refl _)).trans
        (((RatPolyCoeffEqv.one_smul _).symm).add (RatPolyCoeffEqv.refl _))))

/-- The predictor error is the literal centered full source as a Haar
carrier, including arbitrary supported insertions. The only non-coefficient
step is that a reindexed polynomial one has the same sphere restriction as
the original one. -/
theorem centered_error_carrier (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') (m : Q') :
    let s := linkHeadSwap extent link hl
    let f := reindexQuaternionPolynomial s (incidentObservable extent link c)
    HaarCarrierEqv (blocks extent)
      (polyAdd f (polySmul (-1) (centeredPredictor extent link hl c m)))
      (centeredHeadSource extent link hl c m) := by
  dsimp only
  let s := linkHeadSwap extent link hl
  have hone : HaarCarrierEqv (blocks extent)
      (reindexQuaternionPolynomial s polyOne) polyOne :=
    carrierOfPrefix (reindex_supported s polyOne) (supported_one (blocks extent))
      (reindex_polyOne_prefix s)
  have hright : HaarCarrierEqv (blocks extent)
      (centeredHeadSource extent link hl c m)
      (polyAdd (polySmul 1 (reindexQuaternionPolynomial s (observable extent c)))
        (polySmul (-m) polyOne)) := by
    unfold centeredHeadSource shifted
    rw [reindexQuaternionPolynomial_add,
      reindexQuaternionPolynomial_smul, reindexQuaternionPolynomial_smul]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl (blocks extent) _) (HaarCarrierEqv.smul (-m) hone)
  exact (RatPolyCoeffEqv.haarCarrier (centered_error_coeff extent link hl c m)).trans
    hright.symm

/-- One physical edge's original selected-action angular energy is controlled
by the centered signed source with its exact nonincident predictor. The
observable on the left is the WHOLE signed physical plaquette sum. -/
theorem signed_source_one_edge_relative_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : relativeCutoff w 2048 ≤ K)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (c : Nat → Q') (m : Q') :
    let s := linkHeadSwap extent link hl
    let A := reindexQuaternionPolynomial s
      (polynomialProduct (faceHeatPolynomial w K extent)
        (slabPhysicalFaceEdges extent))
    H (blocks extent) (polyMul A
      (angularSquare (reindexQuaternionPolynomial s (observable extent c)))) ≤
      energyPredictionFactor (6*relativeCap w 2048) *
        H (blocks extent) (polyMul A
          (polyMul (centeredHeadSource extent link hl c m)
            (centeredHeadSource extent link hl c m))) := by
  dsimp only
  let s := linkHeadSwap extent link hl
  let A := reindexQuaternionPolynomial s
      (polynomialProduct (faceHeatPolynomial w K extent)
        (slabPhysicalFaceEdges extent))
  let f := reindexQuaternionPolynomial s (incidentObservable extent link c)
  let q := centeredPredictor extent link hl c m
  have hC : (0 : Q') < 6*relativeCap w 2048 :=
    Q'.mul_pos (by decide) (relativeCap_positive hw0 (by decide))
  have hR (i j : Nat) (hi : i < 4) (hj : j < 4) :
      RelativeBound (blocks extent) i j A (6*relativeCap w 2048) :=
    selectedActionRelativeBound hw0 hw1 K extent hK
      (slabPhysicalFaceEdges extent) (fun _ h => h)
      (CayleyParentInj.range_nodup _) link hl hi hj
  have hf : SupportedQuaternionBlocks (blocks extent) f :=
    reindex_supported s (incidentObservable extent link c)
  have hlinear : HasQuaternionBlockDegree 0 1 f :=
    incidentObservable_head_degree_one extent link hl c
  have hq : SupportedQuaternionBlocks (blocks extent) q :=
    centeredPredictor_supported extent link hl c m
  have hfree : HasQuaternionBlockDegree 0 0 q :=
    centeredPredictor_head_degree_zero extent link hl c m
  have hB : (blocks extent-1)+1 = blocks extent := by
    have h := List.idxOf_lt_length_of_mem hl
    change _ < blocks extent at h
    omega
  have hmain := angular_energy_le_prediction (tail := blocks extent-1) (W := A) (f := f) hC
    (by rw [hB]; exact hR) (by rw [hB]; exact hf) hlinear q
    (by rw [hB]; exact hq) hfree
  rw [hB] at hmain
  have hpin := square_derivative_incident extent link hl c
  have hcenter := centered_error_carrier extent link hl c m
  have hsq := (HaarCarrierEqv.mul hcenter hcenter) A
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff (hpin.mul_left A)))
    (Q'.le_trans' _ _ _ hmain
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hsq)))

#print axioms complementSource
#print axioms complementSource_head_degree_zero
#print axioms centeredPredictor
#print axioms centeredPredictor_supported
#print axioms centeredPredictor_head_degree_zero
#print axioms centeredHeadSource
#print axioms centered_error_carrier
#print axioms signed_source_one_edge_relative_energy

end YMGap.Continuum.BF4ExactSlabSignedSourceRelativeEnergy
