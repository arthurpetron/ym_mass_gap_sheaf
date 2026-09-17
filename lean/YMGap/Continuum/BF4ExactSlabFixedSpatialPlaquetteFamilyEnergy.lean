/-
# Signed physical plaquette families pay their original temporal energy

The full-action coefficient bound is normalized by its SAME positive
partition. A signed spatial family is then placed at two adjacent times,
with opposite coefficients. Its doubled coefficient-square sum and the
factor two in the original Dirichlet window cancel exactly.

The resulting lower bound depends only on nome, for cofinal heat cutoffs;
it is independent of width, terminal depth and family size. It bounds a
coefficient norm, NOT the original spatial variance. A width-uniform
variance upper bound, a full observable-sector extension and physical
scaling remain open. No heat-bath operator or surrogate law is used.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow (lower upper)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan windowRatio_span_mul_originalFiniteValue)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (j : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ j)

private theorem finite_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    finiteValue w hw0 hw1 extent ids hids p stage ≈
      finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_right _))

/-- Normalize the signed-family bound with its original positive partition.
All signed cross terms remain in the original squared insertion. -/
theorem normalized_family_coercivity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent)
    (c : Z4Plaq → Q') (stage : Nat) :
    lower w * listQSum (fun p => c p*c p) qs ≤
      (600*upper w) * finiteValue w hw0 hw1 extent ids hids
        (polyMul (sourceSpan extent c qs) (sourceSpan extent c qs)) stage := by
  let A := polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids
  let z := quaternionHaar (B extent) A
  let r := reciprocalTerm w hw0 hw1 extent ids hids stage
  let s := polyMul (sourceSpan extent c qs) (sourceSpan extent c qs)
  let b := listQSum (fun p => c p*c p) qs
  have hz : (0 : Q') < z := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partitionSample_floor w hw0 hw1 extent ids hids stage)
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hz
  have hl : ((lower w*z)*b)*r ≈ lower w*b :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => lower w | 1 => z | 2 => b | _ => r))
      (Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) hr) (Q'.mul_one_eqv _))
  have hf : quaternionHaar (B extent) (polyMul A s)*r ≈
      finiteValue w hw0 hw1 extent ids hids s stage :=
    Q'.mul_eqv_congr_right _ _ r (haar_of_coeff (RatPolyCoeffEqv.mul_comm A s))
  have hb := family_partition_coercivity hw0 hw1 (headCutoff w+stage) extent
    (Nat.le_add_right _ _) ids hids hnodup qs hn hqs c
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ r hb
    (Q'.le_of_lt (Q'.recipPos_pos z hz))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) (qmul (Q'.eqv_refl _) hf))))

attribute [local irreducible] baseLinks windowRatio normalizedEnergy

private theorem stage_family_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n stage : Nat) (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (c : Z4Plaq → Q') :
    lower w * listQSum (fun p => c p*c p) qs ≤
      (600*upper w) * normalizedEnergy hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) n (spatialSpan width c qs) := by
  let E := width+(n+(1+n))+1
  let ids := chainIds E width 0 (n+(1+n))
  let labels := doubledLabels n qs
  let coeff := doubledCoeff n c
  let F := BF4ExactSlabPlaquetteBoundaryDualFamily.sourceSpan E coeff labels
  let f := spatialSpan width c qs
  let b := listQSum (fun p => c p*c p) qs
  have hw : width ≤ E := by dsimp [E]; omega
  have ht : 0+(n+(1+n)) ≤ E := by dsimp [E]; omega
  have hlabels : ∀ p, p ∈ labels → p ∈ boundaryCompleteSlabPlaquettes E :=
    fun _ hp => doubledLabels_physical hw (by dsimp [E]; omega) qs hqs hp
  have hfloor := normalized_family_coercivity hw0 hw1 E ids
    (fun _ hi => chainIds_physical hi) (chainIds_nodup _ _ _ _)
    labels (doubledLabels_nodup n qs hn hqs) hlabels coeff stage
  have hsource := difference_source width c qs
  have hplaced := difference_placed E n c qs hqs
  have hpin : windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      n 1 n (polyMul (jump width f) (jump width f)) ≈
      finiteValue w hw0 hw1 E ids (fun _ hi => chainIds_physical hi) (polyMul F F) stage :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) n 1 n (hsource.mul hsource).symm)
      (Q'.eqv_trans _ _ _
        (windowRatio_span_mul_originalFiniteValue hw0 hw1 (start := 0) (m := n) (L := 1) (n := n)
          hw ht (differenceSchedule c qs) (differenceSchedule c qs)
          (schedule_within c qs) (schedule_faces c qs hqs)
          (schedule_within c qs) (schedule_faces c qs hqs) stage)
        (finite_congr hw0 hw1 E ids (fun _ hi => chainIds_physical hi) stage
          (by simpa only [Nat.zero_add] using hplaced.mul hplaced)))
  have he := normalizedEnergy_window hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) n (spatialSpan_supported width c qs)
  have hleft : lower w*listQSum (fun p => coeff p*coeff p) labels ≈ 2*(lower w*b) :=
    Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) (doubled_square_sum n c qs hqs))
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
        (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => lower w | _ => b))
  have hright : (600*upper w)*finiteValue w hw0 hw1 E ids
      (fun _ hi => chainIds_physical hi) (polyMul F F) stage ≈
      2*((600*upper w)*normalizedEnergy hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) n f) :=
    Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) (Q'.eqv_symm (Q'.eqv_trans _ _ _ he hpin)))
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
        (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => 600*upper w
             | _ => normalizedEnergy hw0 hw1 (headCutoff w+stage) width
                 (Nat.le_add_right _ _) n f))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hright))) (by decide)

/-- An arbitrary finite signed fundamental spatial plaquette family pays
the explicit coefficient floor in the ACTUAL original temporal energy.
The constant depends only on nome; no width/depth/family-size factor occurs.
This is not a variance upper bound or an OS spectral-gap conclusion. -/
theorem family_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (c : Z4Plaq → Q') :
    lower w * listQSum (fun p => c p*c p) qs ≤
      (600*upper w) * normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) := by
  have h := stage_family_energy_floor hw0 hw1 width n (K-headCutoff w) qs hn hqs c
  simpa only [Nat.add_sub_of_le hK] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.normalized_family_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.family_energy_floor
