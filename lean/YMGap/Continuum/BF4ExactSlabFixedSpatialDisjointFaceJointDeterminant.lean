/-
# One signed crossed determinant for the ORIGINAL two-face margin

Split the complete slice into the actual p-face blocks and ALL complementary
blocks. For a literal link-disjoint face q, both test-independence hypotheses
are proved from original geometry. Every product heat factor is retained.

With the original marginal W, projected complete endpoint source a, partition
Z and kernel k, the signed determinant is c*D_W - Z*k*D_a. Its pairing with
the actual full jumps equals 2*Z*jointMargin. This division-free identity
resums the previous signed heat/cubic/cutoff corrections exactly; they are
not removed, estimated or assigned a favorable sign. Both original means
and the existing finite reference margin remain unchanged.

No positive margin, useful scaling bound, continuum survival or Clay closure.
-/

import YMGap.Continuum.SU2QuaternionHeatFourCopy
import YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointMargin
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionFourCopyCovariance
open YMGap.Continuum.SU2QuaternionHeatFourCopy
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_pin marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder (mixedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointMargin
  (ownCovariance jointMargin familyReferenceMargin reference_margin_difference_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage marginalWeight projectedEndpointSource

private theorem partition_cover (width : Nat) (p : Z4Plaq) :
    (observableBlocks width p ++ spectatorBlocks width p).Perm (List.range (N width)) :=
  List.perm_append_comm.trans (spectator_observable_cover width p)

private theorem partition_disjoint (width : Nat) (p : Z4Plaq) (i : Nat)
    (hi : i ∈ observableBlocks width p) : i ∉ spectatorBlocks width p :=
  fun hs => spectator_not_observable width p i hs hi

private theorem singleton_independent {width i : Nat} (coeff : Z4Plaq → Q')
    (p : Z4Plaq)
    (h : QuaternionBlockIndependent i (characterPolynomial (plaquette width p).scalar 1)) :
    QuaternionBlockIndependent i (spatialSpan width coeff [p]) :=
  quaternionBlockIndependent_polyAdd (quaternionBlockIndependent_polySmul (coeff p) h)
    (fun _ hm => False.elim (List.not_mem_nil hm))

/-- A signed singleton omits every block of the COMPLETE face complement. -/
theorem singleton_spectator_independent (width : Nat) (coeff : Z4Plaq → Q')
    (p : Z4Plaq) (i : Nat) (hi : i ∈ spectatorBlocks width p) :
    QuaternionBlockIndependent i (spatialSpan width coeff [p]) :=
  singleton_independent coeff p (plaquette_spectator_independent width p i hi)

/-- Literal original-link disjointness supplies the opposite-side test guard.
No probabilistic independence or action-factor separation is asserted. -/
theorem disjoint_observable_independent {width : Nat} (coeff : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) (hp : p ∈ spatialFaces width)
    (i : Nat) (hi : i ∈ observableBlocks width p) :
    QuaternionBlockIndependent i (spatialSpan width coeff [q]) := by
  have hs : i ∈ faceSlots width p := of_decide_eq_true (List.mem_filter.mp hi).2
  obtain ⟨link, hl, he⟩ := List.mem_map.mp hs
  have hrow : blockRow width i p = true :=
    (blockRow_iff width i p).mpr ⟨link, hl, face_link_mem_base hp hl, he⟩
  have hoff : blockRow width i q = false := by
    rcases blockRow_separate width i hd with h | h
    · rw [hrow] at h
      cases h
    · exact h
  exact singleton_independent coeff q
    (blockRow_character_independent width i q (observableBlocks_lt width p i hi) hoff)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource endpointSource
  exact familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width n))

private theorem sourceEnergy_congr (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a : RatPoly) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    sourceEnergy n w K ids a f ≈ sourceEnergy n w K ids a g := by
  unfold sourceEnergy sourceMoment
  have ht := h.mul_left a
  exact Q'.add_eqv_congr'
    (haar_of_coeff (((h.mul h).mul_left a).mul_right _))
    (Q'.neg_eqv_congr _ _ (haar_of_coeff (ht.mul (productMap_congr n w K ids ht))))

private theorem pair_pin (width : Nat) (coeff : Z4Plaq → Q') (p q : Z4Plaq) :
    RatPolyCoeffEqv (spatialSpan width coeff [p,q])
      (polyAdd (spatialSpan width coeff [p]) (spatialSpan width coeff [q])) :=
  (RatPolyCoeffEqv.add_zero _).symm.add (RatPolyCoeffEqv.refl _)

private theorem normalize_mix (a b c z r : Q') (h : z*r ≈ 1) :
    ((a*r-b*r)-c*r)*z ≈ (a-b)-c :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.add (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 4))))
      (.neg (.mul (.var 2) (.var 4)))) (.var 3))
    (.mul (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (.mul (.var 3) (.var 4))) (by decide)
    (fun | 0 => a | 1 => b | 2 => c | 3 => z | _ => r))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_one_eqv _))

/-- Original normalized mixed energy, with its unchanged odd partition,
equals the complete projected-source jump cross. -/
theorem original_mixed_jump_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K)
    (n : Nat) (coeff : Z4Plaq → Q') {p q : Z4Plaq}
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    mixedEnergy hw0 hw1 K width hK n coeff p q * oddMass w K width n ≈
      H (N width+N width) (polyMul (productHeat (N width) w K (List.range (N width)))
        (polyMul (polyMul
          (projectedEndpointSource w K width (terminalMessage w K width n))
          (SU2QuaternionPartialFactorizedHaar.liftBoundary (N width)
            (projectedEndpointSource w K width (terminalMessage w K width n))))
          (polyMul (jump (N width) (spatialSpan width coeff [p]))
            (jump (N width) (spatialSpan width coeff [q]))))) := by
  let a := projectedEndpointSource w K width (terminalMessage w K width n)
  have ep (qs : List Z4Plaq) (hqs : ∀ r, r ∈ qs → r ∈ spatialFaces base) :
      energy w K width (terminalMessage w K width n) (spatialSpan width coeff qs) ≈
        sourceEnergy (N width) w K (List.range (N width)) a (spatialSpan width coeff qs) :=
    energy_projected_source w K width _ _ (terminalMessage_supported w K width n)
      (spatialSpan_supported width coeff qs)
      (spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs)
  have hpq : ∀ r, r ∈ [p,q] → r ∈ spatialFaces base := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp
    · exact (List.mem_singleton.mp hr) ▸ hq
  have hraw := normalize_mix
    (energy w K width (terminalMessage w K width n) (spatialSpan width coeff [p,q]))
    (energy w K width (terminalMessage w K width n) (spatialSpan width coeff [p]))
    (energy w K width (terminalMessage w K width n) (spatialSpan width coeff [q])) _ _
    (Q'.mul_recipPos_eqv _ (oddMass_positive hw0 hw1 K width hK n))
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (ep [p,q] hpq)
          (sourceEnergy_congr (N width) w K _ a (pair_pin width coeff p q)))
          (Q'.neg_eqv_congr _ _ (ep [p] (fun _ hr => (List.mem_singleton.mp hr) ▸ hp))))
        (Q'.neg_eqv_congr _ _ (ep [q] (fun _ hr => (List.mem_singleton.mp hr) ▸ hq))))
      (sourceEnergy_mixed_pin (N width) w K _ (fun _ hi => List.mem_range.mp hi)
        (source_supported w K width n) (spatialSpan_supported width coeff [p])
        (spatialSpan_supported width coeff [q])))

/-- Exact complete-source determinant pin. The original head cutoff is the
only cutoff guard; no Taylor or discarded-mode allowance is introduced. -/
theorem original_energy_determinant_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    H (N width+N width) (polyMul (productHeat (N width) w K (List.range (N width)))
      (fourEnergy (N width) (observableBlocks width p) (spectatorBlocks width p)
        (projectedEndpointSource w K width (terminalMessage w K width n))
        (spatialSpan width coeff [p]) (spatialSpan width coeff [q]))) ≈
      2*(mixedEnergy hw0 hw1 K width hK n coeff p q * oddMass w K width n) :=
  Q'.eqv_trans _ _ _
    (heat_fourEnergy_pin (N width) w K _ _ (partition_disjoint width p) (partition_cover width p)
      _ _ _ (source_supported w K width n) (spatialSpan_supported width coeff [p])
      (spatialSpan_supported width coeff [q]) (singleton_spectator_independent width coeff p)
      (disjoint_observable_independent coeff hd (spatialFaces_mono (Nat.le_of_lt hwidth) hp)))
    (Q'.mul_eqv_congr_left 2 _ _ (original_mixed_jump_pin hw0 hw1 K hwidth hK n coeff hp hq).symm)

/-- The determinant is normalized by the original W mass and BOTH OWN means. -/
theorem original_covariance_determinant_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n : Nat) (coeff : Z4Plaq → Q') {p q : Z4Plaq}
    (hd : LinkDisjoint p q) (hp : p ∈ spatialFaces width) :
    H (N width+N width)
      (fourEnergy (N width) (observableBlocks width p) (spectatorBlocks width p)
        (marginalWeight w K width n) (spatialSpan width coeff [p]) (spatialSpan width coeff [q])) ≈
      4*(ownCovariance hw0 hw1 K width hK n coeff p q *
        (oddMass w K width n * oddMass w K width n)) := by
  have hm := marginalMass_pin w K width n
  have hs := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
    (Q'.mul_eqv_congr_left _ _ _ hm)
  have hn := covariance_numerator_pin (N width) (marginalWeight w K width n)
    (spatialSpan width coeff [p]) (spatialSpan width coeff [q])
    (marginalMass_positive hw0 hw1 K width hK n)
  exact Q'.eqv_trans _ _ _
    (covariance_fourEnergy_pin (N width) _ _ (partition_disjoint width p) (partition_cover width p)
      _ _ _ (marginalWeight_supported w K width n) (spatialSpan_supported width coeff [p])
      (spatialSpan_supported width coeff [q]) (singleton_spectator_independent width coeff p)
      (disjoint_observable_independent coeff hd hp))
    (Q'.mul_eqv_congr_left 4 _ _ (Q'.eqv_trans _ _ _ hn.symm
      (Q'.mul_eqv_congr_left _ _ _ hs)))

/-- Division-free signed determinant: covariance and energy corrections are
retained TOGETHER, not bounded separately or replaced by a source-square law. -/
def signedDeterminant (w : Q') (K width n : Nat) (p : Z4Plaq) (c : Q') : RatPoly :=
  polyAdd
    (polySmul c (crossDeterminant (N width) (observableBlocks width p) (spectatorBlocks width p)
      (marginalWeight w K width n)))
    (polySmul (-(oddMass w K width n))
      (polyMul (productHeat (N width) w K (List.range (N width)))
        (crossDeterminant (N width) (observableBlocks width p) (spectatorBlocks width p)
          (projectedEndpointSource w K width (terminalMessage w K width n)))))

def jointPairing (w : Q') (K width n : Nat) (coeff : Z4Plaq → Q')
    (p q : Z4Plaq) (c : Q') : Q' :=
  finiteHaarPair (N width+N width) (signedDeterminant w K width n p c)
    (polyMul (jump (N width) (spatialSpan width coeff [p]))
      (jump (N width) (spatialSpan width coeff [q])))

attribute [local irreducible] signedDeterminant jointPairing jointMargin oddMass
  ownCovariance mixedEnergy spatialSpan productHeat crossDeterminant

/-- Exact original joint-margin consumer. Every signed finite-cutoff effect
is in ONE pairing, with the original partition and interacting covariance. -/
theorem joint_pairing_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K)
    (n : Nat) (coeff : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) (c : Q') :
    jointPairing w K width n coeff p q c ≈
      2*oddMass w K width n * jointMargin hw0 hw1 K width hK n coeff p q c := by
  unfold jointPairing signedDeterminant jointMargin
  let Z := oddMass w K width n
  let f := spatialSpan width coeff [p]
  let g := spatialSpan width coeff [q]
  let D := polyMul (jump (N width) f) (jump (N width) g)
  let W := marginalWeight w K width n
  let a := projectedEndpointSource w K width (terminalMessage w K width n)
  let k := productHeat (N width) w K (List.range (N width))
  have hfull (r : RatPoly) := fourEnergy_full_pin (partition_cover width p) r
    (spatialSpan_supported width coeff [p]) (spatialSpan_supported width coeff [q])
  have hv : finiteHaarPair (N width+N width)
      (crossDeterminant (N width) (observableBlocks width p) (spectatorBlocks width p) W) D ≈
      4*(ownCovariance hw0 hw1 K width hK n coeff p q * (Z*Z)) :=
    Q'.eqv_trans _ _ _ (haar_of_carrier (hfull W).symm)
      (original_covariance_determinant_pin hw0 hw1 K width hK n coeff hd
        (spatialFaces_mono (Nat.le_of_lt hwidth) hp))
  have he : finiteHaarPair (N width+N width)
      (polyMul k (crossDeterminant (N width) (observableBlocks width p) (spectatorBlocks width p) a)) D ≈
      2*(mixedEnergy hw0 hw1 K width hK n coeff p q * Z) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (Q'.eqv_trans _ _ _ (haar_of_carrier ((hfull a).symm.mul_left k))
        (original_energy_determinant_pin hw0 hw1 K hwidth hK n coeff hd hp hq))
  change finiteHaarPair _ (polyAdd (polySmul c _) (polySmul (-Z) _)) D ≈ _
  exact Q'.eqv_trans _ _ _ (finiteHaarPair_add_left _ _ _ D)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left _ c _ D) (Q'.mul_eqv_congr_left c _ _ hv))
        (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left _ (-Z) _ D) (Q'.mul_eqv_congr_left (-Z) _ _ he)))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.const 4) (.mul (.var 1) (.mul (.var 3) (.var 3)))))
          (.mul (.neg (.var 3)) (.mul (.const 2) (.mul (.var 2) (.var 3)))))
        (.mul (.mul (.const 2) (.var 3))
          (.mul (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2))) (.var 3)))
        (by decide) (fun | 0 => c | 1 => ownCovariance hw0 hw1 K width hK n coeff p q
                         | 2 => mixedEnergy hw0 hw1 K width hK n coeff p q | _ => Z)))

private theorem two_faces {base : Nat} {p q : Z4Plaq}
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    ∀ r, r ∈ [p,q] → r ∈ spatialFaces base := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hp
  · exact (List.mem_singleton.mp hr) ▸ hq

/-- Direct join to the EXISTING original finite reference-margin consumer,
at one unchanged cutoff/depth. No successful input or favorable sign assumed. -/
theorem reference_pairing_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base width : Nat}
    (hwidth : base < width) (coeff : Z4Plaq → Q') {p q : Z4Plaq}
    (hd : LinkDisjoint p q) (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base)
    (c : Q') (stage depth : Nat) :
    jointPairing w (headCutoff w+stage) width depth coeff p q c ≈
      (2*(oddMass w (headCutoff w+stage) width depth *
        oddMass w (headCutoff w+stage) width depth)) *
      ((familyReferenceMargin hw0 hw1 hwidth coeff [p,q] (two_faces hp hq) c stage depth -
        familyReferenceMargin hw0 hw1 hwidth coeff [p]
          (fun _ hr => (List.mem_singleton.mp hr) ▸ hp) c stage depth) -
        familyReferenceMargin hw0 hw1 hwidth coeff [q]
          (fun _ hr => (List.mem_singleton.mp hr) ▸ hq) c stage depth) := by
  let Z := oddMass w (headCutoff w+stage) width depth
  exact Q'.eqv_trans _ _ _
    (joint_pairing_pin hw0 hw1 _ hwidth (Nat.le_add_right _ _) depth coeff hd hp hq c)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (2*Z) _ _
        (reference_margin_difference_pin hw0 hw1 hwidth coeff hp hq c stage depth).symm)
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 0)))
        (.mul (.mul (.const 2) (.mul (.var 0) (.var 0))) (.var 1))
        (by decide) (fun
          | 0 => Z
          | _ =>
            (familyReferenceMargin hw0 hw1 hwidth coeff [p,q] (two_faces hp hq) c stage depth -
              familyReferenceMargin hw0 hw1 hwidth coeff [p]
                (fun _ hr => (List.mem_singleton.mp hr) ▸ hp) c stage depth) -
              familyReferenceMargin hw0 hw1 hwidth coeff [q]
                (fun _ hr => (List.mem_singleton.mp hr) ▸ hq) c stage depth)))

#print axioms singleton_spectator_independent
#print axioms disjoint_observable_independent
#print axioms original_mixed_jump_pin
#print axioms original_energy_determinant_pin
#print axioms original_covariance_determinant_pin
#print axioms signedDeterminant
#print axioms jointPairing
#print axioms joint_pairing_pin
#print axioms reference_pairing_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant
