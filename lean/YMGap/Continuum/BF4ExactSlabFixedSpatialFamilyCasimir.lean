/-
# The literal fixed-spatial family is a Casimir eigenvector

Each of the four physical links incident to a spatial plaquette contributes
three to the negative block angular Laplacian. Spectator blocks contribute
zero. Coefficient linearity then extends the identity to arbitrary signed and
repeated plaquette lists on the same finite product-Haar carrier.
-/

import YMGap.Continuum.SU2QuaternionBlockLinearCasimir
import YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarAngularCarrier

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem negative_linear_block {n block : Nat} (hb : block < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hd : HasQuaternionBlockDegree block 1 p) :
    HaarCarrierEqv n (polyNeg (blockAngularLaplacian block p))
      (polySmul 3 p) := by
  have h := HaarCarrierEqv.neg (blockCasimir_linear hb p hp hd)
  exact h.trans (RatPolyCoeffEqv.haarCarrier
    ((neg_smul (polySmul (-3) p)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) (-3) p).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide) p))))

private theorem four_active_casimir {n : Nat} (active : List Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hlen : active.length = 4)
    (hdegree : ∀ block, block ∈ active → HasQuaternionBlockDegree block 1 p)
    (hrange : ∀ block, block ∈ active → block < n) :
    HaarCarrierEqv n (activeCasimirPolynomial active p) (polySmul 12 p) := by
  cases active with
  | nil => simp at hlen
  | cons a rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest =>
      cases rest with
      | nil => simp at hlen
      | cons c rest =>
        cases rest with
        | nil => simp at hlen
        | cons d rest =>
          have hrest : rest = [] := by
            have hl : rest.length = 0 := by
              simp only [List.length_cons] at hlen
              omega
            exact List.length_eq_zero_iff.mp hl
          subst rest
          have ha := negative_linear_block (hrange a (by simp)) p hp
            (hdegree a (by simp))
          have hb := negative_linear_block (hrange b (by simp)) p hp
            (hdegree b (by simp))
          have hc := negative_linear_block (hrange c (by simp)) p hp
            (hdegree c (by simp))
          have hd := negative_linear_block (hrange d (by simp)) p hp
            (hdegree d (by simp))
          have hs : HaarCarrierEqv n
              (activeCasimirPolynomial [a,b,c,d] p)
              (polyAdd (polySmul 3 p)
                (polyAdd (polySmul 3 p)
                  (polyAdd (polySmul 3 p)
                    (polyAdd (polySmul 3 p) polyZero)))) := by
            change HaarCarrierEqv n
              (polyAdd (polyNeg (blockAngularLaplacian a p))
                (polyAdd (polyNeg (blockAngularLaplacian b p))
                  (polyAdd (polyNeg (blockAngularLaplacian c p))
                    (polyAdd (polyNeg (blockAngularLaplacian d p)) polyZero)))) _
            exact HaarCarrierEqv.add ha
              (HaarCarrierEqv.add hb
                (HaarCarrierEqv.add hc
                  (HaarCarrierEqv.add hd (HaarCarrierEqv.refl n polyZero))))
          have h3 : RatPolyCoeffEqv
              (polyAdd (polySmul 3 p) polyZero) (polySmul 3 p) :=
            RatPolyCoeffEqv.add_zero _
          have h6 : RatPolyCoeffEqv
              (polyAdd (polySmul 3 p) (polyAdd (polySmul 3 p) polyZero))
              (polySmul 6 p) :=
            ((RatPolyCoeffEqv.refl _).add h3).trans
              ((RatPolyCoeffEqv.add_smul_same 3 3 p).trans
                (RatPolyCoeffEqv.smul_coefficient (by decide) p))
          have h9 : RatPolyCoeffEqv
              (polyAdd (polySmul 3 p)
                (polyAdd (polySmul 3 p) (polyAdd (polySmul 3 p) polyZero)))
              (polySmul 9 p) :=
            ((RatPolyCoeffEqv.refl _).add h6).trans
              ((RatPolyCoeffEqv.add_smul_same 3 6 p).trans
                (RatPolyCoeffEqv.smul_coefficient (by decide) p))
          have h12 : RatPolyCoeffEqv
              (polyAdd (polySmul 3 p)
                (polyAdd (polySmul 3 p)
                  (polyAdd (polySmul 3 p)
                    (polyAdd (polySmul 3 p) polyZero))))
              (polySmul 12 p) :=
            ((RatPolyCoeffEqv.refl _).add h9).trans
              ((RatPolyCoeffEqv.add_smul_same 3 9 p).trans
                (RatPolyCoeffEqv.smul_coefficient (by decide) p))
          exact hs.trans (RatPolyCoeffEqv.haarCarrier h12)

/-- The literal four-link spatial plaquette has full slice Casimir 12 under
every insertion in the original finite product-Haar carrier. -/
theorem plaquette_casimir (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial (List.range (N width))
        (characterPolynomial (plaquette width face).scalar 1))
      (polySmul 12 (characterPolynomial (plaquette width face).scalar 1)) := by
  let p := characterPolynomial (plaquette width face).scalar 1
  have hp : SupportedQuaternionBlocks (N width) p :=
    SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hactive : ∀ block, block ∈ observableBlocks width face →
      HasQuaternionBlockDegree block 1 p := by
    intro block hb
    have hs : block ∈ faceSlots width face :=
      of_decide_eq_true (List.mem_filter.mp hb).2
    obtain ⟨link, hl, heq⟩ := List.mem_map.mp hs
    subst block
    exact plaquette_character_degree width hf hl
  have hfour := four_active_casimir (observableBlocks width face) p hp
    (observableBlocks_length width face hf) hactive
    (observableBlocks_lt width face)
  exact (RatPolyCoeffEqv.haarCarrier
      (activeCasimirPolynomial_range_eq_active (N width)
        (spectatorBlocks width face) (observableBlocks width face)
        (spectator_observable_cover width face) p
        (plaquette_spectator_independent width face))).trans hfour

private theorem blockLaplacian_add (block : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian block (polyAdd p q))
      (polyAdd (blockAngularLaplacian block p)
        (blockAngularLaplacian block q)) := by
  have hsecond (i j : Nat) : RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (polyAdd p q)))
      (polyAdd
        (blockAngularDerivative block i j (blockAngularDerivative block i j p))
        (blockAngularDerivative block i j (blockAngularDerivative block i j q))) :=
    (angularDerivative_congr _ _ (angularDerivative_add _ _ p q)).trans
      (angularDerivative_add _ _ _ _)
  have hsix := ((hsecond 0 1).add
    ((hsecond 0 2).add
      ((hsecond 0 3).add
        ((hsecond 1 2).add
          ((hsecond 1 3).add (hsecond 2 3)))))).trans
    (six_add
      (fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j p))
      (fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j q)))
  exact (blockAngularLaplacian_eq_six block _).trans
    (hsix.trans ((blockAngularLaplacian_eq_six block p).symm.add
      (blockAngularLaplacian_eq_six block q).symm))

private theorem blockLaplacian_smul (block : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian block (polySmul c p))
      (polySmul c (blockAngularLaplacian block p)) := by
  have hsecond (i j : Nat) : RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (polySmul c p)))
      (polySmul c
        (blockAngularDerivative block i j (blockAngularDerivative block i j p))) :=
    (angularDerivative_congr _ _ (angularDerivative_smul _ _ c p)).trans
      (angularDerivative_smul _ _ c _)
  have hsix := ((hsecond 0 1).add
    ((hsecond 0 2).add
      ((hsecond 0 3).add
        ((hsecond 1 2).add
          ((hsecond 1 3).add (hsecond 2 3)))))).trans
    (six_smul c (fun i j => blockAngularDerivative block i j
      (blockAngularDerivative block i j p)))
  exact (blockAngularLaplacian_eq_six block _).trans
    (hsix.trans ((blockAngularLaplacian_eq_six block p).symm.smul c))

private theorem neg_add (p q : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polyAdd p q))
      (polyAdd (polyNeg p) (polyNeg q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.neg (.add (.var 0) (.var 1)))
    (.add (.neg (.var 0)) (.neg (.var 1)))
    (by decide) (fun | 0 => p | _ => q)

private theorem neg_smul_comm (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p))
      (polySmul c (polyNeg p)) := by
  have hleft := (neg_smul (polySmul c p)).trans
    (RatPolyCoeffEqv.smul_assoc (-1) c p)
  have hright := ((neg_smul p).smul c).trans
    (RatPolyCoeffEqv.smul_assoc c (-1) p)
  exact hleft.trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) c) p).trans
      hright.symm)

private theorem regroup (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyAdd a b) (polyAdd c d))
      (polyAdd (polyAdd a c) (polyAdd b d)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

/-- Literal Casimir linearity, also available to quadratic observable consumers. -/
theorem activeCasimir_add (active : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyAdd p q))
      (polyAdd (activeCasimirPolynomial active p)
        (activeCasimirPolynomial active q)) := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons block rest ih =>
      have ht := (RatPolyCoeffEqv.neg (blockLaplacian_add block p q)).trans
        (neg_add (blockAngularLaplacian block p)
          (blockAngularLaplacian block q))
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block (polyAdd p q)))
          (activeCasimirPolynomial rest (polyAdd p q)))
        (polyAdd
          (polyAdd (polyNeg (blockAngularLaplacian block p))
            (activeCasimirPolynomial rest p))
          (polyAdd (polyNeg (blockAngularLaplacian block q))
            (activeCasimirPolynomial rest q)))
      exact (ht.add ih).trans (regroup _ _ _ _)

/-- Rational scaling commutes with the original active-block Casimir. -/
theorem activeCasimir_smul (active : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polySmul c p))
      (polySmul c (activeCasimirPolynomial active p)) := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons block rest ih =>
      have ht := (RatPolyCoeffEqv.neg (blockLaplacian_smul block c p)).trans
        (neg_smul_comm c (blockAngularLaplacian block p))
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block (polySmul c p)))
          (activeCasimirPolynomial rest (polySmul c p)))
        (polySmul c (polyAdd (polyNeg (blockAngularLaplacian block p))
          (activeCasimirPolynomial rest p)))
      exact (ht.add ih).trans
        (RatPolyCoeffEqv.smul_add c _ _).symm

private theorem activeCasimir_zero (active : List Nat) :
    RatPolyCoeffEqv (activeCasimirPolynomial active polyZero) polyZero := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons block rest ih =>
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block polyZero))
          (activeCasimirPolynomial rest polyZero)) polyZero
      exact ((RatPolyCoeffEqv.neg
        (blockAngularLaplacian_independent_zero block polyZero
          (quaternionBlockIndependent_polyZero block))).add ih).trans
        (RatPolyCoeffEqv.add_zero polyZero)

/-- Any finite signed list, including repeated faces, has the same literal
full-slice Casimir eigenvalue as each physical spatial plaquette. -/
theorem spatialSpan_casimir (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial (List.range (N width))
        (spatialSpan width c qs))
      (polySmul 12 (spatialSpan width c qs)) := by
  induction qs with
  | nil =>
      simpa only [spatialSpan, finitePolySum, polySmul] using
        (RatPolyCoeffEqv.haarCarrier
          (activeCasimir_zero (List.range (N width))))
  | cons face rest ih =>
      let p := characterPolynomial (plaquette width face).scalar 1
      let r := spatialSpan width c rest
      have hf : face ∈ spatialFaces width := hqs face List.mem_cons_self
      have hrest : ∀ f, f ∈ rest → f ∈ spatialFaces width :=
        fun f h => hqs f (List.mem_cons_of_mem face h)
      have hface := HaarCarrierEqv.smul (c face)
        (plaquette_casimir width face hf)
      have hstep : HaarCarrierEqv (N width)
          (activeCasimirPolynomial (List.range (N width))
            (polyAdd (polySmul (c face) p) r))
          (polySmul 12 (polyAdd (polySmul (c face) p) r)) := by
        have hadd := RatPolyCoeffEqv.haarCarrier (blocks := N width)
          (activeCasimir_add (List.range (N width))
            (polySmul (c face) p) r)
        have hsmul := RatPolyCoeffEqv.haarCarrier (blocks := N width)
          (activeCasimir_smul (List.range (N width)) (c face) p)
        have hface' : HaarCarrierEqv (N width)
            (activeCasimirPolynomial (List.range (N width)) (polySmul (c face) p))
            (polySmul 12 (polySmul (c face) p)) :=
          (hsmul.trans hface).trans (RatPolyCoeffEqv.haarCarrier
            ((RatPolyCoeffEqv.smul_assoc (c face) 12 p).trans
              ((RatPolyCoeffEqv.smul_coefficient
                (Q'.mul_comm_eqv (c face) 12) p).trans
                (RatPolyCoeffEqv.smul_assoc 12 (c face) p).symm)))
        exact hadd.trans
          ((HaarCarrierEqv.add hface' (ih hrest)).trans
            (RatPolyCoeffEqv.haarCarrier
              (RatPolyCoeffEqv.smul_add 12 _ _).symm))
      simpa only [spatialSpan, finitePolySum] using hstep

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir.plaquette_casimir
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir.spatialSpan_casimir
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir.activeCasimir_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir.activeCasimir_smul
