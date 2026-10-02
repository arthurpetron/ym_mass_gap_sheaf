/-
# The growing ORIGINAL Wilson square against its OWN interacting variance

Every distinct boundary link contributes Casimir three, irrespective of
orientation; every spectator contributes zero. Thus the literal padded
dyadic square has full-slice Casimir 12*side, not the plaquette-family
Casimir 12. Weighted IBP and the original temporal Taylor identity retain
the COMPLETE marginal, its OWN mean, partition and signed remainder.

This supplies an exact growing-observable identity, not a useful bound on
its remainder. The assigned geometric spacing is not a justified physical
coupling/time trajectory. No continuum survival or mass gap follows here.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
import YMGap.Continuum.SU2QuaternionBlockLinearCasimir
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
import YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit

namespace YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion orientedCoordinateQuaternion_blockDegree)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive marginalMass_pin marginalVariance_pin
    wardResidual normalizedWardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor (varianceRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
  (quadraticRate normalizedEnergy_centered_taylor
    normalizedRemainder_centered_square_bound completeCenteredError)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression sourcePolynomial)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit (finiteEnergy)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit (finiteVariance)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks oddMass oddVariance

private theorem word_present_degree (i : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es : List OrientedBF4Link, (es.map block).Nodup → i ∈ es.map block →
      HasPolyQuaternionBlockDegree i 1 (wordAt block es)
  | [], _, hm => False.elim (List.not_mem_nil hm)
  | e::es, hnd, hm => by
      have hn := List.nodup_cons.mp hnd
      change HasPolyQuaternionBlockDegree i 1
        (PolyQuaternion.mul (orientedCoordinateQuaternion (block e) e.reverse)
          (wordAt block es))
      by_cases hi : i = block e
      · have hl := orientedCoordinateQuaternion_blockDegree (block e) i e.reverse
        rw [if_pos hi] at hl
        have ht := word_independent i block es (by
          intro f hf heq
          exact hn.1 (List.mem_map.mpr ⟨f, hf, heq.symm.trans hi⟩))
        simpa only [Nat.add_zero] using hl.mul ht
      · have hl := orientedCoordinateQuaternion_blockDegree (block e) i e.reverse
        rw [if_neg hi] at hl
        have ht := word_present_degree i block es hn.2
          ((List.mem_cons.mp hm).resolve_left hi)
        simpa only [Nat.zero_add] using hl.mul ht

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hp => by
      have he := hp e List.mem_cons_self
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es (fun f hf => hp f (List.mem_cons_of_mem e hf))]
      unfold orientedLink link
      rw [if_pos he]
      rfl

/-- Every ACTUAL selected block occurs once, including reverse orientations. -/
theorem paddedSquare_character_degree (scale width : Nat)
    (hwidth : side scale < width) (i : Nat)
    (hi : i ∈ observableBlocks scale width hwidth) :
    HasQuaternionBlockDegree i 1
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  have hm := of_decide_eq_true (List.mem_filter.mp hi).2
  have hd := word_present_degree i (fun e => (baseLinks width).idxOf e.link)
    (paddedSquare scale width hwidth).edges
    (paddedSquare_indices_nodup scale width hwidth) hm
  rw [wordAt_sourceWord width _ (paddedSquare scale width hwidth).physical] at hd
  simpa only [sourceCharacter, characterPolynomial] using hd.scalar.smul 2

private theorem observable_length (scale width : Nat) (hwidth : side scale < width) :
    (observableBlocks scale width hwidth).length = 4*side scale := by
  have hp := Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    (observableBlocks scale width hwidth) (loopSlots scale width hwidth)
    (observableBlocks_nodup scale width hwidth) (loopSlots_nodup scale width hwidth)
    (fun i => by
      constructor
      · intro hi
        exact of_decide_eq_true (List.mem_filter.mp hi).2
      · intro hi
        obtain ⟨e, he, hidx⟩ := List.mem_map.mp hi
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (hidx ▸
          List.idxOf_lt_length_of_mem ((paddedSquare scale width hwidth).physical e he)),
          by simp [hi]⟩)
  exact hp.length_eq.trans (loopSlots_length scale width hwidth)

private theorem negative_linear_block {n i : Nat} (hi : i < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hd : HasQuaternionBlockDegree i 1 p) :
    HaarCarrierEqv n (polyNeg (blockAngularLaplacian i p)) (polySmul 3 p) :=
  (HaarCarrierEqv.neg (blockCasimir_linear hi p hp hd)).trans
    (RatPolyCoeffEqv.haarCarrier ((neg_smul (polySmul (-3) p)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) (-3) p).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide) p))))

private theorem active_linear_casimir {n : Nat} (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) : ∀ active : List Nat,
    (∀ i, i ∈ active → i < n) →
    (∀ i, i ∈ active → HasQuaternionBlockDegree i 1 p) →
    HaarCarrierEqv n (activeCasimirPolynomial active p)
      (polySmul (3*Q'.ofNat active.length) p)
  | [], _, _ => (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.smul_coefficient (by decide :
        (3*Q'.ofNat 0 : Q') ≈ 0) p).trans (RatPolyCoeffEqv.zero_smul p))).symm
  | i::is, hr, hd => by
      have h := HaarCarrierEqv.add
        (negative_linear_block (hr i List.mem_cons_self) p hp (hd i List.mem_cons_self))
        (active_linear_casimir p hp is
          (fun j hj => hr j (List.mem_cons_of_mem i hj))
          (fun j hj => hd j (List.mem_cons_of_mem i hj)))
      have hc : (3 : Q')+3*Q'.ofNat is.length ≈ 3*Q'.ofNat (i::is).length :=
        Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (.add (.const 3) (.mul (.const 3) (.var 0)))
          (.mul (.const 3) (.add (.var 0) (.const 1)))
          (by decide) (fun _ => Q'.ofNat is.length))
          (Q'.mul_eqv_congr_left 3 _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv is.length 1)))
      exact h.trans (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.add_smul_same 3 (3*Q'.ofNat is.length) p).trans
          (RatPolyCoeffEqv.smul_coefficient hc p)))

/-- The full ORIGINAL Haar-slice Casimir is three times the growing perimeter.
This is not an interacting transfer eigenidentity. -/
theorem paddedSquare_casimir (scale width : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    HaarCarrierEqv (N width)
      (activeCasimirPolynomial (List.range (N width)) f)
      (polySmul (12*Q'.ofNat (side scale)) f) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hp := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hactive := active_linear_casimir f hp (observableBlocks scale width hwidth)
    (observableBlocks_lt scale width hwidth) (paddedSquare_character_degree scale width hwidth)
  have hc : (3 : Q')*Q'.ofNat (observableBlocks scale width hwidth).length ≈
      12*Q'.ofNat (side scale) := by
    rw [observable_length]
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 3 _ _ (ofNat_mul_eqv 4 (side scale)))
      (poly_identity_of_normal_eq (.mul (.const 3) (.mul (.const 4) (.var 0)))
        (.mul (.const 12) (.var 0)) (by decide) (fun _ => Q'.ofNat (side scale)))
  exact (RatPolyCoeffEqv.haarCarrier
    (activeCasimirPolynomial_range_eq_active (N width)
      (spectatorBlocks scale width hwidth) (observableBlocks scale width hwidth)
      (spectator_observable_cover scale width hwidth) f
      (sourceCharacter_spectator_independent scale width hwidth))).trans
    (hactive.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_coefficient hc f)))

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

attribute [local irreducible] terminalMessage spatialWeight sourceWord sourceCharacter

/-- Full-weight Ward identity at the ACTUAL interacting mean, with no
source-square substitution and no sign assigned to the weight derivative. -/
theorem paddedSquare_ward {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    marginalAngular w K width n f + wardResidual hw0 hw1 K width hK n f ≈
      (12*Q'.ofNat (side scale))*(oddMass w K width n *
        oddVariance hw0 hw1 K width hK n f) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have h := complete_ward_own_mean (baseLinks_positive width)
    (marginalWeight w K width n) f (marginalMass_positive hw0 hw1 K width hK n)
    (12*Q'.ofNat (side scale)) (paddedSquare_casimir scale width hwidth)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm (totalEnergy_finSum _ _ _)) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (marginalMass_pin w K width n))
        (Q'.mul_eqv_congr_left _ _ _ (marginalVariance_pin hw0 hw1 K width hK n f)))))

theorem paddedSquare_normalized_ward {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    normalizedAngular hw0 hw1 K width hK n f +
      normalizedWardResidual hw0 hw1 K width hK n f ≈
        (12*Q'.ofNat (side scale))*oddVariance hw0 hw1 K width hK n f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let k := (12 : Q')*Q'.ofNat (side scale)
  let z := oddMass w K width n
  let v := oddVariance hw0 hw1 K width hK n f
  let r := Q'.recipPos z (oddMass_positive hw0 hw1 K width hK n)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (paddedSquare_ward hw0 hw1 K width hK n scale hwidth))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => k | 1 => z | 2 => v | _ => r))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z
          (oddMass_positive hw0 hw1 K width hK n))) (Q'.mul_one_eqv _))))

/-- Exact growing-square temporal energy against the SAME interacting
variance. The COMPLETE signed remainder is the existing original one. -/
theorem paddedSquare_energy_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    normalizedEnergy hw0 hw1 K width hK n f ≈
      (12*Q'.ofNat (side scale))*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n f) +
        varianceRemainder hw0 hw1 K width hK n f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := normalizedAngular hw0 hw1 K width hK n f
  let b := normalizedWardResidual hw0 hw1 K width hK n f
  let r := normalizedRemainder hw0 hw1 K width hK n f
  let v := oddVariance hw0 hw1 K width hK n f
  let k := (12 : Q')*Q'.ofNat (side scale)
  let h := (1 : Q')-w
  have hj := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have ht := normalizedEnergy_taylor hw0 hw1 K width hK n f
    (sourceCharacter_supported width _ 1) (baseLinks_positive width)
    (paddedSquare_fringe_independent scale width hwidth)
  have halg : h*a+r ≈ h*(a+b)+(r+ -(h*b)) :=
    poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 3))
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 3) (.neg (.mul (.var 0) (.var 2)))))
      (by decide) (fun | 0 => h | 1 => a | 2 => b | _ => r)
  exact Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ halg
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hj)
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => h | 1 => k | _ => v))) (Q'.eqv_refl _)))

/-- The existing square completion now acts on the ACTUAL growing loop.
All complete centered source/Ward/cutoff debts remain in the displayed error. -/
theorem paddedSquare_energy_centered_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    normalizedEnergy hw0 hw1 K width hK n f ≤
      ((12*Q'.ofNat (side scale))*((1 : Q')-w)+quadraticRate w) *
        oddVariance hw0 hw1 K width hK n f +
          completeCenteredError hw0 hw1 K width hK n f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let A := normalizedAngular hw0 hw1 K width hK n f
  let W := normalizedWardResidual hw0 hw1 K width hK n f
  let V := oddVariance hw0 hw1 K width hK n f
  let D := BF4ExactSlabFixedSpatialCenteredRemainderSquare.normalizedCenteredError
    hw0 hw1 K width hK n f
  let h := (1 : Q')-w
  let k := (12 : Q')*Q'.ofNat (side scale)
  let beta := quadraticRate w
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hind := paddedSquare_fringe_independent scale width hwidth
  have hward := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have hupper := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedEnergy_centered_taylor hw0 hw1 K width hK n hf hind))
    (Q'.add_le_add_left (h*A) _ _
      (normalizedRemainder_centered_square_bound hw0 hw1 K width hK hquad n hf hind))
  have hjoin : h*A+(beta*V+D) ≈ h*(A+W)+beta*V+(D-h*W) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 4) (.var 3)) (.var 5)))
      (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 4) (.var 3)))
        (.add (.var 5) (.neg (.mul (.var 0) (.var 2)))))
      (by decide) (fun | 0 => h | 1 => A | 2 => W | 3 => V | 4 => beta | _ => D)
  exact Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hjoin
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hward) (Q'.eqv_refl _))
      (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.var 2))) (.var 4))
        (.add (.mul (.add (.mul (.var 1) (.var 0)) (.var 3)) (.var 2)) (.var 4))
        (by decide) (fun | 0 => h | 1 => k | 2 => V | 3 => beta | _ => D-h*W)))))

/-- Direct expression of the identity in the EXISTING finite reference-ratio
consumer's energy and variance, on its original headCutoff+stage schedule. -/
theorem finiteSquare_energy_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (stage depth : Nat) :
    let e : WindowExpression width := .loop 0 (paddedSquare scale width hwidth) 1
    finiteEnergy hw0 hw1 e stage depth ≈
      (12*Q'.ofNat (side scale))*(((1 : Q')-w)*finiteVariance hw0 hw1 e stage depth) +
        varianceRemainder hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          depth (sourcePolynomial e) := by
  simpa only [finiteEnergy, finiteVariance, sourcePolynomial, Nat.zero_mul, liftBoundary]
    using paddedSquare_energy_variance hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) depth scale hwidth

#print axioms paddedSquare_character_degree
#print axioms paddedSquare_casimir
#print axioms paddedSquare_ward
#print axioms paddedSquare_normalized_ward
#print axioms paddedSquare_energy_variance
#print axioms paddedSquare_energy_centered_square
#print axioms finiteSquare_energy_variance

end YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor
