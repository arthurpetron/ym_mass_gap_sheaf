/-
# Frozen local marginal jets of the original last-step mass

The checked local score Gram has moments D and G under the SAME original
last-step action. These coefficient identities identify them with frozen
first and all nine ordered second paired output derivatives of T1. The
homogeneous local cost remains explicit in G. No derivative acts on an
output coefficient, and no signed-Fisher upper estimate is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
  (lastStepAction action_integral_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepPairedResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram
  (localPrefix localFrozenFirst localFrozenAugmentedSecond localSignedFisher
    lastStep_local_signed_gram)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (angularDerivative_partialHaarHeads angularDerivative_blockIndependent_zero
    partialHaarHeads_add partialHaarHeads_neg partialHaarHeads_smul)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
  (partialHaarHeads_congr partialHaarHeads_mul_lift)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (heatAt_symm)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
  (lift_add lift_product lift_smul)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr threeSum_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate
  (Certificate haar_of_coeff)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica (momentD momentG)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder (conditionalFisher)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
  (prefixFrozenCurvatureCutoff)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (pairedScorePlus)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

/-- The coefficient is frozen: this differentiates T1, not the vector field u. -/
def frozenMarginalFirst (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  firstJet u (fun i => pairedDerivativeAt s i (transferStep w K width polyOne))

/-- Every ordered i,j derivative is retained, without differentiating u. -/
def frozenMarginalSecond (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  quadraticForm u (fun i j => pairedDerivativeAt s i
    (pairedDerivativeAt s j (transferStep w K width polyOne)))

theorem paired_congr (block : Nat) (i : Fin 3) {P Q : RatPoly}
    (h : RatPolyCoeffEqv P Q) :
    RatPolyCoeffEqv (pairedDerivativeAt block i P) (pairedDerivativeAt block i Q) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      exact (angularDerivative_congr _ _ h).add
        (RatPolyCoeffEqv.neg (angularDerivative_congr _ _ h))
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)

theorem paired_partial (heads s : Nat) (i : Fin 3) (F : RatPoly) :
    RatPolyCoeffEqv
      (pairedDerivativeAt s i (partialHaarHeads heads F))
      (partialHaarHeads heads (pairedDerivativeAt (heads+s) i F)) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simpa only [pairedDerivativeAt, blockAngularDerivative, Nat.mul_add,
      Nat.add_assoc, partialHaarHeads_add] using
      ((angularDerivative_partialHaarHeads heads (4*s+0) (4*s+1) F).add
        (angularDerivative_partialHaarHeads heads (4*s+2) (4*s+3) F))
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      let D02 := angularDerivative (4*(heads+s)+0) (4*(heads+s)+2) F
      let D13 := angularDerivative (4*(heads+s)+1) (4*(heads+s)+3) F
      have h02 : RatPolyCoeffEqv
          (angularDerivative (4*s+0) (4*s+2) (partialHaarHeads heads F))
          (partialHaarHeads heads D02) := by
        simpa only [D02, Nat.mul_add, Nat.add_assoc] using
          angularDerivative_partialHaarHeads heads (4*s+0) (4*s+2) F
      have h13 : RatPolyCoeffEqv
          (angularDerivative (4*s+1) (4*s+3) (partialHaarHeads heads F))
          (partialHaarHeads heads D13) := by
        simpa only [D13, Nat.mul_add, Nat.add_assoc] using
          angularDerivative_partialHaarHeads heads (4*s+1) (4*s+3) F
      have hneg : RatPolyCoeffEqv
          (polyNeg (partialHaarHeads heads D13))
          (partialHaarHeads heads (polyNeg D13)) :=
        (partialHaarHeads_neg heads D13).symm
      have hsum : RatPolyCoeffEqv
          (polyAdd
            (angularDerivative (4*s+0) (4*s+2) (partialHaarHeads heads F))
            (polyNeg (angularDerivative (4*s+1) (4*s+3)
              (partialHaarHeads heads F))))
          (polyAdd (partialHaarHeads heads D02)
            (partialHaarHeads heads (polyNeg D13))) :=
        (h02.add (RatPolyCoeffEqv.neg h13)).trans
          ((RatPolyCoeffEqv.refl (partialHaarHeads heads D02)).add hneg)
      change RatPolyCoeffEqv _
        (partialHaarHeads heads (polyAdd D02 (polyNeg D13)))
      rw [partialHaarHeads_add]
      exact hsum
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simpa only [pairedDerivativeAt, blockAngularDerivative, Nat.mul_add,
        Nat.add_assoc, partialHaarHeads_add] using
        ((angularDerivative_partialHaarHeads heads (4*s+0) (4*s+3) F).add
          (angularDerivative_partialHaarHeads heads (4*s+1) (4*s+2) F))

private theorem plane_product (block j k : Nat) (hj : j < 4) (hk : k < 4)
    (q P : RatPoly) (hq : QuaternionBlockIndependent block q) :
    RatPolyCoeffEqv (blockAngularDerivative block j k (polyMul q P))
      (polyMul q (blockAngularDerivative block j k P)) := by
  have hz := angularDerivative_blockIndependent_zero hj hk hq
  have hrest : RatPolyCoeffEqv
      (polyAdd (polyMul (blockAngularDerivative block j k q) P)
        (polyMul q (blockAngularDerivative block j k P)))
      (polyMul q (blockAngularDerivative block j k P)) :=
    (((hz.mul_right P).trans (RatPolyCoeffEqv.mul_zero_left P)).add
      (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)
  exact (angularDerivative_mul _ _ q P).trans hrest

theorem paired_product (block : Nat) (i : Fin 3) (q P : RatPoly)
    (hq : QuaternionBlockIndependent block q) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (polyMul q P))
      (polyMul q (pairedDerivativeAt block i P)) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    exact ((plane_product block 0 1 (by decide) (by decide) q P hq).add
      (plane_product block 2 3 (by decide) (by decide) q P hq)).trans
        (RatPolyCoeffEqv.mul_add_right q _ _).symm
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      refine ((plane_product block 0 2 (by decide) (by decide) q P hq).add
        (RatPolyCoeffEqv.neg (plane_product block 1 3 (by decide) (by decide) q P hq))).trans ?_
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => q | 1 => blockAngularDerivative block 0 2 P
          | _ => blockAngularDerivative block 1 3 P)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      exact ((plane_product block 0 3 (by decide) (by decide) q P hq).add
        (plane_product block 1 2 (by decide) (by decide) q P hq)).trans
          (RatPolyCoeffEqv.mul_add_right q _ _).symm

private theorem action_mass_pin (w : Q') (K width : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (N width) (lastStepAction w K width))
      (transferStep w K width polyOne) :=
  ((partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_one (lastStepAction w K width)).symm).trans
      (action_integral_pin w K width polyOne))

theorem local_factor_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) :
    RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s) (localPrefix w K width s))
      (lastStepAction w K width) :=
  ((heatAt_symm (N width+s) s w K).mul_left _).trans
    (localOutputDensity_action_pin w K width s hs)

private theorem first_unweighted_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (i : Fin 3) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (localOutputDensity w K width s)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))
      (pairedDerivativeAt s i (transferStep w K width polyOne)) := by
  let q := localOutputDensity w K width s
  let P := localPrefix w K width s
  have hq := localOutputDensity_independent w K width s hs
  have hfactor := local_factor_pin w K width s hs
  have h : RatPolyCoeffEqv
      (polyMul q (pairedDerivativeAt (N width+s) i P))
      (pairedDerivativeAt (N width+s) i (lastStepAction w K width)) :=
    (paired_product (N width+s) i q P hq).symm.trans
      (paired_congr (N width+s) i hfactor)
  exact (partialHaarHeads_congr (N width) h).trans
    ((paired_partial (N width) s i (lastStepAction w K width)).symm.trans
      (paired_congr s i (action_mass_pin w K width)))

private theorem second_unweighted_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (i j : Fin 3) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (localOutputDensity w K width s)
          (pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j (localPrefix w K width s)))))
      (pairedDerivativeAt s i
        (pairedDerivativeAt s j (transferStep w K width polyOne))) := by
  let q := localOutputDensity w K width s
  let P := localPrefix w K width s
  have hq := localOutputDensity_independent w K width s hs
  have hfactor := local_factor_pin w K width s hs
  have hproduct : RatPolyCoeffEqv
      (pairedDerivativeAt (N width+s) i (pairedDerivativeAt (N width+s) j (polyMul q P)))
      (polyMul q (pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j P))) :=
    (paired_congr (N width+s) i (paired_product (N width+s) j q P hq)).trans
      (paired_product (N width+s) i q (pairedDerivativeAt (N width+s) j P) hq)
  have h : RatPolyCoeffEqv
      (polyMul q (pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j P)))
      (pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j (lastStepAction w K width))) :=
    hproduct.symm.trans (paired_congr (N width+s) i
      (paired_congr (N width+s) j hfactor))
  have hpartial : RatPolyCoeffEqv
      (pairedDerivativeAt s i (pairedDerivativeAt s j
        (partialHaarHeads (N width) (lastStepAction w K width))))
      (partialHaarHeads (N width)
        (pairedDerivativeAt (N width+s) i
          (pairedDerivativeAt (N width+s) j (lastStepAction w K width)))) :=
    (paired_congr s i (paired_partial (N width) s j (lastStepAction w K width))).trans
      (paired_partial (N width) s i
        (pairedDerivativeAt (N width+s) j (lastStepAction w K width)))
  exact (partialHaarHeads_congr (N width) h).trans
    (hpartial.symm.trans (paired_congr s i
      (paired_congr s j (action_mass_pin w K width))))

theorem integrate_threeSum (heads : Nat) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads heads (threeSum f))
      (threeSum (fun i => partialHaarHeads heads (f i))) := by
  unfold threeSum
  rw [partialHaarHeads_add, partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

theorem integrate_add (heads : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads heads (polyAdd p q))
      (polyAdd (partialHaarHeads heads p) (partialHaarHeads heads q)) := by
  rw [partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

theorem integrate_quadratic (heads : Nat) (f : Fin 3 → Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (threeSum (fun i => threeSum (f i))))
      (threeSum (fun i => threeSum (fun j => partialHaarHeads heads (f i j)))) :=
  (integrate_threeSum heads _).trans
    ((integrate_threeSum heads (f 0)).add
      ((integrate_threeSum heads (f 1)).add (integrate_threeSum heads (f 2))))

theorem pull_coefficient (heads : Nat) (u F : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul (liftBoundary heads u) F))
      (polyMul u (partialHaarHeads heads F)) := by
  have h := partialHaarHeads_mul_lift heads F u
  exact (partialHaarHeads_congr heads (RatPolyCoeffEqv.mul_comm _ F)).trans
    (h.trans (RatPolyCoeffEqv.mul_comm _ u))

private theorem first_term_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (i : Fin 3) (u : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (localOutputDensity w K width s)
        (polyMul (liftBoundary (N width) u)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))))
      (polyMul u (pairedDerivativeAt s i (transferStep w K width polyOne))) := by
  have hmove : RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s)
        (polyMul (liftBoundary (N width) u)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))
      (polyMul (liftBoundary (N width) u)
        (polyMul (localOutputDensity w K width s)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun
        | 0 => localOutputDensity w K width s
        | 1 => liftBoundary (N width) u
        | _ => pairedDerivativeAt (N width+s) i (localPrefix w K width s))
  exact (partialHaarHeads_congr (N width) hmove).trans
    ((pull_coefficient (N width) u _).trans
      ((first_unweighted_pin w K width s hs i).mul_left u))

private theorem second_term_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (i j : Fin 3) (ui uj : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (localOutputDensity w K width s)
        (polyMul (polyMul (liftBoundary (N width) ui) (liftBoundary (N width) uj))
          (pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))))
      (polyMul (polyMul ui uj)
        (pairedDerivativeAt s i
          (pairedDerivativeAt s j (transferStep w K width polyOne)))) := by
  let F := pairedDerivativeAt (N width+s) i
    (pairedDerivativeAt (N width+s) j (localPrefix w K width s))
  have hmove : RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s)
        (polyMul (polyMul (liftBoundary (N width) ui) (liftBoundary (N width) uj)) F))
      (polyMul (liftBoundary (N width) (polyMul ui uj))
        (polyMul (localOutputDensity w K width s) F)) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => localOutputDensity w K width s
        | 1 => liftBoundary (N width) ui
        | 2 => liftBoundary (N width) uj | _ => F)
  exact (partialHaarHeads_congr (N width) hmove).trans
    ((pull_coefficient (N width) (polyMul ui uj) _).trans
      ((second_unweighted_pin w K width s hs i j).mul_left (polyMul ui uj)))

private theorem first_sum_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentD (N width) (localOutputDensity w K width s)
        (localFrozenFirst w K width s u))
      (frozenMarginalFirst w K width s u) := by
  change RatPolyCoeffEqv
    (partialHaarHeads (N width) (polyMul (localOutputDensity w K width s)
      (threeSum (fun i => polyMul (liftBoundary (N width) (u i))
        (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))))
    (threeSum (fun i => polyMul (u i)
      (pairedDerivativeAt s i (transferStep w K width polyOne))))
  have hdistrib : RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s)
        (threeSum (fun i => polyMul (liftBoundary (N width) (u i))
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))))
      (threeSum (fun i => polyMul (localOutputDensity w K width s)
        (polyMul (liftBoundary (N width) (u i))
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_add_right _ _ _))
  exact (partialHaarHeads_congr (N width) hdistrib).trans
    ((integrate_threeSum (N width) _).trans
      ((first_term_pin w K width s hs 0 (u 0)).add
        ((first_term_pin w K width s hs 1 (u 1)).add
          (first_term_pin w K width s hs 2 (u 2)))))

private theorem second_sum_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (localOutputDensity w K width s)
          (quadraticForm (fun i => liftBoundary (N width) (u i))
            (fun i j => pairedDerivativeAt (N width+s) i
              (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))))
      (frozenMarginalSecond w K width s u) := by
  let q := localOutputDensity w K width s
  let v := fun i => liftBoundary (N width) (u i)
  let M := fun i j => pairedDerivativeAt (N width+s) i
    (pairedDerivativeAt (N width+s) j (localPrefix w K width s))
  have hdistrib : RatPolyCoeffEqv
      (polyMul q (quadraticForm v M))
      (threeSum (fun i => threeSum (fun j => polyMul q (polyMul (polyMul (v i) (v j)) (M i j))))) := by
    unfold quadraticForm
    exact (threeSum_mul_left q _).symm.trans
      (threeSum_congr (fun i => (threeSum_mul_left q _).symm))
  change RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul q (quadraticForm v M)))
    (frozenMarginalSecond w K width s u)
  exact (partialHaarHeads_congr (N width) hdistrib).trans
    ((integrate_quadratic (N width) _).trans
      (((second_term_pin w K width s hs 0 0 (u 0) (u 0)).add
        ((second_term_pin w K width s hs 0 1 (u 0) (u 1)).add
          (second_term_pin w K width s hs 0 2 (u 0) (u 2)))).add
        (((second_term_pin w K width s hs 1 0 (u 1) (u 0)).add
          ((second_term_pin w K width s hs 1 1 (u 1) (u 1)).add
            (second_term_pin w K width s hs 1 2 (u 1) (u 2)))).add
          ((second_term_pin w K width s hs 2 0 (u 2) (u 0)).add
            ((second_term_pin w K width s hs 2 1 (u 2) (u 1)).add
              (second_term_pin w K width s hs 2 2 (u 2) (u 2)))))))

theorem lift_threeSquare (heads : Nat) (u : Fin 3 → RatPoly) :
    liftBoundary heads (threeSquare u) =
      threeSquare (fun i => liftBoundary heads (u i)) := by
  simp only [threeSquare, lift_add, lift_product]

private theorem cost_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (localOutputDensity w K width s)
        (polyMul (polyMul (cap (prefixCurvatureCost w))
          (threeSquare (fun i => liftBoundary (N width) (u i))))
          (localPrefix w K width s))))
      (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
        (transferStep w K width polyOne)) := by
  let q := localOutputDensity w K width s
  let P := localPrefix w K width s
  let C := prefixCurvatureCost w
  have hmove : RatPolyCoeffEqv
      (polyMul q (polyMul (polyMul (cap C)
        (threeSquare (fun i => liftBoundary (N width) (u i)))) P))
      (polyMul (cap C)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P))) := by
    rw [lift_threeSquare]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 3))))
      (by decide) (fun
        | 0 => q | 1 => cap C
        | 2 => threeSquare (fun i => liftBoundary (N width) (u i)) | _ => P)
  have hsmul : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (cap C)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P))))
      (polySmul C (partialHaarHeads (N width)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P)))) :=
    (partialHaarHeads_congr (N width) (cap_mul_left C _)).trans
      (partialHaarHeads_smul (N width) C _)
  have hpull := pull_coefficient (N width) (threeSquare u) (polyMul q P)
  have hmass : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul q P))
      (transferStep w K width polyOne) :=
    (partialHaarHeads_congr (N width) (local_factor_pin w K width s hs)).trans
      (action_mass_pin w K width)
  have hfinal : RatPolyCoeffEqv
      (polySmul C (polyMul (threeSquare u) (transferStep w K width polyOne)))
      (polyMul (polyMul (cap C) (threeSquare u))
        (transferStep w K width polyOne)) := by
    exact (RatPolyCoeffEqv.polyMul_smul_left C (threeSquare u)
      (transferStep w K width polyOne)).symm.trans
        ((cap_mul_left C (threeSquare u)).symm.mul_right _)
  exact (partialHaarHeads_congr (N width) hmove).trans
    (hsmul.trans ((RatPolyCoeffEqv.smul C (hpull.trans
      (hmass.mul_left (threeSquare u)))).trans hfinal))

/-- D is exactly the frozen first paired derivative of the ORIGINAL T1. -/
theorem local_momentD_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentD (N width) (localOutputDensity w K width s)
        (localFrozenFirst w K width s u))
      (frozenMarginalFirst w K width s u) :=
  first_sum_pin w K width s hs u

/-- G keeps all nine frozen second jets and its homogeneous cost. -/
theorem local_momentG_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentG (N width) (localOutputDensity w K width s)
        (localFrozenAugmentedSecond w K width s u))
      (polyAdd (frozenMarginalSecond w K width s u)
        (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
          (transferStep w K width polyOne))) := by
  change RatPolyCoeffEqv
    (partialHaarHeads (N width)
      (polyMul (localOutputDensity w K width s)
        (polyAdd (quadraticForm (fun i => liftBoundary (N width) (u i))
          (fun i j => pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))
          (polyMul (polyMul (cap (prefixCurvatureCost w))
            (threeSquare (fun i => liftBoundary (N width) (u i))))
            (localPrefix w K width s))))) _
  exact (partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_add_right _ _ _)).trans
      ((integrate_add (N width) _ _).trans
        ((second_sum_pin w K width s hs u).add (cost_pin w K width s hs u)))

/-- The signed Fisher in the checked local Gram is the actual frozen
T1 Hessian combination, retaining the negative mean-square term. -/
theorem localSignedFisher_marginal_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (localSignedFisher w K width s u)
      (polyAdd
        (polyMul (transferStep w K width polyOne)
          (polyAdd (frozenMarginalSecond w K width s u)
            (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
              (transferStep w K width polyOne))))
        (polyNeg (polyMul (frozenMarginalFirst w K width s u)
          (frozenMarginalFirst w K width s u)))) := by
  have hA := (partialHaarHeads_congr (N width) (local_factor_pin w K width s hs)).trans
    (action_mass_pin w K width)
  have hD := local_momentD_pin w K width s hs u
  have hG := local_momentG_pin w K width s hs u
  exact (hA.mul hG).add (RatPolyCoeffEqv.neg (hD.mul hD))

/-- The checked original-action Gram with its signed Fisher replaced by the
actual frozen differential expression of T1. The noise and tail insertion are
unchanged; this supplies no upper bound on the signed Fisher itself. -/
theorem lastStep_local_differential_gram {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width s : Nat)
    (hs : s ∈ activeBlocks width) (hK : prefixFrozenCurvatureCutoff w ≤ K)
    {a c R : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (PR : Certificate (N width) R) :
    let score := firstJet u
      (pairedScorePlus s (transferStep w K width a) (transferStep w K width c))
    let X := lastStepPairedResidual w K width a c
    quaternionHaar (N width) (polyMul R
      (polyMul (transferStep w K width polyOne) (polyMul score score))) ≤
    quaternionHaar (N width) (polyMul R
      (polyMul (partialHaarHeads (N width)
        (polyMul (lastStepAction w K width) (polyMul X X)))
        (polyAdd
          (polyMul (transferStep w K width polyOne)
            (polyAdd (frozenMarginalSecond w K width s u)
              (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
                (transferStep w K width polyOne))))
          (polyNeg (polyMul (frozenMarginalFirst w K width s u)
            (frozenMarginalFirst w K width s u)))))) := by
  dsimp only
  have h := lastStep_local_signed_gram hw0 hw1 K width s hs hK ha hc u hu PR
  have hF := localSignedFisher_marginal_pin w K width s hs u
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (haar_of_coeff ((hF.mul_left _).mul_left R)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.frozenMarginalFirst
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.frozenMarginalSecond
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.paired_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.paired_partial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.paired_product
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.local_factor_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.integrate_threeSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.integrate_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.integrate_quadratic
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.pull_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.lift_threeSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.local_momentD_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.local_momentG_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.localSignedFisher_marginal_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets.lastStep_local_differential_gram
