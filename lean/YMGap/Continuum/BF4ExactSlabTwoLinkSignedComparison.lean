/-
# Signed two-link comparison in the original full action

Only the at-most-twelve faces touching the two selected physical links are
bounded. The reference retains every other original heat factor and allows
arbitrary spectator dependence in both tests. The centered mixed comparison
is finite polynomial algebra; no conditional-pair angle or gap is inferred.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
import YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
import YMGap.Continuum.QuaternionHaarSignedFormComparison
import YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
import YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison

namespace YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSignedFormComparison
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

include hw0 hw1 hsmall hdelta in
/-- Two-sided signed mixed comparison on the actual full-face weight.
The detached reference is shared by arbitrary spectator-dependent tests. -/
theorem two_link_signed_pair (K extent : Nat) (left right : Z4Link)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q) :
    let W := fullWeight w K extent;
    let B := background w K extent [left,right];
    let L := twoLinkLower w;
    let U := twoLinkUpper w;
    -((U + -L) *
        (weightedPair (blocks extent) B p p + weightedPair (blocks extent) B q q)) ≤
      4 * weightedPair (blocks extent) W p q +
        -(2 * (L + U) * weightedPair (blocks extent) B p q) ∧
    4 * weightedPair (blocks extent) W p q +
        -(2 * (L + U) * weightedPair (blocks extent) B p q) ≤
      (U + -L) *
        (weightedPair (blocks extent) B p p + weightedPair (blocks extent) B q q) := by
  apply centered_polarization (fullWeight w K extent)
    (background w K extent [left,right]) (twoLinkLower w) (twoLinkUpper w)
  · intro z hz
    exact two_link_weighted_bounds hw0 hw1 hsmall hdelta K extent left right
      (Certificate.square z hz)
  · exact hp
  · exact hq

/-- The same comparison phrased in the original fullData and the retained
two-link background form, with the strict-nome finite cutoff explicit. -/
theorem two_link_signed_fullData (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)
    (p q : (fullData hwpos hwlt K extent hK).V) :
    let F := fullData hwpos hwlt K extent hK;
    let B0 := twoLinkBackgroundData hw0 hw1 hsmall hdelta K extent left right;
    let L := twoLinkLower w;
    let U := twoLinkUpper w;
    -((U + -L) * (B0.B p p + B0.B q q)) ≤
      4 * F.B p q + -(2 * (L + U) * B0.B p q) ∧
    4 * F.B p q + -(2 * (L + U) * B0.B p q) ≤
      (U + -L) * (B0.B p p + B0.B q q) :=
  two_link_signed_pair hw0 hw1 hsmall hdelta K extent left right
    p.val q.val p.property q.property

/-- The signed mixed comparison on the SAME original completed carrier.
The background map preserves every Cauchy polynomial term and changes only
the explicit modulus; no completed-vector representative is selected. -/
theorem completed_signed_pair (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q'))
    (hd : heatRemainderBound w < 1)
    (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)
    (x y : GNSCompletionSpace (fullData hwpos hwlt K extent hK)) :
    let F := fullData hwpos hwlt K extent hK;
    let B0 := twoLinkBackgroundData hw0 hw1 hsmall hdelta K extent left right;
    let J := toBackground hwpos hwlt hsmall hd K extent hK left right;
    let L := twoLinkLower w;
    let U := twoLinkUpper w;
    CReal.RCle
      (CReal.RCneg (CReal.RCscale (U + -L)
        (CReal.RCadd (B0.cinnerCompl (J x) (J x))
          (B0.cinnerCompl (J y) (J y)))))
      (CReal.RCsub (CReal.RCscale 4 (F.cinnerCompl x y))
        (CReal.RCscale (2 * (L + U)) (B0.cinnerCompl (J x) (J y)))) ∧
    CReal.RCle
      (CReal.RCsub (CReal.RCscale 4 (F.cinnerCompl x y))
        (CReal.RCscale (2 * (L + U)) (B0.cinnerCompl (J x) (J y))))
      (CReal.RCscale (U + -L)
        (CReal.RCadd (B0.cinnerCompl (J x) (J x))
          (B0.cinnerCompl (J y) (J y)))) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let F := fullData hwpos hwlt K extent hK
  let B0 := twoLinkBackgroundData hw0 hw1 hsmall hdelta K extent left right
  let BX := toBackgroundCauchy hwpos hwlt hsmall hd K extent hK left right X
  let BY := toBackgroundCauchy hwpos hwlt hsmall hd K extent hK left right Y
  let L := twoLinkLower w
  let U := twoLinkUpper w
  change CReal.leEv
    (CReal.neg (CReal.mul (CReal.ofQ' (U + -L))
      (CReal.add (B0.cinnerRep BX BX) (B0.cinnerRep BY BY))))
    (CReal.add
      (CReal.mul (CReal.ofQ' 4) (F.cinnerRep X Y))
      (CReal.neg (CReal.mul (CReal.ofQ' (2 * (L + U)))
        (B0.cinnerRep BX BY)))) ∧
    CReal.leEv
      (CReal.add
        (CReal.mul (CReal.ofQ' 4) (F.cinnerRep X Y))
        (CReal.neg (CReal.mul (CReal.ofQ' (2 * (L + U)))
          (B0.cinnerRep BX BY))))
      (CReal.mul (CReal.ofQ' (U + -L))
        (CReal.add (B0.cinnerRep BX BX) (B0.cinnerRep BY BY)))
  have hfxy := CReal.convergesTo_ofQ'CauchySeq _ (F.cInnerQCauchy X Y)
  have hbxy := CReal.convergesTo_ofQ'CauchySeq _ (B0.cInnerQCauchy BX BY)
  have hbxx := CReal.convergesTo_ofQ'CauchySeq _ (B0.cInnerQCauchy BX BX)
  have hbyy := CReal.convergesTo_ofQ'CauchySeq _ (B0.cInnerQCauchy BY BY)
  have hsum := CReal.convergesTo_add hbxx hbyy
  have hright := CReal.convergesTo_const_mul (CReal.ofQ' (U + -L)) hsum
  have hleft := CReal.convergesTo_neg hright
  have hmiddle := CReal.convergesTo_add
    (CReal.convergesTo_const_mul (CReal.ofQ' 4) hfxy)
    (CReal.convergesTo_neg
      (CReal.convergesTo_const_mul (CReal.ofQ' (2 * (L + U))) hbxy))
  have hterm (n : Nat) := two_link_signed_fullData hw0 hw1 hsmall hdelta
    hwpos hwlt K extent hK left right (X.seq n) (Y.seq n)
  constructor
  · exact CReal.leEv_of_convergesTo_le hleft hmiddle
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (hterm n).1
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))
  · exact CReal.leEv_of_convergesTo_le hmiddle hright
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (hterm n).2
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

include hw0 hw1 hsmall hdelta in
/-- Haar integration at either selected physical link contracts the SAME
detached certified background norm. This assertion has no full-action
projection or conditional-angle conclusion. -/
theorem detached_project_square_contraction (K extent : Nat)
    (left right : Z4Link)
    (i : {j : Z4Link // j ∈ boundaryCompleteSlabLinks extent})
    (hi : i.val ∈ [left,right]) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let block := (boundaryCompleteSlabLinks extent).idxOf i.val
    let B := background w K extent [left,right]
    weightedPair (blocks extent) B (project block p) (project block p) ≤
      weightedPair (blocks extent) B p p := by
  exact weighted_project_square_contraction (blocks extent)
    ((boundaryCompleteSlabLinks extent).idxOf i.val)
    (List.idxOf_lt_length_of_mem i.property)
    (background w K extent [left,right]) p
    (small_background_certificate hw0 hw1 hsmall hdelta K extent [left,right])
    (background_independent_on_support w K extent [left,right] i.property hi) hp

end YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison

#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison.two_link_signed_pair
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison.two_link_signed_fullData
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison.completed_signed_pair
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkSignedComparison.detached_project_square_contraction
