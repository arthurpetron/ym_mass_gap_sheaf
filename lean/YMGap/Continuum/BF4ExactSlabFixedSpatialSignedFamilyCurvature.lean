/-
# Signed original spatial-family curvature on the actual passive channels

The equal, shared-link and disjoint branches retain the actual original
fundamental characters. Their remainder is signed. The classifier counts
geometric equality, not list-position equality; subsequent ordered-family
assembly must therefore keep every repeated occurrence.

Ordered occurrence pairs preserve every signed coefficient and repeated face.
The family identity is inserted into the existing ORIGINAL spectator Gram
channels. Only the assembled Gamma(F,F) is nonnegative; the explicit pair
remainder is still signed and unpaid against the OWN interacting variance.
No warmed-source response, scaling retention or physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
import YMGap.Continuum.QuaternionHaarGammaFiniteSum
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (activeCasimir_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelCurvature familyChannelObservableSquare)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSource_supported channelSum_congr channelSum_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks plaquette

private def faceChar (width : Nat) (p : Z4Plaq) : RatPoly :=
  characterPolynomial (plaquette width p).scalar 1

/-- The exact signed pair remainder; no coefficient or face sign is dropped. -/
def pairRemainder (width : Nat) (p q : Z4Plaq) : RatPoly :=
  if p = q then cap (-192)
  else if linkDisjoint p q then polySmul 48 (polyMul (faceChar width p) (faceChar width q))
  else polySmul 42 (polyMul (faceChar width p) (faceChar width q))

private theorem shared_of_all_false (ys : List Z4Link) :
    ∀ xs : List Z4Link, xs.all (fun l => decide (l ∉ ys)) = false →
      ∃ l, l ∈ xs ∧ l ∈ ys
  | [], h => by simp only [List.all_nil, Bool.true_eq_false] at h
  | l::ls, h =>
      if hl : l ∈ ys then ⟨l, List.mem_cons_self, hl⟩
      else by
        have hd : decide (l ∉ ys) = true := decide_eq_true hl
        have ht : ls.all (fun m => decide (m ∉ ys)) = false := by
          simpa only [List.all_cons, hd, Bool.true_and] using h
        obtain ⟨m, hm, hmy⟩ := shared_of_all_false ys ls ht
        exact ⟨m, List.mem_cons_of_mem l hm, hmy⟩

private theorem disjoint_gamma_zero (width : Nat) (p q : Z4Plaq)
    (hd : LinkDisjoint p q) : ∀ ids : List Nat,
    (∀ b, b ∈ ids → b < N width) →
    RatPolyCoeffEqv (activeGamma ids (faceChar width p) (faceChar width q)) polyZero
  | [], _ => .refl _
  | b::bs, hb =>
      ((blockGamma_zero width b hd (hb b List.mem_cons_self)).add
        (disjoint_gamma_zero width p q hd bs
          (fun c hc => hb c (List.mem_cons_of_mem b hc)))).trans
        (RatPolyCoeffEqv.add_zero polyZero)

private theorem equal_shape (f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul (-128) (polyAdd (polyMul f f) (polyNeg polyOne)))
        (polySmul 48 (polyMul f f)))
      (polyAdd (polySmul 20 (polySmul 4
        (polyAdd (cap 4) (polyNeg (polyMul f f))))) (cap (-192))) := by
  let sq := polyMul f f
  have hunit : RatPolyCoeffEqv polyOne (cap 1) :=
    (RatPolyCoeffEqv.one_smul polyOne).symm
  have hleft :=
    (((RatPolyCoeffEqv.refl sq).add (RatPolyCoeffEqv.neg hunit)).smul (-128)).trans
      (cap_mul_left (-128) (polyAdd sq (polyNeg (cap 1)))).symm
  have hright := ((cap_mul_left 4 (polyAdd (cap 4) (polyNeg sq))).symm.smul 20).trans
    (cap_mul_left 20 (polyMul (cap 4) (polyAdd (cap 4) (polyNeg sq)))).symm
  have hring := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.const (-128)) (.add (.var 0) (.neg (.const 1))))
      (.mul (.const 48) (.var 0)))
    (.add (.mul (.const 20) (.mul (.const 4) (.add (.const 4) (.neg (.var 0)))))
      (.const (-192))) (by decide) (fun _ => sq)
  exact (hleft.add (cap_mul_left 48 sq).symm).trans
    (hring.trans (hright.add (RatPolyCoeffEqv.refl _)).symm)

private theorem equal_pair (width : Nat) (p : Z4Plaq)
    (hp : p ∈ spatialFaces width) :
    let f := faceChar width p
    let g := activeGamma (List.range (N width)) f f
    HaarCarrierEqv (N width)
      (polyAdd (activeCasimirPolynomial (List.range (N width)) g) (polySmul 48 (polyMul f f)))
      (polyAdd (polySmul 20 g) (cap (-192))) := by
  dsimp only
  have hc := HaarCarrierEqv.add (plaquette_gamma_casimir width p hp)
    (HaarCarrierEqv.refl (N width) (polySmul 48 (polyMul (faceChar width p) (faceChar width p))))
  have hg := HaarCarrierEqv.add (HaarCarrierEqv.smul 20 (plaquette_gamma width p hp))
    (HaarCarrierEqv.refl (N width) (cap (-192)))
  exact hc.trans ((RatPolyCoeffEqv.haarCarrier (equal_shape (faceChar width p))).trans hg.symm)

private theorem shared_shape (g r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul 20 g) (polySmul (-6) r)) (polySmul 48 r))
      (polyAdd (polySmul 20 g) (polySmul 42 r)) :=
  (RatPolyCoeffEqv.add_assoc _ _ _).trans
    ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.add_smul_same (-6) 48 r).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((-6 : Q')+48) 42) r)))

/-- Full original pair classification, valid under every Haar insertion.
Physical membership is essential, and geometric equality includes repeats. -/
theorem pair_curvature_remainder (width : Nat) (p q : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width) :
    let fp := characterPolynomial (plaquette width p).scalar 1
    let fq := characterPolynomial (plaquette width q).scalar 1
    let g := activeGamma (List.range (N width)) fp fq
    HaarCarrierEqv (N width)
      (polyAdd (activeCasimirPolynomial (List.range (N width)) g) (polySmul 48 (polyMul fp fq)))
      (polyAdd (polySmul 20 g) (pairRemainder width p q)) := by
  dsimp only
  exact if he : p = q then by
    subst q
    simpa only [pairRemainder, if_pos rfl] using equal_pair width p hp
  else by
    cases hd : linkDisjoint p q with
    | true =>
      let ids := List.range (N width)
      let g := activeGamma ids (faceChar width p) (faceChar width q)
      let r := polyMul (faceChar width p) (faceChar width q)
      have hz := disjoint_gamma_zero width p q ((linkDisjoint_correct p q).mp hd) ids
        (fun b hb => List.mem_range.mp hb)
      have hc0 : RatPolyCoeffEqv (activeCasimirPolynomial ids polyZero) polyZero :=
        (activeCasimir_smul ids 0 polyZero).trans (RatPolyCoeffEqv.zero_smul _)
      have hc := (activeCasimirPolynomial_carrier ids (fun b hb => List.mem_range.mp hb)
        (RatPolyCoeffEqv.haarCarrier hz)).trans (RatPolyCoeffEqv.haarCarrier hc0)
      have hleft := (HaarCarrierEqv.add hc (HaarCarrierEqv.refl (N width) (polySmul 48 r))).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _))
      have hright := (HaarCarrierEqv.add (HaarCarrierEqv.smul 20 (RatPolyCoeffEqv.haarCarrier hz))
        (HaarCarrierEqv.refl (N width) (polySmul 48 r))).trans
        (RatPolyCoeffEqv.haarCarrier
          (((RatPolyCoeffEqv.smul_zero 20).add (RatPolyCoeffEqv.refl _)).trans
            (RatPolyCoeffEqv.zero_add _)))
      simpa only [pairRemainder, if_neg he, hd, ↓reduceIte] using hleft.trans hright.symm
    | false =>
      have hall : (edgesOf p).all (fun l => decide (l ∉ edgesOf q)) = false := hd
      obtain ⟨l, hlp, hlq⟩ := shared_of_all_false (edgesOf q) (edgesOf p) hall
      have h := HaarCarrierEqv.add (distinct_pair_full_gamma_casimir width p q hp hq he l hlp hlq)
        (HaarCarrierEqv.refl (N width)
          (polySmul 48 (polyMul (faceChar width p) (faceChar width q))))
      simpa only [pairRemainder, if_neg he, hd, ↓reduceIte] using
        h.trans (RatPolyCoeffEqv.haarCarrier (shared_shape _ _))

private def orderedFold (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (v : Z4Plaq → Z4Plaq → RatPoly) : RatPoly :=
  finitePolySum (fun p => finitePolySum (fun q => polySmul (c p*c q) (v p q)) qs) qs

/-- Literal ordered occurrence pairs, with no deduplication or absolute value. -/
def familyPairRemainder (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : RatPoly :=
  orderedFold c qs (pairRemainder width)

private theorem ordered_add (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (v u : Z4Plaq → Z4Plaq → RatPoly) :
    RatPolyCoeffEqv (orderedFold c qs (fun p q => polyAdd (v p q) (u p q)))
      (polyAdd (orderedFold c qs v) (orderedFold c qs u)) :=
  (finitePolySum_coeff_congr _ _ (fun p =>
    (finitePolySum_coeff_congr _ _ (fun q =>
      RatPolyCoeffEqv.smul_add (c p*c q) (v p q) (u p q)) qs).trans
      (finitePolySum_add _ _ qs)) qs).trans (finitePolySum_add _ _ qs)

private theorem ordered_smul (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (a : Q') (v : Z4Plaq → Z4Plaq → RatPoly) :
    RatPolyCoeffEqv (orderedFold c qs (fun p q => polySmul a (v p q)))
      (polySmul a (orderedFold c qs v)) :=
  (finitePolySum_coeff_congr _ _ (fun p =>
    (finitePolySum_coeff_congr _ _ (fun q =>
      (RatPolyCoeffEqv.smul_assoc (c p*c q) a (v p q)).trans
        ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv _ _) (v p q)).trans
          (RatPolyCoeffEqv.smul_assoc a (c p*c q) (v p q)).symm)) qs).trans
      (finitePolySum_smul a _ qs)) qs).trans (finitePolySum_smul a _ qs)

private theorem ordered_casimir (ids : List Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (v : Z4Plaq → Z4Plaq → RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial ids (orderedFold c qs v))
      (orderedFold c qs (fun p q => activeCasimirPolynomial ids (v p q))) :=
  (activeCasimir_finitePolySum ids _ qs).trans
    (finitePolySum_coeff_congr _ _ (fun p =>
      (activeCasimir_finitePolySum ids _ qs).trans
        (finitePolySum_coeff_congr _ _ (fun q =>
          activeCasimir_smul ids (c p*c q) (v p q)) qs)) qs)

private theorem ordered_gamma (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    RatPolyCoeffEqv
      (activeGamma (List.range (N width)) (spatialSpan width c qs) (spatialSpan width c qs))
      (orderedFold c qs (fun p q =>
        activeGamma (List.range (N width)) (faceChar width p) (faceChar width q))) :=
  (activeGamma_finitePolySum_pair (List.range (N width)) _ _ qs qs).trans
    (finitePolySum_coeff_congr _ _ (fun p => finitePolySum_coeff_congr _ _
      (fun q => activeGamma_smul_pair (List.range (N width)) (c p) (c q)
        (faceChar width p) (faceChar width q)) qs) qs)

private theorem ordered_square (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    RatPolyCoeffEqv (polyMul (spatialSpan width c qs) (spatialSpan width c qs))
      (orderedFold c qs (fun p q => polyMul (faceChar width p) (faceChar width q))) :=
  (finitePolySum_mul_pair _ _ qs qs).trans
    (finitePolySum_coeff_congr _ _ (fun p => finitePolySum_coeff_congr _ _ (fun q =>
      (RatPolyCoeffEqv.polyMul_smul_left (c p) _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right (c q) _ _).smul (c p)).trans
          (RatPolyCoeffEqv.smul_assoc (c p) (c q) _))) qs) qs)

private theorem finiteSum_carrier {I : Type} (n : Nat) (f g : I → RatPoly) :
    ∀ xs : List I, (∀ i, i ∈ xs → HaarCarrierEqv n (f i) (g i)) →
      HaarCarrierEqv n (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => .refl _ _
  | i::xs, h => HaarCarrierEqv.add (h i List.mem_cons_self)
      (finiteSum_carrier n f g xs (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem ordered_carrier (n : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (v u : Z4Plaq → Z4Plaq → RatPoly)
    (h : ∀ p, p ∈ qs → ∀ q, q ∈ qs → HaarCarrierEqv n (v p q) (u p q)) :
    HaarCarrierEqv n (orderedFold c qs v) (orderedFold c qs u) :=
  finiteSum_carrier n _ _ qs (fun p hp => finiteSum_carrier n _ _ qs
    (fun q hq => HaarCarrierEqv.smul (c p*c q) (h p hp q hq)))

/-- Complete signed curvature of the ORIGINAL family, valid under every
insertion. Membership is required for each occurrence, not a Nodup premise. -/
theorem family_curvature_remainder (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let ids := List.range (N width)
    let g := activeGamma ids f f
    HaarCarrierEqv (N width)
      (polyAdd (activeCasimirPolynomial ids g) (polySmul 48 (polyMul f f)))
      (polyAdd (polySmul 20 g) (familyPairRemainder width c qs)) := by
  dsimp only
  let ids := List.range (N width)
  let gv := fun p q => activeGamma ids (faceChar width p) (faceChar width q)
  let pv := fun p q => polyMul (faceChar width p) (faceChar width q)
  have hg := ordered_gamma width c qs
  have hc := (activeCasimirPolynomial_carrier ids (fun b hb => List.mem_range.mp hb)
    (RatPolyCoeffEqv.haarCarrier hg)).trans
      (RatPolyCoeffEqv.haarCarrier (ordered_casimir ids c qs gv))
  have hs := (ordered_square width c qs).smul 48
  have hleft := (HaarCarrierEqv.add hc (RatPolyCoeffEqv.haarCarrier hs)).trans
    (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add (ordered_smul c qs 48 pv).symm))
  have hexpand := hleft.trans (RatPolyCoeffEqv.haarCarrier
    (ordered_add c qs (fun p q => activeCasimirPolynomial ids (gv p q))
      (fun p q => polySmul 48 (pv p q))).symm)
  have hpairs := ordered_carrier (N width) c qs
    (fun p q => polyAdd (activeCasimirPolynomial ids (gv p q)) (polySmul 48 (pv p q)))
    (fun p q => polyAdd (polySmul 20 (gv p q)) (pairRemainder width p q))
    (fun p hp q hq => pair_curvature_remainder width p q (hqs p hp) (hqs q hq))
  have hcollect := (ordered_add c qs (fun p q => polySmul 20 (gv p q)) (pairRemainder width)).trans
    ((ordered_smul c qs 20 gv).add (RatPolyCoeffEqv.refl _))
  exact (hexpand.trans hpairs).trans ((RatPolyCoeffEqv.haarCarrier hcollect).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.smul 20 (RatPolyCoeffEqv.haarCarrier hg.symm))
      (HaarCarrierEqv.refl _ _)))

/-- The assembled diagonal Gamma, inserted into the ORIGINAL signed channels. -/
def familyChannelGradient (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids) (fun z =>
    let b := channelSource ids q z
    H (N width) (polyMul (polyMul b b) (activeGamma (List.range (N width)) f f)))

/-- Signed pair remainder with the SAME endpoint source and Gram insertions. -/
def familyChannelPairRemainder (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids) (fun z =>
    let b := channelSource ids q z
    H (N width) (polyMul (polyMul b b) (familyPairRemainder width c qs)))

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun z => left z + right z) ≈ channelSum cs left + channelSum cs right
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
             | 2 => channelSum cs left | _ => channelSum cs right))

/-- Exact join to the retained-square consumer. No channel-source sign, nome
bound or variance-payment hypothesis is used to obtain this equality. -/
theorem familyChannel_curvature_remainder (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    familyChannelCurvature w K width depth c qs +
        48*familyChannelObservableSquare w K width depth c qs ≈
      20*familyChannelGradient w K width depth c qs +
        familyChannelPairRemainder w K width depth c qs := by
  let f := spatialSpan width c qs
  let g := activeGamma (List.range (N width)) f f
  let cg := activeCasimirPolynomial (List.range (N width)) g
  let r := familyPairRemainder width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  let b := fun z => channelSource ids q z
  let cur := fun z => H (N width) (polyMul (polyMul (b z) (b z)) cg)
  let sq := fun z => H (N width) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let grad := fun z => H (N width) (polyMul (polyMul (b z) (b z)) g)
  let rem := fun z => H (N width) (polyMul (polyMul (b z) (b z)) r)
  have hF := family_curvature_remainder width c qs hqs
  have hz (z : RatPoly) : cur z + 48*sq z ≈ 20*grad z + rem z := by
    let ww := polyMul (b z) (b z)
    have hsq := haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_four_swap (b z) f (b z) f)
    have ha := YMGap.Continuum.QuaternionHaarFamilySquare.haar_weighted_add
    have hl := Q'.eqv_trans _ _ _ (ha (N width) ww cg (polySmul 48 (polyMul f f)))
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) 48 ww (polyMul f f))
          (Q'.mul_eqv_congr_left 48 _ _ (Q'.eqv_symm hsq))))
    have hr := Q'.eqv_trans _ _ _ (ha (N width) ww (polySmul 20 g) r)
      (Q'.add_eqv_congr' (quaternionHaar_polyMul_smul_right (N width) 20 ww g)
        (Q'.eqv_refl _))
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl) (Q'.eqv_trans _ _ _ (hF ww) hr)
  change channelSum cs cur + 48*channelSum cs sq ≈ 20*channelSum cs grad + channelSum cs rem
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (channelSum_smul sq 48 cs)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (channelSum_add cur (fun z => 48*sq z) cs))
      (Q'.eqv_trans _ _ _ (channelSum_congr _ _ cs (fun z _ => hz z.2))
        (Q'.eqv_trans _ _ _ (channelSum_add (fun z => 20*grad z) rem cs)
          (Q'.add_eqv_congr' (channelSum_smul grad 20 cs) (Q'.eqv_refl _)))))

private theorem channelSum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) → (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (channelSum_nonnegative value cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

/-- Positivity applies to the assembled diagonal Gamma, not its mixed terms. -/
theorem familyChannelGradient_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ familyChannelGradient w K width depth c qs := by
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  change (0 : Q') ≤ channelSum (productChannels (N width) w K ids) (fun z =>
    let b := channelSource ids q z
    H (N width) (polyMul (polyMul b b) (activeGamma (List.range (N width)) f f)))
  apply channelSum_nonnegative
  · exact productChannels_nonnegative (N width) hw0 K ids
  · intro z hz
    have hb := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz
    exact (Certificate.multiplySquare _ hb
      (activeGamma_squareCertificate (List.range (N width))
        (fun j hj => List.mem_range.mp hj) (spatialSpan_supported width c qs))).haar_nonnegative

/-- Correct-direction lower bound for the quantity SUBTRACTED in the actual
retained-square estimate. The signed remainder itself has no sign assertion. -/
theorem familyChannelPairRemainder_le_curvature_square {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    familyChannelPairRemainder w K width depth c qs ≤
      familyChannelCurvature w K width depth c qs +
        48*familyChannelObservableSquare w K width depth c qs := by
  let r := familyChannelPairRemainder w K width depth c qs
  let g := familyChannelGradient w K width depth c qs
  have hg : (0 : Q') ≤ 20*g := Q'.mul_nonneg _ _ (by decide)
    (familyChannelGradient_nonnegative hw0 K width depth c qs)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg r (20*g) hg)
      (Q'.le_of_eqv (Q'.add_comm_eqv r (20*g))))
    (Q'.ge_of_eqv (familyChannel_curvature_remainder w K width depth c qs hqs))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.pairRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.pair_curvature_remainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyPairRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.family_curvature_remainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyChannelGradient
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyChannelPairRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyChannel_curvature_remainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyChannelGradient_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature.familyChannelPairRemainder_le_curvature_square
