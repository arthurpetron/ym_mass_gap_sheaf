/-
# A literal inactive face collapses to the unobserved first-transfer message

An original spatial face with an inactive link has a link unique in the
complete spatial face list. Exact spin-one heat selection at that link,
with all other action factors retained, gives
  H[s*T(g_n*chi_p)] = coeffW(w,1)*H[s*Tg_n].
The test s is arbitrary and supported. The equality is Haar-tested, NOT
free-polynomial equality. No positivity, reciprocal or gap is assumed.

This removes the centered inactive-face contribution from the actual first
message pair. Fully active faces, already a cubical core at width two,
remain interacting. No bulk contraction or continuum closure is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (heatFace_haar_remove)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment (heatFace_character_moment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (terminal_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer (kineticMap_symmetric)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_supported productMap_independent_of_not_mem)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks

private theorem move_probe (a b c q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) (polyMul c q))
      (polyMul a (polyMul c (polyMul b q))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => q)

private theorem move_head (a b q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) q) (polyMul b (polyMul a q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => a | 1 => b | _ => q)

private theorem selected_moment (w : Q') (K : Nat) (hK : 1 ≤ K)
    {width : Nat} {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    (leaf : FringeFaceLeaf width face) :
    ∀ (faces : List Z4Plaq), (∀ p, p ∈ faces → p ∈ spatialFaces width) →
      faces.Nodup → face ∈ faces → ∀ q : RatPoly,
      SupportedQuaternionBlocks (N width) q →
      QuaternionBlockIndependent ((baseLinks width).idxOf leaf.link) q →
    quaternionHaar (N width)
      (polyMul (polynomialProduct (fun p => heatPrefix w K (plaquette width p).scalar) faces)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)) ≈
      coeffW w 1 * quaternionHaar (N width)
        (polyMul (polynomialProduct (fun p => heatPrefix w K (plaquette width p).scalar) faces) q)
  | [], _, _, hm, _, _, _ => False.elim (List.not_mem_nil hm)
  | p::ps, hps, hn, hm, q, hq, hi => by
      let H := heatPrefix w K (plaquette width p).scalar
      let R := polynomialProduct (fun p => heatPrefix w K (plaquette width p).scalar) ps
      let chi := characterPolynomial (plaquette width face).scalar 1
      have ht := fun a ha => hps a (List.mem_cons_of_mem p ha)
      have hnd := (List.nodup_cons.mp hn).2
      by_cases he : p = face
      · subst p
        have hnot : ∀ a, a ∈ ps → leaf.link ∉ edgesOf a := by
          intro a ha hl
          have hae := leaf.unique a (ht a ha) hl
          exact (List.nodup_cons.mp hn).1 (hae ▸ ha)
        have hR := heatProduct_supported w K width ps
        have hRi := heatProduct_independent w K leaf.in_carrier ps hnot
        have hmoment := heatFace_character_moment w K hK hf leaf.link leaf.on_face
          (polyMul R q) (supported_polyMul hR hq) (quaternionBlockIndependent_polyMul hRi hi)
        have hremove := heatFace_haar_remove w K hf leaf.link leaf.on_face
          (polyMul R q) (supported_polyMul hR hq) (quaternionBlockIndependent_polyMul hRi hi)
        have hmass : quaternionHaar (N width) (polyMul (polyMul H R) q) ≈
            quaternionHaar (N width) (polyMul R q) :=
          Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc H R q)) hremove
        exact Q'.eqv_trans _ _ _ (haar_of_coeff (move_probe H R chi q))
          (Q'.eqv_trans _ _ _ hmoment (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hmass)))
      · have hm' : face ∈ ps := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
        have hnot : leaf.link ∉ edgesOf p := fun hl => he (leaf.unique p (hps p List.mem_cons_self) hl)
        have hHi := heatFace_independent w K leaf.in_carrier hnot
        have hQ := supported_polyMul (heatFace_supported w K width p) hq
        have hfirst : RatPolyCoeffEqv (polyMul (polyMul H R) (polyMul chi q))
            (polyMul R (polyMul chi (polyMul H q))) :=
          (move_head H R (polyMul chi q)).trans
            (((RatPolyCoeffEqv.mul_assoc H chi q).symm.trans
              (((RatPolyCoeffEqv.mul_comm H chi).mul_right q).trans
                (RatPolyCoeffEqv.mul_assoc chi H q))).mul_left R)
        exact Q'.eqv_trans _ _ _ (haar_of_coeff hfirst)
          (Q'.eqv_trans _ _ _
            (selected_moment w K hK hf leaf ps ht hnd hm' (polyMul H q) hQ
              (quaternionBlockIndependent_polyMul hHi hi))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haar_of_coeff (move_head H R q)))))

/-- Full spatial action, with only independence of the one actual free leaf.
The other three face links and all their interactions remain in q. -/
theorem spatial_fringe_face_moment (w : Q') (K : Nat) (hK : 1 ≤ K)
    {width : Nat} {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    (leaf : FringeFaceLeaf width face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf leaf.link) q) :
    quaternionHaar (N width)
      (polyMul (spatialWeight w K width)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)) ≈
      coeffW w 1 * quaternionHaar (N width) (polyMul (spatialWeight w K width) q) := by
  unfold spatialWeight
  exact selected_moment w K hK hf leaf (spatialFaces width) (fun _ h => h)
    (spatialFaces_nodup width) hf q hq hi

private theorem transfer_product (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) f) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- The actual observed/unobserved pair collapses under every supported test.
This conclusion is tested Haar equality, not coefficient equality. -/
theorem inactive_fundamental_transfer_pair (w : Q') (K width n : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (s : RatPoly) (hs : SupportedQuaternionBlocks (N width) s) :
    quaternionHaar (N width)
      (polyMul s (transferStep w K width
        (polyMul (terminalMessage w K width n) (characterPolynomial (plaquette width face).scalar 1)))) ≈
      coeffW w 1 * quaternionHaar (N width)
        (polyMul s (transferStep w K width (terminalMessage w K width n))) := by
  let leaf := fringeFaceLeaf width face hf ha
  let g := terminalMessage w K width n
  let chi := characterPolynomial (plaquette width face).scalar 1
  let P := productMap (N width) w K (activeBlocks width) s
  have hg := terminalMessage_supported w K width n
  have hc := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hP := productMap_supported (N width) w K (activeBlocks width) (activeBlocks_lt width) hs
  have hPi := productMap_independent_of_not_mem (N width) w K (activeBlocks width)
    (activeBlocks_lt width) _ (List.idxOf_lt_length_of_mem leaf.in_carrier) leaf.inactive s hs
  have hgi := terminal_fringe_independent w K width n _ leaf.fringe
  have hm := spatial_fringe_face_moment w K hK hf leaf (polyMul g P)
    (supported_polyMul hg hP) (quaternionBlockIndependent_polyMul hgi hPi)
  have hl : RatPolyCoeffEqv (polyMul (polyMul (spatialWeight w K width) (polyMul g chi)) P)
      (polyMul (spatialWeight w K width) (polyMul chi (polyMul g P))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
      (by decide) (fun | 0 => spatialWeight w K width | 1 => g | 2 => chi | _ => P)
  rw [transfer_product, transfer_product]
  exact Q'.eqv_trans _ _ _
    (kineticMap_symmetric w K width (supported_polyMul (spatialWeight_supported w K width)
      (supported_polyMul hg hc)) hs)
    (Q'.eqv_trans _ _ _ (haar_of_coeff hl)
      (Q'.eqv_trans _ _ _ hm
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
            (Q'.eqv_symm (kineticMap_symmetric w K width
              (supported_polyMul (spatialWeight_supported w K width) hg) hs))))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer.spatial_fringe_face_moment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer.inactive_fundamental_transfer_pair
