/-
# Local moments factor against the SAME full spectator OS background

Every channel in every unselected original interface face avoids the four
probe links, at every representation degree. The detached lower heat
product also avoids those links. Haar factorization therefore acts inside
each original channel before the full spectator tree is summed.

The resulting reflected pairing is Haar(p)*Haar(q)*Zsp. No spectator
partition is replaced by a bare Haar reference or by the unit channel.
The removed local lower collar is NOT reinstated in this reference identity.
-/

import YMGap.Continuum.ReflectedSquareTreeBlockLocality
import YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes

namespace YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ReflectedSquareTreeBlockLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def OutsideProbe (half block : Nat) : Prop :=
  correctedSlabLinkAt (centralExtent half) block ∉ probeLinks half

theorem link_gram_outside {half : Nat} {link : Z4Link}
    (hp : link ∈ boundaryCompleteSlabLinks (centralExtent half)) (hn : link ∉ probeLinks half) (n : Nat) :
    TreeLocal (blocks half) (OutsideProbe half)
      (gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) link)) n) := by
  have hc (c : Nat) (h : c < 4) : BlockLocal (blocks half) (OutsideProbe half)
      (polyVar (4*(boundaryCompleteSlabLinks (centralExtent half)).idxOf link+c)) := by
    apply BlockLocal.coordinate
    unfold OutsideProbe
    rw [show (4*(boundaryCompleteSlabLinks (centralExtent half)).idxOf link+c)/4 =
      (boundaryCompleteSlabLinks (centralExtent half)).idxOf link by omega, correctedSlabLinkAt_idxOf hp]
    exact hn
  rw [correctedSlabLinkPolynomial_of_mem hp]
  exact gram_local _ (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega)) n

private theorem expansionSum_local {A : Type} {half : Nat} {allowed : Nat → Prop} (f : A → RatPoly) :
    (ids : List A) → (E : ∀ a, a ∈ ids → LocalSquareExpansion half (f a)) →
    (∀ a (ha : a ∈ ids), TreeLocal (blocks half) allowed (E a ha).tree) →
      TreeLocal (blocks half) allowed (LocalSquareExpansion.finiteSum f ids E).tree
  | [], _, _ => True.intro
  | a :: ids, E, h => ⟨h a List.mem_cons_self,
      expansionSum_local f ids (fun b hb => E b (List.mem_cons_of_mem a hb))
        (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

private theorem expansionProduct_local {A : Type} {half : Nat} {allowed : Nat → Prop} (f : A → RatPoly) :
    (ids : List A) → (E : ∀ a, a ∈ ids → LocalSquareExpansion half (f a)) →
    (∀ a (ha : a ∈ ids), TreeLocal (blocks half) allowed (E a ha).tree) →
      TreeLocal (blocks half) allowed (LocalSquareExpansion.finiteProduct f ids E).tree
  | [], _, _ => BlockLocal.one _ _
  | a :: ids, E, h => (h a List.mem_cons_self).product
      (expansionProduct_local f ids (fun b hb => E b (List.mem_cons_of_mem a hb))
        (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem spectatorFace_outside {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ spectatorIds half) :
    TreeLocal (blocks half) (OutsideProbe half) (faceExpansion hw K (spectatorIds_fixed hi)).tree :=
  expansionSum_local _ _ _ (fun _ _ =>
    (link_gram_outside (faceLinkA_physical (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp (spectatorIds_fixed hi)).1))
      (spectator_exposed_not_mem (spectatorIds_fixed hi) (spectatorIds_unselected hi)) _).scale _)

theorem spectatorTree_outside {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    TreeLocal (blocks half) (OutsideProbe half) (spectatorExpansion hw K half).tree :=
  expansionProduct_local _ _ _ (fun _ hi => spectatorFace_outside hw K hi)

theorem spectatorHeat_outside (w : Q') (K half : Nat) :
    BlockLocal (blocks half) (OutsideProbe half) (spectatorHeat w K half) := by
  intro t ht block hb hn
  apply spectatorHeat_local w K half t ht block hb
  intro hm
  exact hn (fun hp => lowerSpectators_disjoint half _ hp hm)

theorem probe_factor {half : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hl : LinkLocal (centralExtent half) (probeLinks half) p) (hr : BlockLocal (blocks half) (OutsideProbe half) q) :
    quaternionHaar (blocks half) (polyMul p q) ≈ quaternionHaar (blocks half) p * quaternionHaar (blocks half) q := by
  apply haar_product hp hq
  intro s hs t ht block hb
  by_cases h : correctedSlabLinkAt (centralExtent half) block ∈ probeLinks half
  · exact Or.inr (hr t ht block hb (fun hn => hn h))
  · exact Or.inl (hl s hs block hb h)

theorem channel_factor {half : Nat} (w : Q') (K : Nat) {p c : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hc : SupportedQuaternionBlocks (blocks half) c)
    (hl : LinkLocal (centralExtent half) (probeLinks half) p) (hr : BlockLocal (blocks half) (OutsideProbe half) c) :
    quaternionHaar (blocks half) (polyMul (polyMul p (spectatorHeat w K half)) c) ≈
      quaternionHaar (blocks half) p * quaternionHaar (blocks half) (polyMul (spectatorHeat w K half) c) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (RatPolyCoeffEqv.mul_assoc _ _ _))
    (probe_factor hp (supported_polyMul (spectatorHeat_supported w K half) hc) hl ((spectatorHeat_outside w K half).mul hr))

private theorem factor_term (a b x weight : Q') : weight*((a*x)*(b*x)) ≈ (a*b)*(weight*(x*x)) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.var 3) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.mul (.var 2) (.var 2)))) (by decide)
    (fun | 0 => a | 1 => b | 2 => x | _ => weight)

/-- The full tree sum survives as one common factor; no sign assumption is needed. -/
theorem tree_pair_factor (w : Q') (K half : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LinkLocal (centralExtent half) (probeLinks half) p) (hlq : LinkLocal (centralExtent half) (probeLinks half) q) :
    ∀ t : SquareTree, SquareTreeSupported (blocks half) t → TreeLocal (blocks half) (OutsideProbe half) t →
    channelBilinearValue (blocks half) (polyMul p (spectatorHeat w K half)) (polyMul q (spectatorHeat w K half)) t ≈
      (quaternionHaar (blocks half) p * quaternionHaar (blocks half) q) *
        channelBilinearValue (blocks half) (spectatorHeat w K half) (spectatorHeat w K half) t
  | .zero, _, _ => Q'.eqv_symm (QPoly.q_mul_zero _)
  | .term weight _, hc, hr => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (channel_factor w K hp hc hlp hr))
        (Q'.mul_eqv_congr_left _ _ _ (channel_factor w K hq hc hlq hr))))
      (factor_term _ _ _ weight)
  | .add s t, hst, hrt => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (tree_pair_factor w K half hp hq hlp hlq s hst.1 hrt.1)
        (tree_pair_factor w K half hp hq hlp hlq t hst.2 hrt.2))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

/-- The reference on the SAME full spectator OS law, not the bare Lfar^2 law. -/
theorem detached_pair_factor {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LinkLocal (centralExtent half) (probeLinks half) p) (hlq : LinkLocal (centralExtent half) (probeLinks half) q) :
    spectatorPair w K half (polyMul p (spectatorHeat w K half)) (polyMul q (spectatorHeat w K half)) ≈
      (quaternionHaar (blocks half) p * quaternionHaar (blocks half) q) * backgroundMass w K half := by
  have hlp' := linkLocal_lower hlp (fun _ hi => lower_face_link (probeFace_lower half) hi)
  have hlq' := linkLocal_lower hlq (fun _ hi => lower_face_link (probeFace_lower half) hi)
  have hL := spectatorHeat_supported w K half
  have hlL := spectatorHeat_lower w K half
  exact Q'.eqv_trans _ _ _
    (expansion_mixed_pairing (spectatorExpansion hw K half) _ _ (supported_polyMul hp hL) (supported_polyMul hq hL)
      (hlp'.mul hlL) (hlq'.mul hlL))
    (Q'.eqv_trans _ _ _
      (tree_pair_factor w K half hp hq hlp hlq _ (spectatorExpansion hw K half).treeSupported
        (spectatorTree_outside hw K half))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm
        (expansion_mixed_pairing (spectatorExpansion hw K half) _ _ hL hL hlL hlL))))

end YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.link_gram_outside
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.spectatorFace_outside
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.spectatorTree_outside
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.spectatorHeat_outside
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.probe_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.channel_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.tree_pair_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization.detached_pair_factor
