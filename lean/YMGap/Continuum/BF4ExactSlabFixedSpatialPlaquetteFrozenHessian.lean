/-
# Frozen paired Hessian of the literal original spatial plaquette

The selected physical link occurs once. Its scalar word is head-linear in
an explicit reversible chart, so the paired diagonal jets are minus the
same scalar and the symmetrized mixed jets vanish. All nine actual ordered
jets are retained before multiplying arbitrary frozen coefficients.

Every identity holds with arbitrary original Haar insertions. This is not
a heat-curvature certificate, an interacting variance or a scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionPairedFrameAt
import YMGap.Continuum.QuaternionHaarPairedLinearHessian
import YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion exposedFourWord exposedFourWord_scalar_blockDegree)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum)
open YMGap.Continuum.QuaternionHaarMixedAngularTransport (chain_carrier)
open YMGap.Continuum.QuaternionHaarAngularCarrier (carrierOfPrefix)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.QuaternionHaarPairedLinearHessian
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

/-- Actual ordered second jets at the specified original block. -/
def frozenSecondAt (block : Nat) (u : Fin 3 → RatPoly) (p : RatPoly) : RatPoly :=
  quadraticForm u (fun i j => pairedDerivativeAt block i (pairedDerivativeAt block j p))

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem word_scalar_supported {blocks : Nat} (a b c d : Fin blocks)
    (r0 r1 r2 r3 : Bool) :
    SupportedQuaternionBlocks blocks (word a.val b.val c.val d.val r0 r1 r2 r3).scalar := by
  have ho (x : Fin blocks) (r : Bool) : Supported blocks (orientedCoordinateQuaternion x.val r) := by
    cases r
    · exact Supported.coordinate x.isLt
    · exact (Supported.coordinate x.isLt).conj
  exact (((ho a r0).mul (ho b r1)).mul (ho c r2) |>.mul (ho d r3)).scalar

private theorem second_carrier {blocks block : Nat} (hb : block < blocks)
    (i j : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks
      (pairedDerivativeAt block i (pairedDerivativeAt block j p))
      (pairedDerivativeAt block i (pairedDerivativeAt block j q)) :=
  pairedDerivativeAt_carrier hb i (pairedDerivativeAt_supported hb j hp)
    (pairedDerivativeAt_supported hb j hq) (pairedDerivativeAt_carrier hb j hp hq h)

private theorem reflect_chain {blocks : Nat}
    (ss : List (QuaternionBlockInvolution blocks)) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain ss p)
      (applyQuaternionBlockSwapChain ss q)) : HaarCarrierEqv blocks p q := by
  have hr := chain_carrier ss.reverse
    (applyQuaternionBlockSwapChain_supported ss p hp)
    (applyQuaternionBlockSwapChain_supported ss q hq) h
  have hi (t : RatPoly) (ht : SupportedQuaternionBlocks blocks t) : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain ss.reverse (applyQuaternionBlockSwapChain ss t)) t :=
    carrierOfPrefix
      (applyQuaternionBlockSwapChain_supported ss.reverse _
        (applyQuaternionBlockSwapChain_supported ss t ht)) ht
      (reverse_apply_inverse_prefix ss t)
  exact (hi p hp).symm.trans (hr.trans (hi q hq))

private theorem chain_zero {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks)) :
    applyQuaternionBlockSwapChain ss polyZero = polyZero := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simpa only [applyQuaternionBlockSwapChain] using ih

/-- Both orders of every mixed entry survive the original word chart.
The exposure is actual finite data, not a changed carrier or action. -/
theorem oriented_fourWord_first_paired_hessian_jets {blocks : Nat} (hb : 3 < blocks)
    (a b c d : Fin blocks) (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool) :
    let f := (word a.val b.val c.val d.val r0 r1 r2 r3).scalar
    (∀ i, HaarCarrierEqv blocks
      (pairedDerivativeAt a.val i (pairedDerivativeAt a.val i f)) (polyNeg f)) ∧
    (∀ i j, i ≠ j → HaarCarrierEqv blocks
      (polyAdd (pairedDerivativeAt a.val i (pairedDerivativeAt a.val j f))
        (pairedDerivativeAt a.val j (pairedDerivativeAt a.val i f))) polyZero) := by
  dsimp only
  let f := (word a.val b.val c.val d.val r0 r1 r2 r3).scalar
  let g := applyQuaternionBlockSwapChain e.steps f
  let canonical := (exposedFourWord r0 r1 r2 r3).scalar
  have hf := word_scalar_supported a b c d r0 r1 r2 r3
  have hg := applyQuaternionBlockSwapChain_supported e.steps f hf
  have hc : SupportedQuaternionBlocks blocks canonical := by
    exact word_scalar_supported ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨2,by omega⟩ ⟨3,hb⟩ r0 r1 r2 r3
  have hgc : HaarCarrierEqv blocks g canonical := by
    apply carrierOfPrefix hg hc
    have h := (word_prefix hb e r0 r1 r2 r3).scalar
    rw [applyQuaternionBlockSwapChainQuaternion_scalar] at h
    exact h
  have hd := exposedFourWord_scalar_blockDegree r0 r1 r2 r3 0 (by decide)
  have htrans (i j : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative j g))
      (applyQuaternionBlockSwapChain e.steps
        (pairedDerivativeAt a.val i (pairedDerivativeAt a.val j f))) := by
    have h := chain_pairedSecondAt e.steps (by omega : 0 < blocks) i j f hf
    simpa only [e.source_zero, pairedDerivativeAt_zero] using h
  have hjet (i j : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative j g))
      (pairedDerivative i (pairedDerivative j canonical)) := by
    simpa only [pairedDerivativeAt_zero] using second_carrier (by omega : 0 < blocks) i j hg hc hgc
  constructor
  · intro i
    have hi := (hjet i i).trans
      ((paired_linear_diagonal (by omega : 0 < blocks) canonical hd i).trans
        (HaarCarrierEqv.neg hgc.symm))
    have hchain : HaarCarrierEqv blocks
        (applyQuaternionBlockSwapChain e.steps (pairedDerivativeAt a.val i (pairedDerivativeAt a.val i f)))
        (applyQuaternionBlockSwapChain e.steps (polyNeg f)) := by
      rw [chain_neg]
      exact (htrans i i).symm.trans hi
    exact reflect_chain e.steps (pairedDerivativeAt_supported a.isLt i
      (pairedDerivativeAt_supported a.isLt i hf)) (neg_supported hf) hchain
  · intro i j hij
    have hijg := (HaarCarrierEqv.add (hjet i j) (hjet j i)).trans
      (paired_linear_mixed (by omega : 0 < blocks) canonical hd i j hij)
    have hchain : HaarCarrierEqv blocks
        (applyQuaternionBlockSwapChain e.steps
          (polyAdd (pairedDerivativeAt a.val i (pairedDerivativeAt a.val j f))
            (pairedDerivativeAt a.val j (pairedDerivativeAt a.val i f))))
        (applyQuaternionBlockSwapChain e.steps polyZero) := by
      rw [chain_add, chain_zero]
      exact (HaarCarrierEqv.add (htrans i j) (htrans j i)).symm.trans hijg
    exact reflect_chain e.steps
      (supported_add (pairedDerivativeAt_supported a.isLt i (pairedDerivativeAt_supported a.isLt j hf))
        (pairedDerivativeAt_supported a.isLt j (pairedDerivativeAt_supported a.isLt i hf)))
      (by intro t ht; exact False.elim (List.not_mem_nil ht)) hchain

private theorem paired_congr (block : Nat) (i : Fin 3) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (pairedDerivativeAt block i p) (pairedDerivativeAt block i q) := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by simp only [Fin.ext_iff]; omega
  rcases hc with rfl | rfl | rfl
  · exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)
  · exact (angularDerivative_congr _ _ h).add (RatPolyCoeffEqv.neg (angularDerivative_congr _ _ h))
  · exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)

private theorem frozen_congr (block : Nat) (u : Fin 3 → RatPoly) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (frozenSecondAt block u p) (frozenSecondAt block u q) := by
  have hjet (i j : Fin 3) := (paired_congr block i (paired_congr block j h)).mul_left (polyMul (u i) (u j))
  exact (hjet 0 0).add ((hjet 0 1).add (hjet 0 2)) |>.add
    (((hjet 1 0).add ((hjet 1 1).add (hjet 1 2))).add
      ((hjet 2 0).add ((hjet 2 1).add (hjet 2 2))))

private theorem frozen_transport (block : Nat) (u : Fin 3 → RatPoly) {blocks : Nat} {p q : RatPoly}
    (h : RatPolyCoeffEqv p q)
    (hq : HaarCarrierEqv blocks (frozenSecondAt block u q) (polyNeg (polyMul (threeSquare u) q))) :
    HaarCarrierEqv blocks (frozenSecondAt block u p) (polyNeg (polyMul (threeSquare u) p)) :=
  (RatPolyCoeffEqv.haarCarrier (frozen_congr block u h)).trans
    (hq.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.neg (h.symm.mul_left (threeSquare u)))))

/-- Arbitrary frozen coefficients are multiplied only AFTER all actual jets. -/
theorem oriented_fourWord_first_frozen_hessian {blocks : Nat} (hb : 3 < blocks)
    (a b c d : Fin blocks) (e : FourBlockExposure a b c d) (r0 r1 r2 r3 : Bool)
    (u : Fin 3 → RatPoly) :
    let f := (word a.val b.val c.val d.val r0 r1 r2 r3).scalar
    HaarCarrierEqv blocks (frozenSecondAt a.val u f) (polyNeg (polyMul (threeSquare u) f)) := by
  dsimp only
  unfold frozenSecondAt quadraticForm
  have h := oriented_fourWord_first_paired_hessian_jets hb a b c d e r0 r1 r2 r3
  exact frozen_hessian_of_diagonal_mixed (blocks := blocks)
    (word a.val b.val c.val d.val r0 r1 r2 r3).scalar u
    (fun i j => pairedDerivativeAt a.val i
      (pairedDerivativeAt a.val j (word a.val b.val c.val d.val r0 r1 r2 r3).scalar)) h.1 h.2

/-- Cyclicity, not commutativity, puts any selected original link first. -/
theorem oriented_fourWord_any_slot_frozen_hessian {blocks : Nat} (hb : 3 < blocks)
    (a b c d : Fin blocks)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (r0 r1 r2 r3 : Bool) (slot : Nat)
    (hm : slot=a.val ∨ slot=b.val ∨ slot=c.val ∨ slot=d.val) (u : Fin 3 → RatPoly) :
    let f := (word a.val b.val c.val d.val r0 r1 r2 r3).scalar
    HaarCarrierEqv blocks (frozenSecondAt slot u f) (polyNeg (polyMul (threeSquare u) f)) := by
  dsimp only
  rcases hm with rfl | rfl | rfl | rfl
  · exact oriented_fourWord_first_frozen_hessian hb a b c d
      (fourBlockExposure hb a b c d hab hac had hbc hbd hcd) r0 r1 r2 r3 u
  · exact frozen_transport b.val u (word_cyclic _ _ _ _ r0 r1 r2 r3)
      (oriented_fourWord_first_frozen_hessian hb b c d a
        (fourBlockExposure hb b c d a hbc hbd (Ne.symm hab) hcd (Ne.symm hac) (Ne.symm had)) r1 r2 r3 r0 u)
  · exact frozen_transport c.val u ((word_cyclic _ _ _ _ r0 r1 r2 r3).trans
      (word_cyclic _ _ _ _ r1 r2 r3 r0))
      (oriented_fourWord_first_frozen_hessian hb c d a b
        (fourBlockExposure hb c d a b hcd (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd) hab) r2 r3 r0 r1 u)
  · exact frozen_transport d.val u (((word_cyclic _ _ _ _ r0 r1 r2 r3).trans
      (word_cyclic _ _ _ _ r1 r2 r3 r0)).trans (word_cyclic _ _ _ _ r2 r3 r0 r1))
      (oriented_fourWord_first_frozen_hessian hb d a b c
        (fourBlockExposure hb d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc) r3 r0 r1 r2 u)

/-- Literal spatial face and literal selected physical link, with every
original insertion retained. No heat cutoff, coupling or volume restriction. -/
theorem plaquette_frozen_hessian {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (u : Fin 3 → RatPoly) :
    HaarCarrierEqv (N width)
      (frozenSecondAt ((baseLinks width).idxOf l) u (plaquette width face).scalar)
      (polyNeg (polyMul (threeSquare u) (plaquette width face).scalar)) := by
  let a : Z4Link := (face.1, (dirsOf face.2).1)
  let b : Z4Link := (face.1, (dirsOf face.2).2)
  let c : Z4Link := (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let d : Z4Link := (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  have ha : a ∈ baseLinks width := face_link_mem_base hf (by simp [a, edgesOf])
  have hb : b ∈ baseLinks width := face_link_mem_base hf (by simp [b, edgesOf])
  have hc : c ∈ baseLinks width := face_link_mem_base hf (by simp [c, edgesOf])
  have hd : d ∈ baseLinks width := face_link_mem_base hf (by simp [d, edgesOf])
  have hn : (a ≠ b ∧ (a ≠ c ∧ a ≠ d)) ∧ ((b ≠ c ∧ b ≠ d) ∧ c ≠ d) := by
    simpa only [edgesOf, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, or_false, not_or, not_false_eq_true, and_true] using edgesOf_nodup face
  have hne {x y : Z4Link} (hx : x ∈ baseLinks width) (hy : y ∈ baseLinks width) (hxy : x ≠ y) :
      (baseLinks width).idxOf x ≠ (baseLinks width).idxOf y :=
    fun he => hxy (idxOf_injective_on_members hx hy he)
  have had := hne ha hd hn.1.2.2
  have hac := hne ha hc hn.1.2.1
  have hab := hne ha hb hn.1.1
  have hdc := hne hd hc (Ne.symm hn.2.2)
  have hdb := hne hd hb (Ne.symm hn.2.1.2)
  have hcb := hne hc hb (Ne.symm hn.2.1.1)
  have hai := List.idxOf_lt_length_of_mem ha
  have hbi := List.idxOf_lt_length_of_mem hb
  have hci := List.idxOf_lt_length_of_mem hc
  have hdi := List.idxOf_lt_length_of_mem hd
  have hsize : 3 < N width := by omega
  have hm : (baseLinks width).idxOf l = (baseLinks width).idxOf a ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf d ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf c ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf b := by
    have he : l=a ∨ l=b ∨ l=c ∨ l=d := by
      simpa only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] using hl
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  exact frozen_transport _ u (plaquette_fourWord hf).scalar
    (oriented_fourWord_any_slot_frozen_hessian hsize ⟨_,hai⟩ ⟨_,hdi⟩ ⟨_,hci⟩ ⟨_,hbi⟩
      had hac hab hdc hdb hcb false false true true _ hm u)

#print axioms oriented_fourWord_first_paired_hessian_jets
#print axioms oriented_fourWord_first_frozen_hessian
#print axioms oriented_fourWord_any_slot_frozen_hessian
#print axioms plaquette_frozen_hessian

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian
