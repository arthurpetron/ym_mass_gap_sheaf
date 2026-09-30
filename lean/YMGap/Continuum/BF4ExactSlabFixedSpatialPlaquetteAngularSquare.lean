/-
# Angular square of an arbitrary actual four-link plaquette

The exposed fundamental identity is transported through finite block swaps
at the full Haar-carrier level, so every original insertion survives. The
generic oriented-word theorem also applies to the corrected full-slab face;
the final spatial specialization uses its literal face word.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
import YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.SU2QuaternionReplicaPairBounds
import YMGap.Continuum.SU2QuaternionBlockSwapChainInverse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (exposedFourWord)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (reindex_cap_carrier)
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_cap (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem support_gap {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyAdd (cap 4) (polyNeg (polyMul p p))) :=
  supported_add (support_cap n 4) (support_neg (supported_polyMul hp hp))

private theorem six_prefix {blocks : Nat} {left right : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 →
      QuaternionPrefixPolynomialEqv blocks (left i j) (right i j)) :
    QuaternionPrefixPolynomialEqv blocks (six left) (six right) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).append
    ((h 0 2 (by decide) (by decide)).append
      ((h 0 3 (by decide) (by decide)).append
        ((h 1 2 (by decide) (by decide)).append
          ((h 1 3 (by decide) (by decide)).append
            (h 2 3 (by decide) (by decide))))))

/-- A block swap transports angular square under every retained insertion. -/
theorem reindex_blockAngularSquare_carrier {blocks block : Nat}
    (s : QuaternionBlockInvolution blocks) (hblock : block < blocks)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s (blockAngularSquare (s.map block) p))
      (blockAngularSquare block (reindexQuaternionPolynomial s p)) := by
  have hprefix : QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (blockAngularSquare (s.map block) p))
      (blockAngularSquare block (reindexQuaternionPolynomial s p)) := by
    simpa only [blockAngularSquare, blockAngularDerivative, six,
      reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul] using
      (six_prefix (fun i j hi hj =>
        (reindex_blockAngularDerivative_prefix s hblock hi hj p).mul
          (reindex_blockAngularDerivative_prefix s hblock hi hj p)))
  exact carrierOfPrefix
    (reindex_supported s (blockAngularSquare (s.map block) p))
    (blockAngularSquare_supported hblock (reindex_supported s p)) hprefix

private theorem chain_carrier {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly},
      SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks q →
      HaarCarrierEqv blocks p q →
      HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q)
  | [], _, _, _, _, h => h
  | s::steps, p, q, hp, hq, h =>
      chain_carrier steps (reindex_supported s p) (reindex_supported s q)
        (reindex_carrier s hp hq h)

private theorem reflect_chain_carrier {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
      (applyQuaternionBlockSwapChain steps q)) : HaarCarrierEqv blocks p q := by
  have hr := chain_carrier steps.reverse
    (applyQuaternionBlockSwapChain_supported steps p hp)
    (applyQuaternionBlockSwapChain_supported steps q hq) h
  have hpInv : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps p)) p := by
    apply carrierOfPrefix
    · exact applyQuaternionBlockSwapChain_supported steps.reverse _
        (applyQuaternionBlockSwapChain_supported steps p hp)
    · exact hp
    · exact reverse_apply_inverse_prefix steps p
  have hqInv : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps q)) q := by
    apply carrierOfPrefix
    · exact applyQuaternionBlockSwapChain_supported steps.reverse _
        (applyQuaternionBlockSwapChain_supported steps q hq)
    · exact hq
    · exact reverse_apply_inverse_prefix steps q
  exact hpInv.symm.trans (hr.trans hqInv)

/-- The source-block angular square is transported by an arbitrary explicit
swap chain, with every spectator insertion retained. -/
theorem chain_blockAngularSquare_carrier {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) (block : Nat),
      block < blocks → ∀ (p : RatPoly), SupportedQuaternionBlocks blocks p →
      HaarCarrierEqv blocks
        (blockAngularSquare block (applyQuaternionBlockSwapChain steps p))
        (applyQuaternionBlockSwapChain steps
          (blockAngularSquare (quaternionBlockSwapChainSource steps block) p))
  | [], block, _, p, _ => HaarCarrierEqv.refl blocks _
  | s::rest, block, hblock, p, hp => by
      let q := reindexQuaternionPolynomial s p
      have hsource : quaternionBlockSwapChainSource rest block < blocks :=
        quaternionBlockSwapChainSource_lt rest hblock
      have hq : SupportedQuaternionBlocks blocks q := reindex_supported s p
      have hr := chain_blockAngularSquare_carrier rest block hblock q hq
      have hs := (reindex_blockAngularSquare_carrier s hsource p hp).symm
      have ht := chain_carrier rest
        (blockAngularSquare_supported hsource hq)
        (reindex_supported s
          (blockAngularSquare (s.map (quaternionBlockSwapChainSource rest block)) p)) hs
      exact hr.trans ht

private theorem angularSquare_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularSquare p) (angularSquare q) := by
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :=
    angularDerivative_carrier hb hi hj h
  exact HaarCarrierEqv.add
    (HaarCarrierEqv.mul (hd 0 1 (by decide) (by decide)) (hd 0 1 (by decide) (by decide)))
    (HaarCarrierEqv.add
      (HaarCarrierEqv.mul (hd 0 2 (by decide) (by decide)) (hd 0 2 (by decide) (by decide)))
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul (hd 0 3 (by decide) (by decide)) (hd 0 3 (by decide) (by decide)))
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul (hd 1 2 (by decide) (by decide)) (hd 1 2 (by decide) (by decide)))
          (HaarCarrierEqv.add
            (HaarCarrierEqv.mul (hd 1 3 (by decide) (by decide)) (hd 1 3 (by decide) (by decide)))
            (HaarCarrierEqv.mul (hd 2 3 (by decide) (by decide))
              (hd 2 3 (by decide) (by decide)))))))

private theorem chain_add {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s rest ih => simp only [applyQuaternionBlockSwapChain,
      reindexQuaternionPolynomial_add, ih]

private theorem chain_neg {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyNeg p) =
      polyNeg (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s rest ih => simp only [applyQuaternionBlockSwapChain,
      reindexQuaternionPolynomial_neg, ih]

private theorem chain_cap {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (c : Q') :
    HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps (cap c)) (cap c) := by
  induction steps with
  | nil => exact HaarCarrierEqv.refl blocks _
  | cons s rest ih =>
      exact (chain_carrier rest (reindex_supported s (cap c))
        (support_cap blocks c) (reindex_cap_carrier s c)).trans ih

private theorem chain_gap {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (f : RatPoly)
    (hf : SupportedQuaternionBlocks blocks f) :
    HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain steps
        (polyAdd (cap 4) (polyNeg (polyMul f f))))
      (polyAdd (cap 4)
        (polyNeg (polyMul (applyQuaternionBlockSwapChain steps f)
          (applyQuaternionBlockSwapChain steps f)))) := by
  rw [chain_add, chain_neg, chain_mul]
  exact HaarCarrierEqv.add (chain_cap steps 4)
    (HaarCarrierEqv.neg (HaarCarrierEqv.refl blocks _))

set_option maxHeartbeats 1000000 in
/-- An explicitly exposed four-word has the exact fundamental angular square
at its first original block. The exposure remains an opaque witness: no
dependent swap-chain construction is unfolded by this proof. -/
theorem oriented_fourWord_first_angularSquare_of_exposure
    {blocks : Nat} (hb : 3 < blocks)
    (a b c d : Fin blocks) (e : FourBlockExposure a b c d)
    (r0 r1 r2 r3 : Bool) :
    let f := characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare a.val f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  let f := characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar 1
  let g := applyQuaternionBlockSwapChain e.steps f
  let canonical := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
  have hf : SupportedQuaternionBlocks blocks f :=
    word_supported a.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 1
  have hg : SupportedQuaternionBlocks blocks g :=
    applyQuaternionBlockSwapChain_supported e.steps f hf
  have hc : SupportedQuaternionBlocks blocks canonical :=
    by simpa only [canonical, word, exposedFourWord] using
      (SU2QuaternionOrientedWordSelection.word_supported
        (by omega : 0 < blocks) (by omega : 1 < blocks)
        (by omega : 2 < blocks) hb r0 r1 r2 r3 1)
  have hgc : HaarCarrierEqv blocks g canonical :=
    carrierOfPrefix hg hc
      (SU2QuaternionOrientedWordSelection.character_prefix hb e r0 r1 r2 r3 1)
  have hangular : HaarCarrierEqv blocks (angularSquare g)
      (polyAdd (cap 4) (polyNeg (polyMul g g))) :=
    (angularSquare_carrier (by omega) hgc).trans
      ((exposedFundamental_angularSquare hb r0 r1 r2 r3).trans
        (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
          (HaarCarrierEqv.neg (HaarCarrierEqv.mul hgc.symm hgc.symm))))
  have htrans := chain_blockAngularSquare_carrier e.steps 0 (by omega) f hf
  rw [e.source_zero] at htrans
  have hgap := chain_gap e.steps f hf
  have hchain : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain e.steps (blockAngularSquare a.val f))
      (applyQuaternionBlockSwapChain e.steps
        (polyAdd (cap 4) (polyNeg (polyMul f f)))) :=
    htrans.symm.trans (hangular.trans hgap.symm)
  exact reflect_chain_carrier e.steps
    (blockAngularSquare_supported a.isLt hf) (support_gap hf) hchain

private theorem blockAngularSquare_coeff (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare block p) (blockAngularSquare block q) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add
      (((hd 0 3).mul (hd 0 3)).add
        (((hd 1 2).mul (hd 1 2)).add
          (((hd 1 3).mul (hd 1 3)).add
            ((hd 2 3).mul (hd 2 3))))))

private theorem blockAngularSquare_zero (p : RatPoly) :
    blockAngularSquare 0 p = angularSquare p := rfl

set_option maxHeartbeats 1000000 in
/-- Literal original full-slab plaquette, with its first physical link moved
to the head. The identity remains valid after multiplying by ANY original
supported or unsupported polynomial insertion on the full Haar carrier. -/
theorem fullSlabFaceCharacter_head_angularSquare {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    let n := (boundaryCompleteSlabLinks extent).length
    let f := characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 1
    let a := blockA hf
    let s := headSwapBlockInvolution n a.val a.isLt
    let q := reindexQuaternionPolynomial s f
    HaarCarrierEqv n (angularSquare q)
      (polyAdd (cap 4) (polyNeg (polyMul q q))) := by
  dsimp only
  let n := (boundaryCompleteSlabLinks extent).length
  let a := blockA hf
  let b := blockB hf
  let c := blockC hf
  let d := blockD hf
  let f := characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 1
  let v := characterPolynomial
    (SU2QuaternionOrientedWordSelection.word a.val b.val c.val d.val false false true true).scalar 1
  let s := headSwapBlockInvolution n a.val a.isLt
  let q := reindexQuaternionPolynomial s f
  have hword : RatPolyCoeffEqv f v := by
    have h := original_character_eq_coordinateWord hf 1
    change RatPolyCoeffEqv f v at h
    exact h
  have hfirst : HaarCarrierEqv n (blockAngularSquare a.val v)
      (polyAdd (cap 4) (polyNeg (polyMul v v))) :=
    oriented_fourWord_first_angularSquare_of_exposure
      (face_carrier_four_blocks hf) a b c d (faceExposure hf)
      false false true true
  have hphysical : HaarCarrierEqv n (blockAngularSquare a.val f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) :=
    (RatPolyCoeffEqv.haarCarrier (blockAngularSquare_coeff a.val hword)).trans
      (hfirst.trans (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.refl (cap 4)).add
          (RatPolyCoeffEqv.neg (hword.mul hword))).symm))
  have hsupport : SupportedQuaternionBlocks n f := original_character_support extent face 1
  have hn : 0 < n := Nat.lt_trans (by decide : 0 < 3) (face_carrier_four_blocks hf)
  have hindex : s.map 0 = a.val := headSwapBlockInvolution_map_zero n a.val a.isLt
  have htransport : HaarCarrierEqv n
      (reindexQuaternionPolynomial s (blockAngularSquare a.val f))
      (angularSquare q) := by
    have h := reindex_blockAngularSquare_carrier s
      hn f hsupport
    rw [hindex] at h
    rw [blockAngularSquare_zero] at h
    exact h
  have hreindex : HaarCarrierEqv n
      (reindexQuaternionPolynomial s (blockAngularSquare a.val f))
      (reindexQuaternionPolynomial s
        (polyAdd (cap 4) (polyNeg (polyMul f f)))) :=
    reindex_carrier s (blockAngularSquare_supported a.isLt hsupport)
      (support_gap hsupport) hphysical
  have hgap : HaarCarrierEqv n
      (reindexQuaternionPolynomial s
        (polyAdd (cap 4) (polyNeg (polyMul f f))))
      (polyAdd (cap 4) (polyNeg (polyMul q q))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg,
      reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.add (reindex_cap_carrier s 4)
      (HaarCarrierEqv.neg (HaarCarrierEqv.refl n _))
  exact htransport.symm.trans (hreindex.trans hgap)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare.reindex_blockAngularSquare_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare.chain_blockAngularSquare_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare.oriented_fourWord_first_angularSquare_of_exposure
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare.fullSlabFaceCharacter_head_angularSquare
