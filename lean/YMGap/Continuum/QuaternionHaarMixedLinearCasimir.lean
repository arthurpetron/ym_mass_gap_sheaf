/-
# The local Casimir of two degree-one angular gradients

On the SAME finite quaternion Haar carrier, C_s Gamma_s(p,q) is
2 Gamma_s(p,q)-6 p*q when both polynomials have degree one at s.
Their signed, shared spectator coefficients are arbitrary; no spectator
unit norm or analytic hypothesis is supplied. Euler reconstruction and a
finite mixed-wedge identity prove the head result, followed by a supported
head-swap transport. Only tangential derivatives transport Haar equality.

This is local polynomial algebra. Joining all physical slots of an actual
overlapping face pair, bounding its signed insertion, and MAIN retention
remain separate obligations.
-/

import YMGap.Continuum.SU2QuaternionBlockLinearCasimir
import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear

namespace YMGap.Continuum.QuaternionHaarMixedLinearCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

private def localC (s : Nat) (p : RatPoly) : RatPoly :=
  polyNeg (blockAngularLaplacian s p)

private theorem singletonC (s : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial [s] p) (localC s p) := by
  change RatPolyCoeffEqv (polyAdd (localC s p) polyZero) (localC s p)
  exact RatPolyCoeffEqv.add_zero _

private theorem singletonGamma (s : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (activeGamma [s] p q) (blockGamma s p q) := by
  change RatPolyCoeffEqv (polyAdd (blockGamma s p q) polyZero) _
  exact RatPolyCoeffEqv.add_zero _

private theorem headLap (p : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian 0 p) (angularLaplacian p) := by
  simpa only [angularLaplacian, blockAngularDerivative, Nat.mul_zero, Nat.zero_add]
    using blockAngularLaplacian_eq_six 0 p

private theorem six_coeff {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))))))

private def fourExpr (f : Nat → PolyExpr) : PolyExpr :=
  .add (f 0) (.add (f 1) (.add (f 2) (f 3)))

private def sixExpr (f : Nat → Nat → PolyExpr) : PolyExpr :=
  .add (f 0 1) (.add (f 0 2) (.add (f 0 3)
    (.add (f 1 2) (.add (f 1 3) (f 2 3)))))

private def wedgeExpr (offset i j : Nat) : PolyExpr :=
  .add (.mul (.var i) (.var (offset+j)))
    (.neg (.mul (.var j) (.var (offset+i))))

private def linearEnv (p q : RatPoly) : Nat → RatPoly
  | 0 => polyVar 0 | 1 => polyVar 1 | 2 => polyVar 2 | 3 => polyVar 3
  | 4 => ratDerivative 0 p | 5 => ratDerivative 1 p
  | 6 => ratDerivative 2 p | 7 => ratDerivative 3 p
  | 8 => ratDerivative 0 q | 9 => ratDerivative 1 q
  | 10 => ratDerivative 2 q | _ => ratDerivative 3 q

private theorem field_wedge (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j p)
      (polyAdd (polyMul (polyVar i) (ratDerivative j p))
        (polyNeg (polyMul (polyVar j) (ratDerivative i p)))) :=
  (RatPolyCoeffEqv.refl _).add (neg_smul _).symm

private theorem mixed_wedge (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (blockGamma 0 p q) (polyMul (headEuler p) (headEuler q)))
      (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0))
        (headGradientDot p q)) := by
  have hf := six_coeff (fun i j _ _ => (field_wedge i j p).mul (field_wedge i j q))
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (sixExpr (fun i j => .mul (wedgeExpr 4 i j) (wedgeExpr 8 i j)))
      (.mul (fourExpr (fun i => .mul (.var i) (.var (4+i))))
        (fourExpr (fun i => .mul (.var i) (.var (8+i))))))
    (.mul (fourExpr (fun i => .mul (.var i) (.var i)))
      (fourExpr (fun i => .mul (.var (4+i)) (.var (8+i)))))
    (by decide) (linearEnv p q)
  exact (hf.add (RatPolyCoeffEqv.refl _)).trans hr

private theorem euler_linear (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) :
    RatPolyCoeffEqv (headEuler p) p :=
  (headEuler_of_blockDegree 1 p hp).trans
    ((cap_mul_left 1 p).symm.trans (RatPolyCoeffEqv.one_mul p))

private theorem head_gradient_constant (p q : RatPoly)
    (hp : HasQuaternionBlockDegree 0 1 p) (hq : HasQuaternionBlockDegree 0 1 q)
    (i j : Nat) (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (angularDerivative i j (headGradientDot p q)) polyZero := by
  have h (k : Nat) (hk : k < 4) : RatPolyCoeffEqv
      (angularDerivative i j (polyMul (ratDerivative k p) (ratDerivative k q))) polyZero :=
    (angularDerivative_mul i j _ _).trans
      ((((angular_partial_zero hi hj hk p hp).mul_right _).trans
        (RatPolyCoeffEqv.mul_zero_left _)).add
        (((angular_partial_zero hi hj hk q hq).mul_left _).trans
          (RatPolyCoeffEqv.mul_zero_right _)))
  exact (angularDerivative_add i j _ _).trans
    (((h 0 (by decide)).add
      ((angularDerivative_add i j _ _).trans
        ((h 1 (by decide)).add
          ((angularDerivative_add i j _ _).trans
            ((h 2 (by decide)).add (h 3 (by decide))))))).trans
      (RatPolyCoeffEqv.refl polyZero))

private theorem head_gradient_casimir_zero (p q : RatPoly)
    (hp : HasQuaternionBlockDegree 0 1 p) (hq : HasQuaternionBlockDegree 0 1 q) :
    RatPolyCoeffEqv (localC 0 (headGradientDot p q)) polyZero := by
  have h := six_coeff (fun i j hi hj =>
    (angularDerivative_congr i j (head_gradient_constant p q hp hq i j hi hj)).trans
      (RatPolyCoeffEqv.refl polyZero))
  exact RatPolyCoeffEqv.neg ((headLap _).trans h)

private theorem head_gamma_plus_product {blocks : Nat} (hb : 0 < blocks)
    (p q : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (hq : HasQuaternionBlockDegree 0 1 q) :
    HaarCarrierEqv blocks (polyAdd (blockGamma 0 p q) (polyMul p q))
      (headGradientDot p q) := by
  have he := (RatPolyCoeffEqv.refl (blockGamma 0 p q)).add
    ((euler_linear p hp).mul (euler_linear q hq)).symm
  have hr : HaarCarrierEqv blocks
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0)) polyOne :=
    (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_coordinateVariable 0)).trans
      (quaternionRadiusPolynomial_carrier_one hb)
  exact (RatPolyCoeffEqv.haarCarrier (he.trans (mixed_wedge p q))).trans
    ((HaarCarrierEqv.mul_right (headGradientDot p q) hr).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _)))

private theorem headC_add (p q : RatPoly) :
    RatPolyCoeffEqv (localC 0 (polyAdd p q))
      (polyAdd (localC 0 p) (localC 0 q)) := by
  have h := (headLap _).trans ((angularLaplacian_add p q).trans
    ((headLap p).symm.add (headLap q).symm))
  exact (RatPolyCoeffEqv.neg h).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.var 1)))
      (.add (.neg (.var 0)) (.neg (.var 1))) (by decide)
      (fun | 0 => blockAngularLaplacian 0 p | _ => blockAngularLaplacian 0 q))

private theorem headC_product {blocks : Nat} (hb : 0 < blocks)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree 0 1 p) (hdq : HasQuaternionBlockDegree 0 1 q) :
    HaarCarrierEqv blocks (localC 0 (polyMul p q))
      (polyAdd (polySmul 6 (polyMul p q)) (polySmul (-2) (blockGamma 0 p q))) := by
  have eigen (r : RatPoly) (hr : SupportedQuaternionBlocks blocks r)
      (hd : HasQuaternionBlockDegree 0 1 r) :
      HaarCarrierEqv blocks (activeCasimirPolynomial [0] r) (polySmul 3 r) := by
    exact (RatPolyCoeffEqv.haarCarrier (singletonC 0 r)).trans
      ((HaarCarrierEqv.neg (blockCasimir_linear hb r hr hd)).trans
        (RatPolyCoeffEqv.haarCarrier
          ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) (-3) r).trans
            (RatPolyCoeffEqv.smul_coefficient (by decide) r)))))
  have h := (RatPolyCoeffEqv.haarCarrier (singletonC 0 (polyMul p q))).symm.trans
    ((RatPolyCoeffEqv.haarCarrier (activeCasimirPolynomial_mul [0] p q)).trans
      (HaarCarrierEqv.add
        (HaarCarrierEqv.add (HaarCarrierEqv.mul_right q (eigen p hp hdp))
          (HaarCarrierEqv.mul_left p (eigen q hq hdq)))
        (RatPolyCoeffEqv.haarCarrier ((singletonGamma 0 p q).smul (-2)))))
  have hc : RatPolyCoeffEqv
      (polyAdd (polyMul (polySmul 3 p) q) (polyMul p (polySmul 3 q)))
      (polySmul 6 (polyMul p q)) := ((RatPolyCoeffEqv.polyMul_smul_left 3 p q).add
    (RatPolyCoeffEqv.polyMul_smul_right 3 p q)).trans
      ((RatPolyCoeffEqv.add_smul_same 3 3 (polyMul p q)).trans
        (RatPolyCoeffEqv.smul_coefficient
          (by decide : Q'.eqv ((3 : Q')+3) 6) (polyMul p q)))
  exact h.trans (RatPolyCoeffEqv.haarCarrier (hc.add (RatPolyCoeffEqv.refl _)))

private theorem cancel_polynomial (a g r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd a (polyAdd (polySmul 6 r) (polySmul (-2) g)))
        (polyAdd (polySmul 2 g) (polySmul (-6) r))) a := by
  have hs := (RatPolyCoeffEqv.refl a).add
    ((cap_mul_left 6 r).symm.add (cap_mul_left (-2) g).symm)
  have ht := (cap_mul_left 2 g).symm.add (cap_mul_left (-6) r).symm
  exact (hs.add ht).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.add (.mul (.const 6) (.var 2)) (.mul (.const (-2)) (.var 1))))
        (.add (.mul (.const 2) (.var 1)) (.mul (.const (-6)) (.var 2))))
      (.var 0) (by decide) (fun | 0 => a | 1 => g | _ => r))

/-- Head-block mixed-gradient Casimir, with unrestricted supported spectator
coefficients. No unit norm for either polynomial or its tails is needed. -/
theorem headGamma_linear_casimir {blocks : Nat} (hb : 0 < blocks)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree 0 1 p) (hdq : HasQuaternionBlockDegree 0 1 q) :
    HaarCarrierEqv blocks (localC 0 (blockGamma 0 p q))
      (polyAdd (polySmul 2 (blockGamma 0 p q)) (polySmul (-6) (polyMul p q))) := by
  let g := blockGamma 0 p q
  let r := polyMul p q
  let target := polyAdd (polySmul 2 g) (polySmul (-6) r)
  have hzero : HaarCarrierEqv blocks (localC 0 (polyAdd g r)) polyZero :=
    (HaarCarrierEqv.neg (blockAngularLaplacian_carrier hb
      (head_gamma_plus_product hb p q hdp hdq))).trans
        (RatPolyCoeffEqv.haarCarrier (head_gradient_casimir_zero p q hdp hdq))
  have hsum : HaarCarrierEqv blocks
      (polyAdd (localC 0 g) (polyAdd (polySmul 6 r) (polySmul (-2) g))) polyZero :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks (localC 0 g))
      (headC_product hb p q hp hq hdp hdq)).symm.trans
        ((RatPolyCoeffEqv.haarCarrier (headC_add g r)).symm.trans hzero)
  exact (RatPolyCoeffEqv.haarCarrier (cancel_polynomial (localC 0 g) g r)).symm.trans
    ((HaarCarrierEqv.add hsum (HaarCarrierEqv.refl blocks target)).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add target)))

private theorem gamma_carrier {blocks block : Nat} (hb : block < blocks)
    {p p' q q' : RatPoly} (hp : HaarCarrierEqv blocks p p')
    (hq : HaarCarrierEqv blocks q q') :
    HaarCarrierEqv blocks (blockGamma block p q) (blockGamma block p' q') := by
  exact six_carrier (fun i j hi hj => HaarCarrierEqv.mul
    (YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.angularDerivative_carrier_at hb hi hj hp)
    (YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.angularDerivative_carrier_at hb hi hj hq))

private theorem reindex_gamma {blocks block : Nat} (s : QuaternionBlockInvolution blocks)
    (hb : block < blocks) (p q : RatPoly) :
    HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s (blockGamma (s.map block) p q))
      (blockGamma block (reindexQuaternionPolynomial s p) (reindexQuaternionPolynomial s q)) := by
  have hs := six_carrier (fun i j hi hj => HaarCarrierEqv.mul
    (carrierOfPrefix
      (reindex_supported s (blockAngularDerivative (s.map block) i j p))
      (angularDerivative_supported_at (by omega) (by omega) (reindex_supported s p))
      (reindex_blockAngularDerivative_prefix s hb hi hj p))
    (carrierOfPrefix
      (reindex_supported s (blockAngularDerivative (s.map block) i j q))
      (angularDerivative_supported_at (by omega) (by omega) (reindex_supported s q))
      (reindex_blockAngularDerivative_prefix s hb hi hj q)))
  simpa only [blockGamma, six, reindexQuaternionPolynomial_add,
    reindexQuaternionPolynomial_mul] using hs

/-- The actual one-block six-plane Casimir of the mixed angular gradient.
The selected slot is transported through an explicit supported head swap;
both original polynomials and every shared spectator remain unchanged. -/
theorem blockGamma_linear_casimir {blocks block : Nat} (hblock : block < blocks)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree block 1 p) (hdq : HasQuaternionBlockDegree block 1 q) :
    HaarCarrierEqv blocks
      (activeCasimirPolynomial [block] (blockGamma block p q))
      (polyAdd (polySmul 2 (blockGamma block p q)) (polySmul (-6) (polyMul p q))) := by
  let s := headSwapBlockInvolution blocks block hblock
  let p' := reindexQuaternionPolynomial s p
  let q' := reindexQuaternionPolynomial s q
  let g' := blockGamma 0 p' q'
  have hb : 0 < blocks := by omega
  have hs0 : s.map 0 = block := headSwapBlockInvolution_map_zero blocks block hblock
  have hsb : s.map block = 0 := headSwapBlockInvolution_map_selected blocks block hblock
  have hp' : SupportedQuaternionBlocks blocks p' := reindex_supported s p
  have hq' : SupportedQuaternionBlocks blocks q' := reindex_supported s q
  have hd'p : HasQuaternionBlockDegree 0 1 p' := blockDegree_reindex s hb hs0 hdp
  have hd'q : HasQuaternionBlockDegree 0 1 q' := blockDegree_reindex s hb hs0 hdq
  have hbackp : HaarCarrierEqv blocks (reindexQuaternionPolynomial s p') p :=
    carrierOfPrefix (reindex_supported s p') hp (reindex_twice_prefix s p)
  have hbackq : HaarCarrierEqv blocks (reindexQuaternionPolynomial s q') q :=
    carrierOfPrefix (reindex_supported s q') hq (reindex_twice_prefix s q)
  have hg' : SupportedQuaternionBlocks blocks g' := by
    have h (i j : Nat) (hi : i < 4) (hj : j < 4) :
        SupportedQuaternionBlocks blocks
          (polyMul (blockAngularDerivative 0 i j p') (blockAngularDerivative 0 i j q')) :=
      supported_polyMul
        (angularDerivative_supported_at (by omega) (by omega) hp')
        (angularDerivative_supported_at (by omega) (by omega) hq')
    exact polyAdd_supported (h 0 1 (by decide) (by decide))
      (polyAdd_supported (h 0 2 (by decide) (by decide))
        (polyAdd_supported (h 0 3 (by decide) (by decide))
          (polyAdd_supported (h 1 2 (by decide) (by decide))
            (polyAdd_supported (h 1 3 (by decide) (by decide)) (h 2 3 (by decide) (by decide))))))
  have hgammaHead : HaarCarrierEqv blocks (reindexQuaternionPolynomial s g')
      (blockGamma block (reindexQuaternionPolynomial s p')
        (reindexQuaternionPolynomial s q')) := by
    simpa only [hsb] using reindex_gamma s hblock p' q'
  have hgamma : HaarCarrierEqv blocks (reindexQuaternionPolynomial s g') (blockGamma block p q) :=
    hgammaHead.trans (gamma_carrier hblock hbackp hbackq)
  have hleft : HaarCarrierEqv blocks (reindexQuaternionPolynomial s (localC 0 g'))
      (localC block (blockGamma block p q)) := by
    rw [localC, reindexQuaternionPolynomial_neg]
    have ht : HaarCarrierEqv blocks
        (reindexQuaternionPolynomial s (blockAngularLaplacian 0 g'))
        (blockAngularLaplacian block (reindexQuaternionPolynomial s g')) := by
      simpa only [hsb] using reindex_blockAngularLaplacian_carrier s hblock g' hg'
    exact HaarCarrierEqv.neg (ht.trans (blockAngularLaplacian_carrier hblock hgamma))
  have htarget : SupportedQuaternionBlocks blocks
      (polyAdd (polySmul 2 g') (polySmul (-6) (polyMul p' q'))) :=
    polyAdd_supported (polySmul_supported hg' 2)
      (polySmul_supported (supported_polyMul hp' hq') (-6))
  have hc := reindex_carrier s
    (by
      intro t ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact blockAngularLaplacian_supported hb hg' u hu)
    htarget (headGamma_linear_casimir hb p' q' hp' hq' hd'p hd'q)
  have hright : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (polyAdd (polySmul 2 g') (polySmul (-6) (polyMul p' q'))))
      (polyAdd (polySmul 2 (blockGamma block p q)) (polySmul (-6) (polyMul p q))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul,
      reindexQuaternionPolynomial_smul, reindexQuaternionPolynomial_mul]
    exact HaarCarrierEqv.add (HaarCarrierEqv.smul 2 hgamma)
      (HaarCarrierEqv.smul (-6) (HaarCarrierEqv.mul hbackp hbackq))
  exact (RatPolyCoeffEqv.haarCarrier (singletonC block _)).trans
    (hleft.symm.trans (hc.trans hright))

end YMGap.Continuum.QuaternionHaarMixedLinearCasimir

#print axioms YMGap.Continuum.QuaternionHaarMixedLinearCasimir.headGamma_linear_casimir
#print axioms YMGap.Continuum.QuaternionHaarMixedLinearCasimir.blockGamma_linear_casimir
