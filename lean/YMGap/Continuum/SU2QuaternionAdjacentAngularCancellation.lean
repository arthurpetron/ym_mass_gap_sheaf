/-
# Oppositely incident plaquettes retain their coherent angular cancellation

For H+=U*p and H-=q*U^-1, with p,q independent of the SAME selected
link and Haar-unit, the original six-plane angular square satisfies

  Gamma_link(chi(H+)+chi(H-)) + (chi(H+)-chi(H-))^2
    = 4*(2-chi(H+*H-^-1)).

Thus its upper bound is a transported holonomy-difference trace, not the
sum of two individual curvature deficits. EVERY polynomial Haar insertion
is retained, including a full action depending on the shared link. The
discarded remainder is an actual supported square. The difference word
still contains the shared link twice: it is NOT the shared-link-eliminated
outer rectangle and no conditional-independence substitution is made.

The literal neighboring spatial faces are instantiated in
`BF4ExactSlabFixedSpatialAdjacentAngularCancellation`.
This supplies local signed interference data for the family angular/Ward
cost. Smallness under the original interacting law versus SAME OWN
variance, the complete signed Taylor correction and physical scaling
remain OPEN. Neither scalar zero-sum coefficients nor adjacency supplies
those estimates.
-/

import YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.SU2QuaternionAdjacentAngularCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube (plaquette)
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing (first_cycle)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

def forwardTrace (block : Nat) (p : PolyQuaternion) : RatPoly :=
  characterPolynomial (PolyQuaternion.coordinateVariable block ⋄ p).scalar 1

def reverseTrace (block : Nat) (q : PolyQuaternion) : RatPoly :=
  characterPolynomial (q ⋄ PolyQuaternion.conj (PolyQuaternion.coordinateVariable block)).scalar 1

/-- Both holonomies are based at the shared link. No link is integrated out. -/
def differenceTrace (block : Nat) (p q : PolyQuaternion) : RatPoly :=
  characterPolynomial ((PolyQuaternion.coordinateVariable block ⋄ p) ⋄
    PolyQuaternion.conj (q ⋄ PolyQuaternion.conj (PolyQuaternion.coordinateVariable block))).scalar 1

private def coherentTail (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart (polyNeg q.iPart),
    polyAdd p.jPart (polyNeg q.jPart), polyAdd p.kPart (polyNeg q.kPart)⟩

private def env (block : Nat) (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => polyVar (4*block) | 1 => polyVar (4*block+1)
  | 2 => polyVar (4*block+2) | 3 => polyVar (4*block+3)
  | 4 => p.scalar | 5 => p.iPart | 6 => p.jPart | 7 => p.kPart
  | 8 => q.scalar | 9 => q.iPart | 10 => q.jPart | 11 => q.kPart
  | _ => polyZero

private def uExpr := PolyQuaternionExpr.coordinate 0
private def pExpr := PolyQuaternionExpr.coordinate 4
private def qExpr := PolyQuaternionExpr.coordinate 8
private def coherentExpr : PolyQuaternionExpr :=
  ⟨.add (.var 4) (.var 8), .add (.var 5) (.neg (.var 9)),
    .add (.var 6) (.neg (.var 10)), .add (.var 7) (.neg (.var 11))⟩
private def fExpr : PolyExpr := .mul (.const 2) (PolyQuaternionExpr.mul uExpr pExpr).scalar
private def gExpr : PolyExpr := .mul (.const 2)
  (PolyQuaternionExpr.mul qExpr (PolyQuaternionExpr.conj uExpr)).scalar
private def dExpr : PolyExpr := .mul (.const 2)
  (PolyQuaternionExpr.mul (PolyQuaternionExpr.mul uExpr pExpr)
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.mul qExpr (PolyQuaternionExpr.conj uExpr)))).scalar

private theorem sum_recode (block : Nat) (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polyAdd (forwardTrace block p) (reverseTrace block q))
      (forwardTrace block (coherentTail p q)) := by
  have h : RatPolyCoeffEqv
      (polyAdd (PolyQuaternion.coordinateVariable block ⋄ p).scalar
        (q ⋄ PolyQuaternion.conj (PolyQuaternion.coordinateVariable block)).scalar)
      (PolyQuaternion.coordinateVariable block ⋄ coherentTail p q).scalar := by
    simpa only [coherentTail, PolyQuaternion.mul, PolyQuaternion.conj,
      PolyQuaternion.coordinateVariable, uExpr, pExpr, qExpr, coherentExpr,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, env] using
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (PolyQuaternionExpr.mul uExpr pExpr).scalar
          (PolyQuaternionExpr.mul qExpr (PolyQuaternionExpr.conj uExpr)).scalar)
        (PolyQuaternionExpr.mul uExpr coherentExpr).scalar
        (by decide) (env block p q))
  exact (RatPolyCoeffEqv.smul_add 2 _ _).symm.trans (h.smul 2)

private theorem square_congr (block : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (blockAngularSquare block f) (blockAngularSquare block g) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add (((hd 0 3).mul (hd 0 3)).add
      (((hd 1 2).mul (hd 1 2)).add (((hd 1 3).mul (hd 1 3)).add
        ((hd 2 3).mul (hd 2 3))))))

private theorem norm_recode (block : Nat) (p q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyAdd (polySmul 4 (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyQuaternionNorm (coherentTail p q))))
        (polyNeg (polyMul (forwardTrace block (coherentTail p q))
          (forwardTrace block (coherentTail p q)))))
      (polyAdd (polySmul 4 (polyAdd (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q)))
          (polyNeg (differenceTrace block p q))))
        (polyNeg (polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
          (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))))) := by
  let lhs : PolyExpr := .add
    (.mul (.const 4) (.mul (PolyQuaternionExpr.norm uExpr) (PolyQuaternionExpr.norm coherentExpr)))
    (.neg (.mul (.mul (.const 2) (PolyQuaternionExpr.mul uExpr coherentExpr).scalar)
      (.mul (.const 2) (PolyQuaternionExpr.mul uExpr coherentExpr).scalar)))
  let rhs : PolyExpr := .add
    (.mul (.const 4) (.add (.mul (PolyQuaternionExpr.norm uExpr)
      (.add (PolyQuaternionExpr.norm pExpr) (PolyQuaternionExpr.norm qExpr))) (.neg dExpr)))
    (.neg (.mul (.add fExpr (.neg gExpr)) (.add fExpr (.neg gExpr))))
  have h := coeffEvalExpr_eqv_of_normalize_eq lhs rhs (by decide +kernel) (env block p q)
  have hf : RatPolyCoeffEqv (coeffEvalExpr (env block p q) fExpr) (forwardTrace block p) :=
    cap_mul_left 2 _
  have hg : RatPolyCoeffEqv (coeffEvalExpr (env block p q) gExpr) (reverseTrace block q) :=
    cap_mul_left 2 _
  have hd : RatPolyCoeffEqv (coeffEvalExpr (env block p q) dExpr) (differenceTrace block p q) :=
    cap_mul_left 2 _
  have hc : RatPolyCoeffEqv (coeffEvalExpr (env block p q)
      (.mul (.const 2) (PolyQuaternionExpr.mul uExpr coherentExpr).scalar))
      (forwardTrace block (coherentTail p q)) := cap_mul_left 2 _
  have hdiff := hf.add (RatPolyCoeffEqv.neg hg)
  have hl : RatPolyCoeffEqv (coeffEvalExpr (env block p q) lhs)
      (polyAdd (polyMul (cap 4) (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyQuaternionNorm (coherentTail p q))))
        (polyNeg (polyMul (forwardTrace block (coherentTail p q))
          (forwardTrace block (coherentTail p q))))) :=
    (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hc.mul hc))
  have hr : RatPolyCoeffEqv (coeffEvalExpr (env block p q) rhs)
      (polyAdd (polyMul (cap 4) (polyAdd (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q)))
          (polyNeg (differenceTrace block p q))))
        (polyNeg (polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
          (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))))) :=
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hd)).mul_left (cap 4)).add
      (RatPolyCoeffEqv.neg (hdiff.mul hdiff))
  have he : RatPolyCoeffEqv
      (polyAdd (polyMul (cap 4) (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyQuaternionNorm (coherentTail p q))))
        (polyNeg (polyMul (forwardTrace block (coherentTail p q))
          (forwardTrace block (coherentTail p q)))))
      (polyAdd (polyMul (cap 4) (polyAdd (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q)))
          (polyNeg (differenceTrace block p q))))
        (polyNeg (polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
          (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))))) :=
    hl.symm.trans (h.trans hr)
  exact ((cap_mul_left 4 _).add (RatPolyCoeffEqv.refl _)).symm.trans
    (he.trans ((cap_mul_left 4 _).add (RatPolyCoeffEqv.refl _)))

/-- The complete opposite-incidence sum, retaining the actual norm factors
before invoking unit-quaternion laws. No independent-tail integration occurs. -/
theorem oriented_pair_angular_norm {blocks block : Nat} (hb : block < blocks)
    (p q : PolyQuaternion) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q) :
    HaarCarrierEqv blocks
      (blockAngularSquare block (polyAdd (forwardTrace block p) (reverseTrace block q)))
      (polyAdd (polySmul 4 (polyAdd (polyMul
        (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q)))
          (polyNeg (differenceTrace block p q))))
        (polyNeg (polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
          (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))))) := by
  have ht : HasPolyQuaternionBlockDegree block 0 (coherentTail p q) :=
    ⟨hp.scalar.add hq.scalar, hp.iPart.add hq.iPart.neg,
      hp.jPart.add hq.jPart.neg, hp.kPart.add hq.kPart.neg⟩
  exact (RatPolyCoeffEqv.haarCarrier (square_congr block (sum_recode block p q))).trans
    ((linear_angularSquare_norm hb (coherentTail p q) ht).trans
      (RatPolyCoeffEqv.haarCarrier (norm_recode block p q)))

/-- Exact gauge-covariant cancellation under EVERY original Haar insertion.
The trace on the right is a holonomy DIFFERENCE, not the outer rectangle. -/
theorem oriented_pair_angular_difference {blocks block : Nat} (hb : block < blocks)
    (p q : PolyQuaternion) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q)
    (hnp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (hnq : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv blocks
      (polyAdd (blockAngularSquare block (polyAdd (forwardTrace block p) (reverseTrace block q)))
        (polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
          (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))))
      (polySmul 4 (polyAdd (cap 2) (polyNeg (differenceTrace block p q)))) := by
  let A := blockAngularSquare block (polyAdd (forwardTrace block p) (reverseTrace block q))
  let D := polyMul (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
    (polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q)))
  let B := polyAdd (cap 2) (polyNeg (differenceTrace block p q))
  have hnorm : HaarCarrierEqv blocks
      (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
        (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q))) (cap 2) :=
    (HaarCarrierEqv.mul (haarNorm_coordinate hb) (HaarCarrierEqv.add hnp hnq)).trans
      (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.one_mul _).trans
        ((RatPolyCoeffEqv.add_smul_same 1 1 polyOne).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (1+1) 2) polyOne))))
  have h : HaarCarrierEqv blocks A (polyAdd (polySmul 4 B) (polyNeg D)) :=
    (oriented_pair_angular_norm hb p q hp hq).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.smul 4
        (HaarCarrierEqv.add hnorm (HaarCarrierEqv.refl blocks _))) (HaarCarrierEqv.refl blocks _))
  have hc : RatPolyCoeffEqv (polyAdd (polyAdd (polySmul 4 B) (polyNeg D)) D)
      (polySmul 4 B) :=
    (((cap_mul_left 4 B).symm.add (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.const 4) (.var 0)) (.neg (.var 1))) (.var 1))
        (.mul (.const 4) (.var 0)) (by decide) (fun | 0 => B | _ => D)).trans (cap_mul_left 4 B))
  exact (HaarCarrierEqv.add h (HaarCarrierEqv.refl blocks D)).trans (RatPolyCoeffEqv.haarCarrier hc)

/-- The sharp discarded term is a computed square under the SAME full W.
W may depend on the shared link; no spectator premise is used. -/
theorem oriented_pair_weighted_angular_le {blocks block : Nat} (hb : block < blocks)
    (p q : PolyQuaternion) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q)
    (hnp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (hnq : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne)
    (hf : SupportedQuaternionBlocks blocks (forwardTrace block p))
    (hg : SupportedQuaternionBlocks blocks (reverseTrace block q))
    (W : RatPoly) (hW : Certificate blocks W) :
    quaternionHaar blocks (polyMul W
      (blockAngularSquare block (polyAdd (forwardTrace block p) (reverseTrace block q)))) ≤
      4*quaternionHaar blocks (polyMul W (polyAdd (cap 2) (polyNeg (differenceTrace block p q)))) := by
  let A := blockAngularSquare block (polyAdd (forwardTrace block p) (reverseTrace block q))
  let d := polyAdd (forwardTrace block p) (polyNeg (reverseTrace block q))
  let B := polyAdd (cap 2) (polyNeg (differenceTrace block p q))
  have hd : SupportedQuaternionBlocks blocks d := supported_add hf (by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hg s hs)
  have hz : (0 : Q') ≤ quaternionHaar blocks (polyMul W (polyMul d d)) :=
    (hW.mul (.square d hd)).haar_nonnegative
  have hid : quaternionHaar blocks (polyMul W A)+quaternionHaar blocks (polyMul W (polyMul d d)) ≈
      4*quaternionHaar blocks (polyMul W B) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W A (polyMul d d)))
        (quaternionHaar_append blocks _ _)))
      (Q'.eqv_trans _ _ _ (oriented_pair_angular_difference hb p q hp hq hnp hnq W)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 4 W B))
          (quaternionHaar_polySmul blocks 4 (polyMul W B))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hz) (Q'.le_of_eqv hid)

#print axioms forwardTrace
#print axioms reverseTrace
#print axioms differenceTrace
#print axioms oriented_pair_angular_norm
#print axioms oriented_pair_angular_difference
#print axioms oriented_pair_weighted_angular_le

end YMGap.Continuum.SU2QuaternionAdjacentAngularCancellation
