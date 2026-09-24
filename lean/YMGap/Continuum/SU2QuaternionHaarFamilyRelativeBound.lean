/-
# Relative angular bounds survive spectator Haar integration

The original positive-cone witnesses `c*p + Dp` and `c*p - Dp` can be integrated over
any finite family not containing the differentiated block. The resulting
witnesses concern the actual projected source, with exactly the same c.
Repeated projection indices are allowed. No conditional heat operator is
identified with a Haar projection, and no source is divided out.

The consumer is the complete BF4 endpoint source P_fringe(V*g_n), not just
the terminal message. The weighted square consequence retains every
certified positive background. It is not an interacting-variance estimate.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockCertificate
import YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionHaarFamilyRelativeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- Construct the positive certificate after the actual integration schedule. -/
def familyProjectCertificate (blocks : Nat) :
    (ids : List Nat) → (∀ s, s ∈ ids → s < blocks) →
    {p : RatPoly} → SupportedQuaternionBlocks blocks p → Certificate blocks p →
      Certificate blocks (familyProject ids p)
  | [], _, _, _, P => P
  | s::ids, hs, _, hp, P =>
      familyProjectCertificate blocks ids (fun t ht => hs t (List.mem_cons_of_mem s ht))
        (project_supported s hp) (project_certificate blocks s (hs s List.mem_cons_self) hp P)

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

/-- Integration over other blocks preserves the same relative constant.
Both the derivative and source remain on their original coordinate carrier. -/
def familyProjectRelativeBound (blocks : Nat) (ids : List Nat)
    (hids : ∀ s, s ∈ ids → s < blocks) (block : Nat) (hb : block < blocks)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (hnot : block ∉ ids)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks blocks p)
    (P : RelativeBound blocks (4*block+i) (4*block+j) p c) :
    RelativeBound blocks (4*block+i) (4*block+j) (familyProject ids p) c := by
  have hd := blockAngularDerivative_familyProject ids block i j hi hj hnot p
  have hs : SupportedQuaternionBlocks blocks (angularDerivative (4*block+i) (4*block+j) p) :=
    angularDerivative_supported_at (by omega) (by omega) hp
  have hc : SupportedQuaternionBlocks blocks (cap c) :=
    polySmul_supported (supported_one blocks) c
  have hm := familyProject_mul_of_independent ids (cap c) p (fun s _ =>
    quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne s))
  refine ⟨familyProjectCertificate blocks ids hids hp P.positive, P.nonnegative, ?_, ?_⟩
  · have C := familyProjectCertificate blocks ids hids
      (supported_add (supported_polyMul hc hp) (neg_supported hs)) P.upper
    rw [familyProject_add] at C
    exact .ofCoeff (hm.add ((familyProject_neg ids _).trans
      (RatPolyCoeffEqv.neg hd.symm))).symm C
  · have C := familyProjectCertificate blocks ids hids
      (supported_add (supported_polyMul hc hp) hs) P.lower
    rw [familyProject_add] at C
    exact .ofCoeff (hm.add hd.symm).symm C

/-- Multiplying the two relative certificates controls the derivative
square with no loss and without deciding whether the source vanishes. -/
def relativeSquareCertificate {blocks i j : Nat} {p : RatPoly} {c : Q'}
    (P : RelativeBound blocks i j p c) :
    Certificate blocks (polyAdd
      (polyMul (polyMul (cap c) p) (polyMul (cap c) p))
      (polyNeg (polyMul (angularDerivative i j p) (angularDerivative i j p)))) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
    (by decide) (fun | 0 => polyMul (cap c) p | _ => angularDerivative i j p))
    (P.upper.mul P.lower)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem scaled_square_pair (blocks : Nat) (c : Q') (p R : RatPoly) :
    quaternionHaar blocks
      (polyMul (polyMul (polyMul (cap c) p) (polyMul (cap c) p)) R) ≈
      (c*c) * weightedPair blocks R p p := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul (cap c) p) (polyMul (cap c) p)) R)
      (polySmul (c*c) (polyMul (polyMul p p) R)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => cap c | 1 => p | _ => R)).trans
      (((cap_mul c c).mul_right _).trans (cap_mul_left (c*c) _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he) (quaternionHaar_polySmul _ _ _)

/-- The same relative constant controls the SAME derivative square under
any certified positive background, including shared-variable backgrounds. -/
theorem relativeWeightedSquare {blocks i j : Nat} {p R : RatPoly} {c : Q'}
    (P : RelativeBound blocks i j p c) (HR : Certificate blocks R) :
    weightedPair blocks R (angularDerivative i j p) (angularDerivative i j p) ≤
      (c*c) * weightedPair blocks R p p := by
  let d := angularDerivative i j p
  let a := polyMul (cap c) p
  have C := (relativeSquareCertificate P).mul HR
  have he : quaternionHaar blocks
      (polyMul (polyAdd (polyMul a a) (polyNeg (polyMul d d))) R) ≈
      (c*c) * weightedPair blocks R p p + -(weightedPair blocks R d d) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => polyMul a a | 1 => polyMul d d | _ => R)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (scaled_square_pair blocks c p R) (haar_neg _ _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ C.haar_nonnegative (Q'.le_of_eqv he))

#print axioms familyProjectCertificate
#print axioms familyProjectRelativeBound
#print axioms relativeSquareCertificate
#print axioms relativeWeightedSquare

end YMGap.Continuum.SU2QuaternionHaarFamilyRelativeBound
