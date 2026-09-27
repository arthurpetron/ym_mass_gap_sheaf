/-
# Signed mixed cost on the original slab action

The mixed numerator D*N(p*q)-N(p)*N(q) retains the original exterior
weight.  No sign or small-interaction estimate is asserted.  In particular,
the cross-link application pairs an exterior-modulated polynomial residual
with another residual, not an independent-link or deleted-action pairing.
The exterior insertion need not preserve the second link's kernel.
-/

import YMGap.Continuum.BF4ExactSlabStarPolynomialCost

namespace YMGap.Continuum.BF4ExactSlabStarMixedPolynomialCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarExteriorResidual
open YMGap.Continuum.BF4ExactSlabStarPolynomialCost
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ q : RatPoly,
    quaternionHaar blocks (polyNeg q) ≈ -(quaternionHaar blocks q)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: qs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 _) (haar_neg blocks qs))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property
local notation "E" => exteriorSeed hw0 hw1 K extent hK i
local notation "t" => polynomialResidual hw0 hw1 K extent hK i

/-- The signed conditional covariance numerator of two distinct inputs. -/
def mixedNumerator (p q : (F).V) : RatPoly :=
  polyAdd
    (polyMul (normalizer w K extent i.val i.property)
      (N ⟨polyMul p.val q.val, supported_polyMul p.property q.property⟩).val)
    (polyNeg (polyMul (N p).val (N q).val))

/-- Signed mixed numerator tested against the unchanged original exterior. -/
def mixedFunctional (r : (G).V) (p q : (F).V) : Q' :=
  quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
    (polyMul (polyMul r.val (mixedNumerator hw0 hw1 K extent hK i p q))
      (exterior w K extent i.val i.property))

set_option maxHeartbeats 2000000 in
/-- The same-action signed pairing is exactly the retained-exterior mixed
numerator, without a positivity or independent-spectator assumption. -/
theorem exterior_mixed_pair (r : (G).V) (p q : (F).V) :
    (F).B (E r p) (t q) ≈ mixedFunctional hw0 hw1 K extent hK i r p q := by
  let d := normalizerState hw0 hw1 K extent hK i
  let rd : (G).V := ⟨polyMul r.val d.val, supported_polyMul r.property d.property⟩
  let rn : (G).V := ⟨polyMul r.val (N q).val, supported_polyMul r.property (N q).property⟩
  let pq : (F).V := ⟨polyMul p.val q.val, supported_polyMul p.property q.property⟩
  have hJd : (J rd).val = polyMul (J r).val (J d).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val d.val
  have hJn : (J rn).val = polyMul (J r).val (J (N q)).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val (N q).val
  have hfirst : (F).B (E r p) (E d q) ≈ (G).B rd (N pq) := by
    have hc : (F).B (E r p) (E d q) ≈ (F).B (J rd) pq := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      rw [hJd]
      exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (by decide) (fun | 0 => (J r).val | 1 => (J d).val
                         | 2 => p.val | _ => q.val)).mul_right _)
    exact Q'.eqv_trans _ _ _ hc
      (probeMap_test hw0 hw1 K extent hK i.val i.property rd pq)
  have hsecond : (F).B (E r p) (J (N q)) ≈ (G).B rn (N p) := by
    have hc : (F).B (E r p) (J (N q)) ≈ (F).B (J rn) p := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      rw [hJn]
      exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => (J r).val | 1 => p.val | _ => (J (N q)).val)).mul_right _)
    exact Q'.eqv_trans _ _ _ hc
      (probeMap_test hw0 hw1 K extent hK i.val i.property rn p)
  have hv : mixedFunctional hw0 hw1 K extent hK i r p q ≈
      (G).B rd (N pq) + -((G).B rn (N p)) := by
    have hc := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 3) (.var 4))))) (.var 5))
      (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 5))
        (.neg (.mul (.mul (.mul (.var 0) (.var 4)) (.var 3)) (.var 5))))
      (by decide)
      (fun | 0 => r.val | 1 => d.val | 2 => (N pq).val
           | 3 => (N p).val | 4 => (N q).val
           | _ => exterior w K extent i.val i.property)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg _ _)))
  change (F).B (E r p) ((F).sub (E d q) (J (N q))) ≈ _
  exact Q'.eqv_trans _ _ _ ((F).B_add_right (E r p) (E d q) ((F).neg (J (N q))))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst
      (Q'.eqv_trans _ _ _ ((F).B_neg_right (E r p) (J (N q)))
        (Q'.neg_eqv_congr _ _ hsecond))) hv.symm)

/-- Pair an exterior-modulated residual of a second physical link against
the first link's residual under the complete original slab action. The
insertion need not preserve the second link's kernel. No smallness or
orthogonality is asserted. -/
theorem cross_link_kernel_test (j : PhysicalLink extent) (r : (G).V)
    (p q : (F).V) :
    (F).B (E r (polynomialResidual hw0 hw1 K extent hK j p)) (t q) ≈
      mixedFunctional hw0 hw1 K extent hK i r
        (polynomialResidual hw0 hw1 K extent hK j p) q :=
  exterior_mixed_pair hw0 hw1 K extent hK i r
    (polynomialResidual hw0 hw1 K extent hK j p) q

#print axioms mixedNumerator
#print axioms mixedFunctional
#print axioms exterior_mixed_pair
#print axioms cross_link_kernel_test

end YMGap.Continuum.BF4ExactSlabStarMixedPolynomialCost
