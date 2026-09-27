/-
# The exact retained-exterior cost of an original conditional-kernel test

For t(p)=J(D)*p-J(Np) and Phi=D*N(p^2)-Np^2, the signed pairing with
J(r)*p is H[B*r*Phi]. In particular the actual squared cost of t(p) is
H[B*D*Phi], not H[B*Phi] and not a normalizer-cap replacement. These
identities expose the quantities consumed by exact test-ray optimization.
They do not bound the ratio uniformly or establish global coercivity.
-/

import YMGap.Continuum.BF4ExactSlabStarExteriorResidual
import YMGap.Continuum.BF4ExactSlabStarOptimizedPolynomialTest

namespace YMGap.Continuum.BF4ExactSlabStarPolynomialCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
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
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.BF4ExactSlabStarExteriorResidual
open YMGap.Continuum.BF4ExactSlabStarNormalizedPolynomialTest
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

def normalizerState : (G).V :=
  ⟨normalizer w K extent i.val i.property,
    normalizer_supported w K extent i.val i.property⟩

/-- Original signed variance functional with a retained exterior insertion. -/
def varianceFunctional (r : (G).V) (p : (F).V) : Q' :=
  quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
    (polyMul (polyMul r.val (varianceNumerator w K extent i.val i.property p.val))
      (exterior w K extent i.val i.property))

set_option maxHeartbeats 2000000 in
/-- Arbitrary signed exterior insertion, with the SAME original B and D. -/
theorem exterior_variance_pair (r : (G).V) (p : (F).V) :
    (F).B (E r p) (t p) ≈ varianceFunctional hw0 hw1 K extent hK i r p := by
  let d := normalizerState hw0 hw1 K extent hK i
  let rd : (G).V := ⟨polyMul r.val d.val, supported_polyMul r.property d.property⟩
  let rn : (G).V := ⟨polyMul r.val (N p).val, supported_polyMul r.property (N p).property⟩
  let pp : (F).V := ⟨polyMul p.val p.val, supported_polyMul p.property p.property⟩
  have hJd : (J rd).val = polyMul (J r).val (J d).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val d.val
  have hJn : (J rn).val = polyMul (J r).val (J (N p)).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val (N p).val
  have hfirst : (F).B (E r p) (E d p) ≈ (G).B rd (N pp) := by
    have hc : (F).B (E r p) (E d p) ≈ (F).B (J rd) pp := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      rw [hJd]
      exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
        (by decide) (fun | 0 => (J r).val | 1 => (J d).val | _ => p.val)).mul_right _)
    exact Q'.eqv_trans _ _ _ hc
      (probeMap_test hw0 hw1 K extent hK i.val i.property rd pp)
  have hsecond : (F).B (E r p) (J (N p)) ≈ (G).B rn (N p) := by
    have hc : (F).B (E r p) (J (N p)) ≈ (F).B (J rn) p := by
      change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
      rw [hJn]
      exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => (J r).val | 1 => p.val | _ => (J (N p)).val)).mul_right _)
    exact Q'.eqv_trans _ _ _ hc
      (probeMap_test hw0 hw1 K extent hK i.val i.property rn p)
  have hv : varianceFunctional hw0 hw1 K extent hK i r p ≈
      (G).B rd (N pp) + -((G).B rn (N p)) := by
    have hc := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 3) (.var 3))))) (.var 4))
      (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 4))
        (.neg (.mul (.mul (.mul (.var 0) (.var 3)) (.var 3)) (.var 4))))
      (by decide)
      (fun | 0 => r.val | 1 => d.val | 2 => (N pp).val | 3 => (N p).val
           | _ => exterior w K extent i.val i.property)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg _ _)))
  change (F).B (E r p) ((F).sub (E d p) (J (N p))) ≈ _
  exact Q'.eqv_trans _ _ _ ((F).B_add_right (E r p) (E d p) ((F).neg (J (N p))))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst
      (Q'.eqv_trans _ _ _ ((F).B_neg_right (E r p) (J (N p)))
        (Q'.neg_eqv_congr _ _ hsecond))) hv.symm)

set_option maxHeartbeats 2000000 in
/-- The test's actual squared cost has one MORE normalizer than its cross-pair. -/
theorem normCost_variance (p : (F).V) :
    normCost hw0 hw1 K extent hK i p ≈
      varianceFunctional hw0 hw1 K extent hK i
        (normalizerState hw0 hw1 K extent hK i) p := by
  let d := normalizerState hw0 hw1 K extent hK i
  have hz : (F).B (J (N p)) (t p) ≈ 0 :=
    polynomialResidual_probe_zero hw0 hw1 K extent hK i p (N p)
  have hc : normCost hw0 hw1 K extent hK i p ≈ (F).B (E d p) (t p) := by
    change (F).B ((F).sub (E d p) (J (N p))) (t p) ≈ _
    exact Q'.eqv_trans _ _ _ ((F).B_add_left (E d p) ((F).neg (J (N p))) (t p))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ ((F).B_neg_left (J (N p)) (t p))
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hz) (by decide : -(0 : Q') ≈ 0))))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.eqv_trans _ _ _ hc (exterior_variance_pair hw0 hw1 K extent hK i d p)

set_option maxHeartbeats 2000000 in
/-- Retain an arbitrary exterior insertion in the test's cost pairing. -/
theorem exterior_cost_pair (r : (G).V) (p : (F).V) :
    (F).B (E r (t p)) (t p) ≈
      varianceFunctional hw0 hw1 K extent hK i
        (normalizerMap hw0 hw1 K extent hK i.val i.property r) p := by
  let d := normalizerState hw0 hw1 K extent hK i
  let rd := normalizerMap hw0 hw1 K extent hK i.val i.property r
  let rn : (G).V := ⟨polyMul r.val (N p).val, supported_polyMul r.property (N p).property⟩
  have hJd : (J rd).val = polyMul (J r).val (J d).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val d.val
  have hJn : (J rn).val = polyMul (J r).val (J (N p)).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val (N p).val
  have he : (F).veq (E r (t p)) ((F).sub (E rd p) (J rn)) := by
    change RatPolyCoeffEqv
      (polyMul (J r).val
        (polyAdd (polyMul (J d).val p.val) (polySmul (-1) (J (N p)).val)))
      (polyAdd (polyMul (J rd).val p.val) (polySmul (-1) (J rn).val))
    rw [hJd, hJn]
    exact (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_assoc _ _ _).symm
        (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
  have hz : (F).B (J rn) (t p) ≈ 0 :=
    polynomialResidual_probe_zero hw0 hw1 K extent hK i p rn
  have hc : (F).B ((F).sub (E rd p) (J rn)) (t p) ≈ (F).B (E rd p) (t p) :=
    Q'.eqv_trans _ _ _ ((F).B_add_left (E rd p) ((F).neg (J rn)) (t p))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ ((F).B_neg_left (J rn) (t p))
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hz) (by decide : -(0 : Q') ≈ 0))))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.eqv_trans _ _ _ ((F).B_congr_left (t p) he)
    (Q'.eqv_trans _ _ _ hc (exterior_variance_pair hw0 hw1 K extent hK i rd p))

set_option maxHeartbeats 2000000 in
/-- Squared norm of an exterior-weighted kernel test: exactly H[B*r^2*D*Phi]. -/
theorem exterior_test_cost (r : (G).V) (p : (F).V) :
    (F).B (E r (t p)) (E r (t p)) ≈
      varianceFunctional hw0 hw1 K extent hK i
        (normalizerMap hw0 hw1 K extent hK i.val i.property
          ⟨polyMul r.val r.val, supported_polyMul r.property r.property⟩) p := by
  let rr : (G).V := ⟨polyMul r.val r.val, supported_polyMul r.property r.property⟩
  have hJ : (J rr).val = polyMul (J r).val (J r).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val r.val
  have he : (F).B (E r (t p)) (E r (t p)) ≈ (F).B (E rr (t p)) (t p) := by
    change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
    dsimp only [exteriorSeed]
    rw [hJ]
    exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1))
      (by decide) (fun | 0 => (J r).val | _ => (t p).val)).mul_right _)
  exact Q'.eqv_trans _ _ _ he (exterior_cost_pair hw0 hw1 K extent hK i rr p)

set_option maxHeartbeats 2000000 in
/-- The optimizer's cross-pair for seed J(r)*p and original input p. -/
theorem exteriorSeed_pairValue (r : (G).V) (p : (F).V) :
    pairValue hw0 hw1 K extent hK i (E r p) p ≈
      varianceFunctional hw0 hw1 K extent hK i r p := by
  have hr := polynomialResidual_exteriorSeed_rad hw0 hw1 K extent hK i r p
  have he : (F).B p (E r (t p)) ≈ (F).B (E r p) (t p) := by
    change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
    exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2))
      (by decide) (fun | 0 => p.val | 1 => (J r).val | _ => (t p).val)).mul_right _)
  exact Q'.eqv_trans _ _ _ ((F).B_welldef ((F).rad_refl p) hr)
    (Q'.eqv_trans _ _ _ he (exterior_variance_pair hw0 hw1 K extent hK i r p))

/-- The optimizer's actual cost for the SAME exterior-modulated seed. -/
theorem exteriorSeed_normCost (r : (G).V) (p : (F).V) :
    normCost hw0 hw1 K extent hK i (E r p) ≈
      varianceFunctional hw0 hw1 K extent hK i
        (normalizerMap hw0 hw1 K extent hK i.val i.property
          ⟨polyMul r.val r.val, supported_polyMul r.property r.property⟩) p := by
  have hr := polynomialResidual_exteriorSeed_rad hw0 hw1 K extent hK i r p
  exact Q'.eqv_trans _ _ _ ((F).B_welldef hr hr)
    (exterior_test_cost hw0 hw1 K extent hK i r p)

#print axioms normalizerState
#print axioms varianceFunctional
#print axioms exterior_variance_pair
#print axioms normCost_variance
#print axioms exterior_cost_pair
#print axioms exterior_test_cost
#print axioms exteriorSeed_pairValue
#print axioms exteriorSeed_normCost

end YMGap.Continuum.BF4ExactSlabStarPolynomialCost
