/-
# Positive windows for the actual conditional seed denominators

For the original odd marginal nu and m_i=P_i nu, both factors have the
constructed finite window [ell,u]. Their product has window [ell^2,u^2].
Every retained coordinate is allowed, including the kinetic fringe. No
independence of nu, product law for nu, or uniform-regulator estimate is used.
The intended consumer is the polynomial inverse of nu*m_i, used only to
construct exactly centered finite dual tests.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

/-- The denominator used by the seed algorithm, not by a physical transfer. -/
def denominator (w : Q') (K width n i : Nat) : RatPoly :=
  polyMul (marginalWeight w K width n) (project i (marginalWeight w K width n))

theorem denominator_supported (w : Q') (K width n i : Nat) :
    SupportedQuaternionBlocks (N width) (denominator w K width n i) :=
  supported_polyMul (marginalWeight_supported w K width n)
    (project_supported i (marginalWeight_supported w K width n))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem cap_supported (blocks : Nat) (c : Q') : SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks r hr

private def projectLower {blocks : Nat} (i : Nat) (hi : i < blocks)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks blocks p)
    (P : Certificate blocks (polyAdd p (polyNeg (cap c)))) :
    Certificate blocks (polyAdd (project i p) (polyNeg (cap c))) := by
  have h : RatPolyCoeffEqv (project i (polyAdd p (polyNeg (cap c))))
      (polyAdd (project i p) (polyNeg (cap c))) := by
    rw [project_add]
    exact (RatPolyCoeffEqv.refl _).add
      ((project_neg i _).trans (RatPolyCoeffEqv.neg (project_cap i c)))
  exact .ofCoeff h.symm (project_certificate blocks i hi
    (supported_add hp (support_neg (cap_supported blocks c))) P)

private def projectUpper {blocks : Nat} (i : Nat) (hi : i < blocks)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks blocks p)
    (P : Certificate blocks (polyAdd (cap c) (polyNeg p))) :
    Certificate blocks (polyAdd (cap c) (polyNeg (project i p))) := by
  have h : RatPolyCoeffEqv (project i (polyAdd (cap c) (polyNeg p)))
      (polyAdd (cap c) (polyNeg (project i p))) := by
    rw [project_add]
    exact (project_cap i c).add (project_neg i p)
  exact .ofCoeff h.symm (project_certificate blocks i hi
    (supported_add (cap_supported blocks c) (support_neg hp)) P)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n i : Nat) (hi : i < N width)

def conditionalLowerCertificate :
    Certificate (N width) (polyAdd (project i (marginalWeight w K width n))
      (polyNeg (cap (lower w K width n)))) :=
  projectLower i hi (marginalWeight_supported w K width n)
    (lowerCertificate hw0 hw1 K width hK n)

def conditionalUpperCertificate :
    Certificate (N width) (polyAdd (cap (upper w K width n))
      (polyNeg (project i (marginalWeight w K width n)))) :=
  projectUpper i hi (marginalWeight_supported w K width n)
    (upperCertificate hw0 hw1 K width hK n)

def denominatorLowerCertificate :
    Certificate (N width) (polyAdd (denominator w K width n i)
      (polyNeg (cap (lower w K width n * lower w K width n)))) := by
  let a := marginalWeight w K width n
  let m := project i a
  let ell := lower w K width n
  have hm := project_certificate (N width) i hi (marginalWeight_supported w K width n)
    (marginalCertificate hw0 hw1 K width hK n)
  have hp : RatPolyCoeffEqv (polyAdd (polyMul a m) (polyNeg (cap (ell*ell))))
      (polyAdd (polyMul (polyAdd a (polyNeg (cap ell))) m)
        (polyMul (cap ell) (polyAdd m (polyNeg (cap ell))))) :=
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul ell ell).symm))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
        (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
          (.mul (.var 2) (.add (.var 1) (.neg (.var 2)))))
        (by decide) (fun | 0 => a | 1 => m | _ => cap ell))
  exact .ofCoeff hp (((lowerCertificate hw0 hw1 K width hK n).mul hm).add
    ((Certificate.constant (N width) ell (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n))).mul
      (conditionalLowerCertificate hw0 hw1 K width hK n i hi)))

def denominatorUpperCertificate :
    Certificate (N width) (polyAdd (cap (upper w K width n * upper w K width n))
      (polyNeg (denominator w K width n i))) := by
  let a := marginalWeight w K width n
  let m := project i a
  let u := upper w K width n
  have hp : RatPolyCoeffEqv (polyAdd (cap (u*u)) (polyNeg (polyMul a m)))
      (polyAdd (polyMul (cap u) (polyAdd (cap u) (polyNeg a)))
        (polyMul a (polyAdd (cap u) (polyNeg m)))) :=
    (((cap_mul u u).symm).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1))))
        (.add (.mul (.var 2) (.add (.var 2) (.neg (.var 0))))
          (.mul (.var 0) (.add (.var 2) (.neg (.var 1)))))
        (by decide) (fun | 0 => a | 1 => m | _ => cap u))
  exact .ofCoeff hp
    (((Certificate.constant (N width) u (Q'.le_of_lt (upper_positive hw0 hw1 K width hK n))).mul
      (upperCertificate hw0 hw1 K width hK n)).add
      ((marginalCertificate hw0 hw1 K width hK n).mul
        (conditionalUpperCertificate hw0 hw1 K width hK n i hi)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.denominator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.denominator_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.conditionalLowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.conditionalUpperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.denominatorLowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow.denominatorUpperCertificate
