/-
# A positive spatial-only window for the full fringe projection

The denominator is exactly m_F=P_F(V), where V is the complete original
spatial weight and P_F integrates all inactive kinetic coordinates in place.
Projecting the existing spatial floor certificate supplies its positive
lower bound. A cap computed from this actual polynomial supplies its upper
bound. No terminal message or terminal depth enters either constant.

The reciprocal is a finite polynomial in m_F. It is independent of every
fringe coordinate, has a certified multiplier-square cap one, and has an
explicit geometric multiplier-error interval. The approximation rate can
depend on nome, cutoff and spatial width; it is not a physical gap or a
uniform estimate on the interacting active-coordinate sector.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (spatialFloorCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (fringeProject spatialFringeMass spatialFringeMass_supported spatialFringeMass_independent)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (corrector)
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse (corrector_independent)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight

private def familyCertificate (blocks : Nat) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < blocks) →
    {p : RatPoly} → SupportedQuaternionBlocks blocks p → Certificate blocks p →
      Certificate blocks (familyProject ids p)
  | [], _, _, _, P => P
  | i::ids, hi, _, hp, P =>
      familyCertificate blocks ids (fun j hj => hi j (List.mem_cons_of_mem i hj))
        (project_supported i hp) (project_certificate blocks i (hi i List.mem_cons_self) hp P)

private theorem family_cap (ids : List Nat) (c : Q') :
    RatPolyCoeffEqv (familyProject ids (cap c)) (cap c) :=
  familyProject_fixed ids (cap c) (fun i _ =>
    quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne i))

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks s hs

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The full original spatial product floor, before and after fringe integration. -/
def lower (w : Q') (_K width : Nat) : Q' :=
  (headFloor w)^(spatialFaces width).length

theorem lower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) : (0 : Q') < lower w K width :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

/-- Every original spatial factor is retained when the floor is projected. -/
def lowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width) (polyAdd (spatialFringeMass w K width)
      (polyNeg (cap (lower w K width)))) := by
  let ids := fringeBlocks width
  let c := lower w K width
  have P := familyCertificate (N width) ids (fringeBlocks_lt width)
    (supported_add (spatialWeight_supported w K width)
      (neg_supported (cap_supported (N width) c)))
    (spatialFloorCertificate hw0 hw1 K width hK)
  have he : RatPolyCoeffEqv
      (familyProject ids (polyAdd (spatialWeight w K width) (polyNeg (cap c))))
      (polyAdd (spatialFringeMass w K width) (polyNeg (cap c))) := by
    rw [familyProject_add]
    exact (RatPolyCoeffEqv.refl _).add
      ((familyProject_neg ids (cap c)).trans (RatPolyCoeffEqv.neg (family_cap ids c)))
  exact .ofCoeff he.symm P

/-- Computed from the projected ORIGINAL polynomial; no depth parameter. -/
def upper (w : Q') (K width : Nat) : Q' :=
  polynomialCap (spatialFringeMass w K width) + (lower w K width + 1)

theorem lower_le_upper (w : Q') (K width : Nat) :
    lower w K width ≤ upper w K width :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (polynomialCap_nonnegative (spatialFringeMass w K width)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem upper_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (_hK : headCutoff w ≤ K) : (0 : Q') < upper w K width :=
  Q'.pos_of_lt_of_le (lower_positive hw0 hw1 K width) (lower_le_upper w K width)

def upperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (_hK : headCutoff w ≤ K) :
    Certificate (N width) (polyAdd (cap (upper w K width))
      (polyNeg (spatialFringeMass w K width))) :=
  ((polynomialInterval (N width) (spatialFringeMass w K width)
    (spatialFringeMass_supported w K width)).raise (lower w K width+1)
      (Q'.zero_le_add _ _ (Q'.le_of_lt (lower_positive hw0 hw1 K width)) Q'.zero_le_one)).upper

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K)

/-- Approximation rate only; all finite spatial-window dependence stays visible. -/
def rate : Q' :=
  QuaternionHaarPositiveWindowInverse.radius (lower w K width) (upper w K width)
    (upper_positive hw0 hw1 K width hK)

theorem rate_nonnegative : (0 : Q') ≤ rate hw0 hw1 K width hK :=
  QuaternionHaarPositiveWindowInverse.radius_nonnegative
    (upper_positive hw0 hw1 K width hK) (lower_le_upper w K width)

theorem rate_lt_one : rate hw0 hw1 K width hK < (1 : Q') :=
  QuaternionHaarPositiveWindowInverse.radius_lt_one (lower_positive hw0 hw1 K width)
    (upper_positive hw0 hw1 K width hK)

/-- A finite polynomial in m_F, not a configuration-space reciprocal function. -/
def reciprocal (k : Nat) : RatPoly :=
  QuaternionHaarPositiveWindowInverse.reciprocal (spatialFringeMass w K width)
    (upper w K width) (upper_positive hw0 hw1 K width hK) k

theorem reciprocal_supported (k : Nat) :
    SupportedQuaternionBlocks (N width) (reciprocal hw0 hw1 K width hK k) :=
  QuaternionHaarPositiveWindowInverse.reciprocal_supported
    (spatialFringeMass_supported w K width) (upper w K width)
    (upper_positive hw0 hw1 K width hK) k

/-- Inverse polynomials do not reintroduce an integrated fringe coordinate. -/
theorem reciprocal_independent (k i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (reciprocal hw0 hw1 K width hK k) := by
  apply quaternionBlockIndependent_polySmul
  apply corrector_independent
  change QuaternionBlockIndependent i
    (polyAdd (polySmul _ (spatialFringeMass w K width)) (polyNeg polyOne))
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polySmul _ (spatialFringeMass_independent w K width i hi))
    (quaternionBlockIndependent_polyNeg (quaternionBlockIndependent_polyOne i))

/-- Coefficient-one multiplier norm control, supplied by an actual certificate. -/
def multiplierSquareCertificate (k : Nat) :
    Certificate (N width) (polyAdd polyOne (polyNeg (polyMul
      (polyMul (spatialFringeMass w K width) (reciprocal hw0 hw1 K width hK k))
      (polyMul (spatialFringeMass w K width) (reciprocal hw0 hw1 K width hK k))))) :=
  QuaternionHaarPositiveWindowInverse.multiplierSquareCertificate
    (spatialFringeMass_supported w K width) (lower_positive hw0 hw1 K width)
    (upper_positive hw0 hw1 K width hK) (lower_le_upper w K width)
    (lowerCertificate hw0 hw1 K width hK) (upperCertificate hw0 hw1 K width hK) k

/-- Explicit signed error interval for the same finite multiplier. -/
def multiplierErrorInterval (k : Nat) :
    Interval (N width) (polyAdd
      (polyMul (spatialFringeMass w K width) (reciprocal hw0 hw1 K width hK k))
      (polyNeg polyOne)) ((rate hw0 hw1 K width hK)^k) :=
  QuaternionHaarPositiveWindowInverse.multiplierErrorInterval
    (spatialFringeMass_supported w K width) (upper_positive hw0 hw1 K width hK)
    (lower_le_upper w K width) (lowerCertificate hw0 hw1 K width hK)
    (upperCertificate hw0 hw1 K width hK) k

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.lower_le_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.upper_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.upperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.rate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.rate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.rate_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.reciprocal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.reciprocal_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.reciprocal_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.multiplierSquareCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow.multiplierErrorInterval
