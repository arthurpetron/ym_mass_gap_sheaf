/-
# Original full-action comparison for a literal link-local polynomial

Only heat factors meeting the supplied link support are bounded. Every
detached face factor remains in the exact original Haar background. The
collar has at most six faces per supplied link; no uniform weak-coupling,
conditional-dynamics, or continuum claim is made here.
-/

import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

namespace YMGap.Continuum.BF4ExactSlabLocalSupportComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.SU2QuaternionBlockLocality

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def collar (extent : Nat) (links : List Z4Link) : List Nat :=
  collarIds extent links [] (slabPhysicalFaceEdges extent)

def detached (extent : Nat) (links : List Z4Link) : List Nat :=
  detachedIds extent links [] (slabPhysicalFaceEdges extent)

def collarCount (extent : Nat) (links : List Z4Link) : Nat :=
  (collar extent links).length

def background (w : Q') (K extent : Nat) (links : List Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (detached extent links)

def fullWeight (w : Q') (K extent : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

theorem collarCount_le (extent : Nat) (links : List Z4Link) :
    collarCount extent links ≤ 6*links.length := by
  simpa only [collarCount, collar, Nat.mul_zero, Nat.add_zero] using
    full_collarIds_length_le extent links []

theorem collar_physical {extent : Nat} {links : List Z4Link} {id : Nat}
    (hi : id ∈ collar extent links) : id ∈ slabPhysicalFaceEdges extent :=
  collar_mem hi

theorem detached_physical {extent : Nat} {links : List Z4Link} {id : Nat}
    (hi : id ∈ detached extent links) : id ∈ slabPhysicalFaceEdges extent :=
  detached_mem hi

theorem links_detached_disjoint (extent : Nat) (links : List Z4Link) :
    LinksDisjoint links (faceLinks extent (detached extent links)) := by
  simpa only [detached, faceLinks, List.flatMap_nil, List.append_nil] using
    detached_disjoint extent links [] (slabPhysicalFaceEdges extent)

def background_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link) :
    Certificate (blocks extent) (background w K extent links) :=
  headProduct_certificate hw0 hw1 K extent hK _ (fun _ hi => detached_physical hi)

theorem fullWeight_split (w : Q') (K extent : Nat) (links : List Z4Link) :
    RatPolyCoeffEqv (fullWeight w K extent)
      (polyMul (background w K extent links)
        (polynomialProduct (faceHeatPolynomial w K extent) (collar extent links))) :=
  (polynomialProduct_perm _ (region_partition extent links [] _).symm).trans
    ((polynomialProduct_append _ (collar extent links) (detached extent links)).trans
      (RatPolyCoeffEqv.mul_comm _ _))

theorem background_factorization (w : Q') (K extent : Nat) (links : List Z4Link)
    {p : RatPoly} (hp : LinkLocal extent links p)
    (hs : SupportedQuaternionBlocks (blocks extent) p) :
    quaternionHaar (blocks extent) (polyMul (polyMul p p) (background w K extent links)) ≈
      quaternionHaar (blocks extent) (polyMul p p) *
        quaternionHaar (blocks extent) (background w K extent links) :=
  haar_product (supported_polyMul hs hs) (heatProduct_supported w K extent _)
    (linkLocal_disjoint (hp.mul hp) (heatProduct_local w K extent _)
      (links_detached_disjoint extent links))

/-- The actual full face product, with only the collar bounded and the
detached original action untouched. -/
theorem weighted_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
    {q : RatPoly} (P : Certificate (blocks extent) q) :
    (headFloor w)^collarCount extent links *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) ≤
      quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≤
      (prefixCap w)^collarCount extent links *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) := by
  have H := headProduct_weighted_floor hw0 hw1 K extent hK
    (P.mul (background_certificate hw0 hw1 K extent hK links))
    (collar extent links) (fun _ hi => collar_physical hi)
  have U := headProduct_weighted_upper hw0 hw1 K extent
    (P.mul (background_certificate hw0 hw1 K extent hK links))
    (collar extent links) (fun _ hi => collar_physical hi)
  have he : quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≈
      quaternionHaar (blocks extent)
        (polyMul (polyMul q (background w K extent links))
          (polynomialProduct (faceHeatPolynomial w K extent) (collar extent links))) :=
    haar_of_coeff (((RatPolyCoeffEqv.refl q).mul (fullWeight_split w K extent links)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact ⟨Q'.le_trans' _ _ _ H (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) U⟩

/-- A square localized on literal links has a two-sided original-action
comparison in which the Haar background is factored exactly. -/
theorem local_squared_norm_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
    {p : RatPoly} (hp : LinkLocal extent links p)
    (hs : SupportedQuaternionBlocks (blocks extent) p) :
    (headFloor w)^collarCount extent links *
        (quaternionHaar (blocks extent) (polyMul p p) *
          quaternionHaar (blocks extent) (background w K extent links)) ≤
      quaternionHaar (blocks extent) (polyMul (polyMul p p) (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul (polyMul p p) (fullWeight w K extent)) ≤
      (prefixCap w)^collarCount extent links *
        (quaternionHaar (blocks extent) (polyMul p p) *
          quaternionHaar (blocks extent) (background w K extent links)) := by
  have H := weighted_bounds hw0 hw1 K extent hK links (Certificate.square p hs)
  have he := background_factorization w K extent links hp hs
  exact ⟨Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm he))) H.1,
    Q'.le_trans' _ _ _ H.2
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he))⟩

/-- The same collar comparison for the original partition function. -/
theorem partition_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link) :
    (headFloor w)^collarCount extent links *
        quaternionHaar (blocks extent) (background w K extent links) ≤
      quaternionHaar (blocks extent) (fullWeight w K extent) ∧
    quaternionHaar (blocks extent) (fullWeight w K extent) ≤
      (prefixCap w)^collarCount extent links *
        quaternionHaar (blocks extent) (background w K extent links) := by
  have H := weighted_bounds hw0 hw1 K extent hK links (Certificate.one (blocks extent))
  have hb := haar_of_coeff («blocks» := blocks extent)
    (RatPolyCoeffEqv.one_mul (background w K extent links))
  have hf := haar_of_coeff («blocks» := blocks extent)
    (RatPolyCoeffEqv.one_mul (fullWeight w K extent))
  exact ⟨Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hb)))
      (Q'.le_trans' _ _ _ H.1 (Q'.le_of_eqv hf)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hf)
      (Q'.le_trans' _ _ _ H.2
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hb)))⟩

end YMGap.Continuum.BF4ExactSlabLocalSupportComparison

#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.collar
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.detached
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.collarCount
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.background
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.fullWeight
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.collarCount_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.collar_physical
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.detached_physical
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.links_detached_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.background_certificate
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.fullWeight_split
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.background_factorization
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.weighted_bounds
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.local_squared_norm_bounds
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportComparison.partition_bounds
