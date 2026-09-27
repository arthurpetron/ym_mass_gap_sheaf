/-
# Near-one original-action comparison with a detached two-link background

Only the at-most-twelve original faces meeting two selected links are
estimated. Every other original factor remains in a shared positive
background. The inserted test is arbitrary: spectator dependence is NOT
excluded. Bounds hold at every heat cutoff and extent under explicit
small-nome guards. This is a quadratic-form comparison, not yet a signed
conditional-pair estimate, a dynamics gap, or continuum scaling control.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
import YMGap.Continuum.BF4ExactSlabStarFullActionProbe

namespace YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.GNSQuotient

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

local notation "lo" => (1 : Q') + -heatRemainderBound w
local notation "up" => (1 : Q') + heatRemainderBound w

include hw0 hw1 hsmall hdelta in
/-- The original positive background may contain every spectator variable. -/
theorem faceProduct_weighted_lower (K extent : Nat) {p : RatPoly}
    (P : Certificate (blocks extent) p) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      lo^ids.length * quaternionHaar (blocks extent) p ≤
        quaternionHaar (blocks extent)
          (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids))
  | [], _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))
  | id :: ids, hi => by
      have ht : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent :=
        fun j hj => hi j (List.mem_cons_of_mem id hj)
      have h := insertFace_lower hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K
        (P.mul (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids ht))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
          (faceProduct_weighted_lower K extent P ids ht) (Q'.sub_nonneg_of_le hdelta))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
            ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
              ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)))))))

include hw0 hw1 hsmall hdelta in
/-- The matching upper comparison uses exactly the same background. -/
theorem faceProduct_weighted_upper (K extent : Nat) {p : RatPoly}
    (P : Certificate (blocks extent) p) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      quaternionHaar (blocks extent)
          (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≤
        up^ids.length * quaternionHaar (blocks extent) p
  | [], _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  | id :: ids, hi => by
      have ht : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent :=
        fun j hj => hi j (List.mem_cons_of_mem id hj)
      have h := insertFace_upper hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K
        (P.mul (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids ht))
      have hup : (0 : Q') ≤ up := Q'.le_trans' _ _ _ Q'.zero_le_one
        (Q'.add_le_self_of_nonneg _ _ (remainder_nonnegative hw0))
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff
        ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
          ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)))))
        (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (faceProduct_weighted_upper K extent P ids ht) hup)
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- Constructed SAME detached original background, at every heat cutoff. -/
def small_background_certificate (K extent : Nat) (links : List Z4Link) :
    Certificate (blocks extent) (background w K extent links) :=
  faceProductCertificate hw0 hw1 hsmall hdelta K extent (detached extent links)
    (fun _ hi => detached_physical hi)

include hw0 hw1 hsmall hdelta in
/-- All collar faces, without any locality restriction on the test insertion. -/
theorem collar_weighted_bounds (K extent : Nat) (links : List Z4Link)
    {q : RatPoly} (P : Certificate (blocks extent) q) :
    lo^collarCount extent links *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) ≤
      quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≤
      up^collarCount extent links *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) := by
  have C := P.mul (small_background_certificate hw0 hw1 hsmall hdelta K extent links)
  have H := faceProduct_weighted_lower hw0 hw1 hsmall hdelta K extent C
    (collar extent links) (fun _ hi => collar_physical hi)
  have U := faceProduct_weighted_upper hw0 hw1 hsmall hdelta K extent C
    (collar extent links) (fun _ hi => collar_physical hi)
  have he := haar_of_coeff («blocks» := blocks extent)
    (((RatPolyCoeffEqv.refl q).mul (fullWeight_split w K extent links)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact ⟨Q'.le_trans' _ _ _ H (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) U⟩

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {i j : Nat}
    (hij : i ≤ j) : x^i ≤ x^j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
        (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (i+d))))

include hw0 hw1 hsmall hdelta in
/-- A fixed twelve-face budget, independent of extent, cutoff and test support. -/
theorem two_link_weighted_bounds (K extent : Nat) (left right : Z4Link)
    {q : RatPoly} (P : Certificate (blocks extent) q) :
    twoLinkLower w *
        quaternionHaar (blocks extent) (polyMul q (background w K extent [left,right])) ≤
      quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≤
      twoLinkUpper w *
        quaternionHaar (blocks extent) (polyMul q (background w K extent [left,right])) := by
  have hc : collarCount extent [left,right] ≤ 12 := collarCount_le extent [left,right]
  have H := collar_weighted_bounds hw0 hw1 hsmall hdelta K extent [left,right] P
  have hb := (P.mul (small_background_certificate hw0 hw1 hsmall hdelta K extent [left,right])).haar_nonnegative
  have hl1 : lo ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (remainder_nonnegative hw0))) (by decide)
  have hl := HKConvGen.pow_base_antitone (Q'.sub_nonneg_of_le hdelta) hl1 hc
  have hu := pow_exponent_mono (Q'.add_le_self_of_nonneg 1 _ (remainder_nonnegative hw0)) hc
  exact ⟨Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hl hb) H.1,
    Q'.le_trans' _ _ _ H.2 (Q'.mul_le_mul_of_nonneg_right _ _ _ hu hb)⟩

/-- The reference retains every face outside the two-link collar. Its dense
polynomial carrier is definitionally the original fullData carrier. -/
def twoLinkBackgroundData (K extent : Nat) (left right : Z4Link) : GNSData :=
  weightedGNSData (blocks extent) (background w K extent [left,right])
    (small_background_certificate hw0 hw1 hsmall hdelta K extent [left,right])

/-- Actual original form comparison for EVERY supported polynomial, including
arbitrary spectator dependence. No locality or mean-zero premise is used. -/
theorem two_link_fullData_bounds (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)
    (p : (fullData hwpos hwlt K extent hK).V) :
    let B0 := twoLinkBackgroundData hw0 hw1 hsmall hdelta K extent left right
    twoLinkLower w * B0.B p p ≤ (fullData hwpos hwlt K extent hK).B p p ∧
      (fullData hwpos hwlt K extent hK).B p p ≤ twoLinkUpper w * B0.B p p :=
  two_link_weighted_bounds hw0 hw1 hsmall hdelta K extent left right
    (Certificate.square p.val p.property)

#print axioms faceProduct_weighted_lower
#print axioms faceProduct_weighted_upper
#print axioms small_background_certificate
#print axioms collar_weighted_bounds
#print axioms two_link_weighted_bounds
#print axioms twoLinkBackgroundData
#print axioms two_link_fullData_bounds

end YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
