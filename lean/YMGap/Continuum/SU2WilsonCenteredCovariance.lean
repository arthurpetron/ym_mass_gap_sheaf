/-
# OWN centering of the actual finite Wilson covariance

Extract the two distinct `1+chi` insertions from the SAME nodup plaquette
product, expand the two centered characters, and cancel the SAME positive
partition. The resulting covariance is exactly the expression consumed by
`SU2ClusterBridge.hcov` after its geometric roots are substituted.

This completes only the finite centering/cancellation ingredient. Equality
of reflected/translated one-point means, the RP identification, positive-time
support and the time-shift join remain separate obligations. No decay or
continuum statement is asserted here.
-/

import YMGap.Continuum.SU2WilsonObsExtraction
import YMGap.Continuum.SU2TorusRPBil
import YMGap.Continuum.RationalConnectedResponse

namespace YMGap.Continuum.SU2WilsonCenteredCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2HaarAlgebra
  (PE pe_haar pe_trans pe_symm pe_mulL pe_mulR pe_comm pe_assoc pe_one pe_const)
open YMGap.Continuum.SU2TorusRPBil (mul_app_l mul_smul_l)
open YMGap.Continuum.BF4CompactActionCPOrder
  (quaternionHaar_append quaternionHaar_polySmul)
open YMGap.Continuum.SU2WilsonObsActivity (chi)
open YMGap.Continuum.SU2WilsonTrunc (obsTK ZW)
open YMGap.Continuum.SU2WilsonObsExtraction (obsTK_extract)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-- The actual finite Wilson weight, with no selected observable roots. -/
def weight (links : List Z4Link) (N K : Nat) (P : List Z4Plaq) : RatPoly :=
  prodPoly (obsTK links N K []) P

/-- The rational OWN mean, using the actual unchanged partition reciprocal.
The theorems below require positivity before using its cancellation law. -/
def ownMean (links : List Z4Link) (N K : Nat) (P : List Z4Plaq)
    (p : Z4Plaq) : Q' :=
  quaternionHaar links.length (polyMul (chi links N p) (weight links N K P)) *
    Q'.recip (ZW links N K P [])

/-- The genuine character centered at its OWN mean for this Wilson weight. -/
def centeredCharacter (links : List Z4Link) (N K : Nat) (P : List Z4Plaq)
    (p : Z4Plaq) : RatPoly :=
  polyAdd (chi links N p) (polySmul (-(ownMean links N K P p)) polyOne)

private theorem one_add_haar (n : Nat) (X Y : RatPoly) :
    quaternionHaar n (polyMul (polyAdd polyOne X) Y) ≈
      quaternionHaar n Y + quaternionHaar n (polyMul X Y) := by
  change quaternionHaar n (polyMul (polyOne ++ X) Y) ≈ _
  rw [mul_app_l]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr' (pe_haar n (pe_const n 1 (Q'.eqv_refl 1) Y))
      (Q'.eqv_refl _))

private theorem affine_haar (n : Nat) (X Y : RatPoly) (c : Q') :
    quaternionHaar n (polyMul (polyAdd X (polySmul c polyOne)) Y) ≈
      quaternionHaar n (polyMul X Y) + c * quaternionHaar n Y := by
  change quaternionHaar n (polyMul (X ++ polySmul c polyOne) Y) ≈ _
  rw [mul_app_l]
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) ?_)
  exact Q'.eqv_trans _ _ _ (pe_haar n (mul_smul_l n c polyOne Y))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n c _)
      (Q'.mul_eqv_congr_left _ _ _
        (pe_haar n (pe_const n 1 (Q'.eqv_refl 1) Y))))

private theorem affine_pair_haar (n : Nat) (X Y W : RatPoly) (a b : Q') :
    quaternionHaar n (polyMul
      (polyMul (polyAdd X (polySmul a polyOne))
        (polyAdd Y (polySmul b polyOne))) W) ≈
      (quaternionHaar n (polyMul (polyMul X Y) W) +
        b * quaternionHaar n (polyMul X W)) +
      a * (quaternionHaar n (polyMul Y W) + b * quaternionHaar n W) := by
  let Yb := polyAdd Y (polySmul b polyOne)
  refine Q'.eqv_trans _ _ _ (pe_haar n (pe_assoc n _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (affine_haar n X (polyMul Yb W) a) ?_
  refine Q'.add_eqv_congr' ?_
    (Q'.mul_eqv_congr_left _ _ _ (affine_haar n Y W b))
  have he : PE n (polyMul X (polyMul Yb W)) (polyMul Yb (polyMul X W)) :=
    pe_trans n (pe_symm n (pe_assoc n X Yb W))
      (pe_trans n (pe_mulR n W (pe_comm n X Yb)) (pe_assoc n Yb X W))
  refine Q'.eqv_trans _ _ _ (pe_haar n he)
    (Q'.eqv_trans _ _ _ (affine_haar n Y (polyMul X W) b) ?_)
  exact Q'.add_eqv_congr' (pe_haar n
    (pe_trans n (pe_symm n (pe_assoc n Y X W))
      (pe_mulR n W (pe_comm n Y X)))) (Q'.eqv_refl _)

/-- A root occurring once in the actual plaquette product inserts `1+chi`. -/
theorem single_insertion (links : List Z4Link) (N K : Nat)
    (P : List Z4Plaq) (p : Z4Plaq) (hP : P.Nodup) (hp : p ∈ P) :
    ZW links N K P [p] ≈ ZW links N K P [] +
      quaternionHaar links.length (polyMul (chi links N p) (weight links N K P)) :=
  Q'.eqv_trans _ _ _
    (pe_haar _ (obsTK_extract links N K P [] p hP hp List.not_mem_nil))
    (one_add_haar _ _ _)

/-- Two distinct physical roots are extracted from the SAME product once each. -/
theorem pair_insertion (links : List Z4Link) (N K : Nat)
    (P : List Z4Plaq) (p q : Z4Plaq)
    (hP : P.Nodup) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ZW links N K P [p,q] ≈
      (ZW links N K P [] +
        quaternionHaar links.length (polyMul (chi links N q) (weight links N K P))) +
      (quaternionHaar links.length (polyMul (chi links N p) (weight links N K P)) +
        quaternionHaar links.length
          (polyMul (polyMul (chi links N p) (chi links N q)) (weight links N K P))) := by
  have hpn : p ∉ [q] := by
    intro h
    exact hpq (List.mem_singleton.mp h)
  have he := pe_trans links.length
    (obsTK_extract links N K P [q] p hP hp hpn)
    (pe_mulL links.length _
      (obsTK_extract links N K P [] q hP hq List.not_mem_nil))
  refine Q'.eqv_trans _ _ _ (pe_haar _ he) ?_
  refine Q'.eqv_trans _ _ _ (one_add_haar _ _ _) ?_
  refine Q'.add_eqv_congr' (one_add_haar _ _ _) ?_
  have hs : PE links.length
      (polyMul (chi links N p)
        (polyMul (polyAdd polyOne (chi links N q)) (weight links N K P)))
      (polyMul (polyAdd polyOne (chi links N q))
        (polyMul (chi links N p) (weight links N K P))) :=
    pe_trans _ (pe_symm _ (pe_assoc _ _ _ _))
      (pe_trans _ (pe_mulR _ _ (pe_comm _ _ _)) (pe_assoc _ _ _ _))
  refine Q'.eqv_trans _ _ _ (pe_haar _ hs)
    (Q'.eqv_trans _ _ _ (one_add_haar _ _ _) ?_)
  exact Q'.add_eqv_congr' (Q'.eqv_refl _) (pe_haar _
    (pe_trans _ (pe_symm _ (pe_assoc _ _ _ _)) (pe_mulR _ _ (pe_comm _ _ _))))

private theorem centering_clear (z a b ab s : Q') (hz : z * s ≈ 1) :
    ((ab + (-(b*s))*a) + (-(a*s))*(b + (-(b*s))*z))*z ≈
      ab*z + -(a*b) := by
  let V := PolyExpr.var
  have hf := poly_identity_of_normal_eq
    (((V 3 + -(V 2*V 4)*V 1) +
      -(V 1*V 4)*(V 2 + -(V 2*V 4)*V 0))*V 0)
    ((V 3*V 0 + -(V 1*V 2*(V 0*V 4))) +
      (V 1*V 2*(V 0*V 4))*((V 0*V 4) + PolyExpr.const (-1)))
    (by decide) (fun | 0 => z | 1 => a | 2 => b | 3 => ab | _ => s)
  have ht : z*s + (-1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hz (Q'.eqv_refl _)) (by decide)
  have hproduct : a*b*(z*s) ≈ a*b :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hproduct))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht) (Q'.mul_zero_eqv _)))
    (poly_identity_of_normal_eq (V 0 + PolyExpr.const 0) (V 0)
      (by decide) (fun _ => ab*z + -(a*b))))

private theorem insertion_determinant_clear (z a b ab : Q') :
    ((z + b) + (a + ab))*z + -((z + a)*(z + b)) ≈ ab*z + -(a*b) := by
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    (((V 0 + V 2) + (V 1 + V 3))*V 0 + -((V 0 + V 1)*(V 0 + V 2)))
    (V 3*V 0 + -(V 1*V 2)) (by decide)
    (fun | 0 => z | 1 => a | 2 => b | _ => ab)

/-- Exact finite centered determinant: only the actual positive partition is
cancelled; neither marginal nor the signed joint moment is inverted. -/
theorem centered_covariance_clear (links : List Z4Link) (N K : Nat)
    (P : List Z4Plaq) (p q : Z4Plaq)
    (hP : P.Nodup) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hZ : (0 : Q') < ZW links N K P []) :
    quaternionHaar links.length (polyMul
      (polyMul (centeredCharacter links N K P p) (centeredCharacter links N K P q))
      (weight links N K P)) * ZW links N K P [] ≈
      ZW links N K P [p,q] * ZW links N K P [] +
        -(ZW links N K P [p] * ZW links N K P [q]) := by
  let z := ZW links N K P []
  let a := quaternionHaar links.length (polyMul (chi links N p) (weight links N K P))
  let b := quaternionHaar links.length (polyMul (chi links N q) (weight links N K P))
  let ab := quaternionHaar links.length
    (polyMul (polyMul (chi links N p) (chi links N q)) (weight links N K P))
  let s := Q'.recip z
  have hc : quaternionHaar links.length (polyMul
      (polyMul (centeredCharacter links N K P p) (centeredCharacter links N K P q))
      (weight links N K P)) * z ≈ ab*z + -(a*b) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (affine_pair_haar links.length (chi links N p) (chi links N q)
          (weight links N K P) (-(a*s)) (-(b*s))))
      (centering_clear z a b ab s (Q'.mul_recip_eqv z hZ))
  have hd : ZW links N K P [p,q] * z +
      -(ZW links N K P [p] * ZW links N K P [q]) ≈ ab*z + -(a*b) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (pair_insertion links N K P p q hP hp hq hpq))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (single_insertion links N K P p hP hp))
        (Q'.mul_eqv_congr_left _ _ _ (single_insertion links N K P q hP hq))))) ?_
    exact insertion_determinant_clear z a b ab
  exact Q'.eqv_trans _ _ _ hc (Q'.eqv_symm hd)

private theorem cancel_partition (u v z s : Q') (hz : z*s ≈ 1)
    (h : u*z ≈ v*z) : u ≈ v := by
  have hc (x : Q') : (x*z)*s ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hc u))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (hc v))

/-- The actual unnormalized OWN-centered Haar integral is `Z` times the
`1+chi` covariance used by `SU2ClusterBridge`, with its literal reciprocal. -/
theorem centered_covariance (links : List Z4Link) (N K : Nat)
    (P : List Z4Plaq) (p q : Z4Plaq)
    (hP : P.Nodup) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hZ : (0 : Q') < ZW links N K P []) :
    quaternionHaar links.length (polyMul
      (polyMul (centeredCharacter links N K P p) (centeredCharacter links N K P q))
      (weight links N K P)) ≈
      ZW links N K P [] *
        (ZW links N K P [p,q] * Q'.recip (ZW links N K P []) +
          -((ZW links N K P [p] * Q'.recip (ZW links N K P [])) *
            (ZW links N K P [q] * Q'.recip (ZW links N K P [])))) := by
  let z := ZW links N K P []
  let s := Q'.recip z
  let c := ZW links N K P [p,q]*s +
    -((ZW links N K P [p]*s)*(ZW links N K P [q]*s))
  have hz : z*s ≈ 1 := Q'.mul_recip_eqv z hZ
  refine cancel_partition _ (z*c) z s hz ?_
  refine Q'.eqv_trans _ _ _
    (centered_covariance_clear links N K P p q hP hp hq hpq hZ) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ ?_
    (RationalConnectedResponse.covariance_clear z (ZW links N K P [p])
      (ZW links N K P [q]) (ZW links N K P [p,q]) s hz))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq ((V 0*V 1)*V 0) (V 1*(V 0*V 0))
    (by decide) (fun | 0 => z | _ => c)

end YMGap.Continuum.SU2WilsonCenteredCovariance

#print axioms YMGap.Continuum.SU2WilsonCenteredCovariance.single_insertion
#print axioms YMGap.Continuum.SU2WilsonCenteredCovariance.pair_insertion
#print axioms YMGap.Continuum.SU2WilsonCenteredCovariance.centered_covariance_clear
#print axioms YMGap.Continuum.SU2WilsonCenteredCovariance.centered_covariance
