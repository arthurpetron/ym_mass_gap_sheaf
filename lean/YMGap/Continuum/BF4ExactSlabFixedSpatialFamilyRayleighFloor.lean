/-
# A finite-support Rayleigh floor for the original spatial family

The original positive odd marginal bounds the variance of a signed family
by four times the literal family length and coefficient-square sum. Combining
this with the original plaquette-family energy floor gives a division-free
necessary scale test. This is an unfiltered, finite-support statement, not a
filtered-sector or continuum spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_polySmul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order weighted_scale)
open YMGap.Continuum.QuaternionHaarFamilySquare (qListSum_congr)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance marginalVariance_pin marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper (weighted_sum_square_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect (plaquetteSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy (family_energy_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow (lower upper lower_positive upper_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks plaquette marginalWeight oddVariance
  normalizedEnergy
  YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage
  YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight

private theorem finite_sum_map {A : Type} (f : A → RatPoly) :
    ∀ xs : List A, finitePolySum f xs = polySum (xs.map f)
  | [] => rfl
  | _ :: xs => congrArg (polyAdd _) (finite_sum_map f xs)

private theorem sum_mono {A : Type} (xs : List A) (f g : A → Q')
    (h : ∀ x, x ∈ xs → f x ≤ g x) :
    qListSum (xs.map f) ≤ qListSum (xs.map g) := by
  induction xs with
  | nil => exact Q'.le_refl' 0
  | cons x xs ih =>
      exact Q'.add_le_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem indexed_sum_scale {A : Type} (f : A → Q') (C : Q') :
    ∀ xs : List A, qListSum (xs.map (fun x => C*f x)) ≈ C*listQSum f xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv C)
  | x :: xs =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (indexed_sum_scale f C xs))
        (Q'.eqv_symm (Q'.mul_add_eqv C (f x) (listQSum f xs)))

private theorem term_square_cap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (c : Q') (p : Z4Plaq) :
    quaternionHaar (N width)
      (polyMul (marginalWeight w K width n)
        (polyMul (polySmul c (characterPolynomial (plaquette width p).scalar 1))
          (polySmul c (characterPolynomial (plaquette width p).scalar 1)))) ≤
      (4*(c*c))*quaternionHaar (N width) (marginalWeight w K width n) := by
  let W := marginalWeight w K width n
  let f := characterPolynomial (plaquette width p).scalar 1
  let P := (plaquetteSquareBound width p).smul c
  have h := weighted_order (marginalCertificate hw0 hw1 K width hK n) P.certificate
  have he : quaternionHaar (N width) (polyMul W (cap ((c*c)*4))) ≈
      (4*(c*c))*quaternionHaar (N width) W :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.mul_comm W _).trans (cap_mul_left _ W)))
        (quaternionHaar_polySmul (N width) ((c*c)*4) W))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)

/-- The actual unfiltered odd variance of a signed or repeated family has
the literal finite-Cauchy loss. The source and center are unchanged. -/
theorem family_oddVariance_coefficient_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    oddVariance hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      (4*Q'.ofNat qs.length)*listQSum (fun p => c p*c p) qs := by
  let W := marginalWeight w K width n
  let z := quaternionHaar (N width) W
  let r := Q'.recipPos z (marginalMass_positive hw0 hw1 K width hK n)
  let f (p : Z4Plaq) := characterPolynomial (plaquette width p).scalar 1
  let ps := qs.map fun p => polySmul (c p) (f p)
  let S := listQSum (fun p => c p*c p) qs
  have R := marginalCertificate hw0 hw1 K width hK n
  have hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks (N width) p := by
    intro p hp
    obtain ⟨face, _, rfl⟩ := List.mem_map.mp hp
    exact ((plaquetteSquareBound width face).smul (c face)).support
  have hc := weighted_sum_square_le R ps hs
  simp only [ps, List.length_map] at hc
  have ht : qListSum (ps.map fun p => quaternionHaar (N width) (polyMul W (polyMul p p))) ≤
      qListSum (qs.map fun p => (4*(c p*c p))*z) := by
    simpa only [ps, List.map_map, Function.comp_def] using
      (sum_mono qs
        (fun p => quaternionHaar (N width)
          (polyMul W (polyMul (polySmul (c p) (f p)) (polySmul (c p) (f p)))))
        (fun p => (4*(c p*c p))*z)
        (fun p _ => term_square_cap hw0 hw1 K width hK n (c p) p))
  have hsum : qListSum (qs.map fun p => (4*(c p*c p))*z) ≈ (4*S)*z :=
    Q'.eqv_trans _ _ _
      (qListSum_congr qs _ _ (fun p _ =>
        poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.var 1))
          (.mul (.mul (.const 4) (.var 1)) (.mul (.var 0) (.var 0)))
          (by decide) (fun | 0 => c p | _ => z)))
      (Q'.eqv_trans _ _ _ (indexed_sum_scale (fun p => c p*c p) (4*z) qs)
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (.mul (.mul (.const 4) (.var 1)) (.var 0))
          (by decide) (fun | 0 => z | _ => S)))
  have hraw : quaternionHaar (N width)
      (polyMul W (polyMul (spatialSpan width c qs) (spatialSpan width c qs))) ≤
      Q'.ofNat qs.length*((4*S)*z) := by
    have hp : spatialSpan width c qs = polySum ps :=
      finite_sum_map (fun p => polySmul (c p) (f p)) qs
    rw [hp]
    exact Q'.le_trans' _ _ _ hc
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ht (Q'.ofNat_nonneg _))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hsum)))
  have hvar : normalizedVariance (N width) W (spatialSpan width c qs)
      (marginalMass_positive hw0 hw1 K width hK n) ≤
      normalizedMoment (N width) W
        (polyMul (spatialSpan width c qs) (spatialSpan width c qs))
        (marginalMass_positive hw0 hw1 K width hK n) := by
    unfold normalizedVariance
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _
        (Q'.neg_le_neg (SumOfSquares.q_mul_self_nonneg _)))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.const 0))) (.var 0)
        (by decide) (fun _ => normalizedMoment (N width) W
          (polyMul (spatialSpan width c qs) (spatialSpan width c qs))
          (marginalMass_positive hw0 hw1 K width hK n))))
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos z (marginalMass_positive hw0 hw1 K width hK n)))
  have hcancel : (Q'.ofNat qs.length*((4*S)*z))*r ≈ (4*Q'.ofNat qs.length)*S :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.mul (.const 4) (.var 1)) (.var 2))) (.var 3))
        (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => Q'.ofNat qs.length | 1 => S | 2 => z | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_recipPos_eqv z (marginalMass_positive hw0 hw1 K width hK n))))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv S)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (marginalVariance_pin hw0 hw1 K width hK n _)))
    (Q'.le_trans' _ _ _ hvar
      (Q'.le_trans' _ _ _ hnorm (Q'.le_of_eqv hcancel)))

/-- A division-free lower energy bound for the same original unfiltered
signed family. It is finite-support and fixed-nome, not a scaling gap. -/
theorem family_energy_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    (c : Z4Plaq → Q') :
    lower w * oddVariance hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      (2400*upper w*Q'.ofNat qs.length)*
        normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) := by
  let S := listQSum (fun p => c p*c p) qs
  let V := oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)
  let E := normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs)
  have hv := family_oddVariance_coefficient_cap hw0 hw1 K width hK n qs c
  have he := family_energy_floor hw0 hw1 K width hK n qs hn hqs c
  have ha := Q'.mul_le_mul_of_nonneg_left _ _ (lower w) hv
    (Q'.le_of_lt (lower_positive hw0 hw1))
  have hb := Q'.mul_le_mul_of_nonneg_left _ _ (4*Q'.ofNat qs.length) he
    (Q'.mul_nonneg _ _ (by decide) (Q'.ofNat_nonneg _))
  exact Q'.le_trans' _ _ _ ha
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.const 4) (.var 1)) (.var 2)))
        (.mul (.mul (.const 4) (.var 1)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => lower w | 1 => Q'.ofNat qs.length | _ => S)))
      (Q'.le_trans' _ _ _ hb
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0))
            (.mul (.mul (.const 600) (.var 1)) (.var 2)))
          (.mul (.mul (.mul (.const 2400) (.var 1)) (.var 0)) (.var 2))
          (by decide) (fun | 0 => Q'.ofNat qs.length | 1 => upper w | _ => E)))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor.family_oddVariance_coefficient_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor.family_energy_variance_floor
