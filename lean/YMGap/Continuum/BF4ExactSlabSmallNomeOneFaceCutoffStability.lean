/-
EARLY-cutoff normalized stability of ONE ORIGINAL shared-link heat factor.

For 0 <= w <= 1/2 and inclusive K >= 1, the sharp actual character tail
has cap (81/2272)*(1/72)^(K-1). The produced early floor 1055/2272 pays it
relative to the later original partition. Both OWN endpoint partitions
are retained until the existing rational determinant cancellation.
The spectator is an actual finite original heat product with independently
specified occurrence cutoffs >= 1; its positivity and strict mass are
constructed, not assumed. Repeated faces/shared links are allowed.
No headCutoff/relativeCutoff consumer is changed. This is one-face finite
cutoff control, not a volume-uniform telescope, OS norm or scaling result.
The nome-sensitive refinement retains the actual label-two head 9*w^8;
both estimates use the SAME early floor and normalized cancellation proof.
-/

import YMGap.Continuum.QuaternionHaarSmallNomeHeatCertificate
import YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation

namespace YMGap.Continuum.BF4ExactSlabSmallNomeOneFaceCutoffStability

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
  (faceScalar faceHeatTerm faceHeatTail faceHeatPolynomial_cutoff_append)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_slabPlaquette)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (supported_slabPlaquette)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm termInterval)
open YMGap.Continuum.QuaternionHaarSmallNomeHeatCertificate
  (floor floor_positive faceFloorCertificate faceCertificate)
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (floor_insertion)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
  (half sharpTailRatio sharpTailRatio_nonnegative labelTwoHead allLabelTailBudget
    labelTwo_majorant_le pointwiseHeatMajorant pointwiseHeatMajorant_succ_le
    exact_geometric_closure)
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment)
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
  (slabPhysicalFaceEdges slabPlaquetteAt_mem)

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Actual sharp finite-tail cap after inclusive cutoff K. -/
def tailCap (K : Nat) : Q' := allLabelTailBudget * sharpTailRatio ^ (K-1)

/-- The same cap relative to the PRODUCED original factor floor. -/
def relativeTailCap (K : Nat) : Q' :=
  Q'.mkPos 81 1055 (by decide) * sharpTailRatio ^ (K-1)

theorem relativeTailCap_nonnegative (K : Nat) : (0 : Q') ≤ relativeTailCap K :=
  Q'.le_of_lt (Q'.mul_pos (by decide :
      (0 : Q') < Q'.mkPos 81 1055 (by decide))
    (HKPos.pow_pos (by decide : (0 : Q') < sharpTailRatio) (K-1)))

theorem tailCap_relative_floor (K : Nat) : tailCap K ≈ relativeTailCap K * floor := by
  unfold tailCap relativeTailCap
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide :
      allLabelTailBudget ≈ Q'.mkPos 81 1055 (by decide) * floor))
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun
        | 0 => Q'.mkPos 81 1055 (by decide)
        | 1 => floor
        | _ => sharpTailRatio ^ (K-1)))

/-- Every finite ORIGINAL majorant tail, starting exactly at K+1. -/
theorem shifted_majorant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K : Nat) (hK : 1 ≤ K) (L : Nat) :
    finSum (fun j => pointwiseHeatMajorant w (K+1+j)) L ≤ tailCap K := by
  let r := sharpTailRatio
  let p := r ^ (K-1)
  have hp : (0 : Q') ≤ p := Q'.le_of_lt
    (HKPos.pow_pos (by decide : (0 : Q') < sharpTailRatio) (K-1))
  have hdom := CharacterTail.geom_dom
    (fun j => pointwiseHeatMajorant w (2+j)) labelTwoHead r
    sharpTailRatio_nonnegative
    (by simpa only [Nat.add_zero] using labelTwo_majorant_le hw0 hw)
    (fun j => by
      change pointwiseHeatMajorant w (2+(j+1)) ≤ r * pointwiseHeatMajorant w (2+j)
      rw [show 2+(j+1) = (2+j)+1 by omega]
      exact pointwiseHeatMajorant_succ_le hw0 hw (2+j) (by omega))
  have hhead : pointwiseHeatMajorant w (K+1) ≤ labelTwoHead*p := by
    simpa only [show 2+(K-1) = K+1 by omega] using hdom (K-1)
  apply CharacterTail.geom_series_le (fun j => pointwiseHeatMajorant w (K+1+j))
    (labelTwoHead*p) r (tailCap K) sharpTailRatio_nonnegative
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ allLabelTailBudget) hp)
    (by simpa only [Nat.add_zero] using hhead)
    (fun j => by
      change pointwiseHeatMajorant w (K+1+(j+1)) ≤ r * pointwiseHeatMajorant w (K+1+j)
      rw [show K+1+(j+1) = (K+1+j)+1 by omega]
      exact pointwiseHeatMajorant_succ_le hw0 hw (K+1+j) (by omega))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ p exact_geometric_closure hp
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (by decide)
      (fun
        | 0 => labelTwoHead
        | 1 => r
        | 2 => allLabelTailBudget
        | _ => p))) hscaled

/-- Both signed tail endpoints are actual Type-valued Haar certificates. -/
def tailInterval {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    {n : Nat} {x : RatPoly} (P : SquareBound n x 1) (K : Nat) (hK : 1 ≤ K) (L : Nat) :
    Interval n (finitePolySum (fun j => heatTerm w x (K+1+j)) (List.range L))
      (tailCap K) :=
  (Interval.finiteRange _ _ (fun j => termInterval hw0 P (K+1+j)) L).weaken
    (shifted_majorant_bound hw0 hw K hK L)

/-- Exact original slab face tail, not a surrogate scalar heat kernel. -/
def faceTailInterval_early {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K) :
    Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (tailCap K) :=
  tailInterval hw0 hw
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi)))
    K hK L

/-- Keep the actual first omitted majorant, rather than its half-nome cap.
This is (648/71)*w^8*(1/72)^(K-1). -/
def nomeTailCap (w : Q') (K : Nat) : Q' :=
  Q'.mkPos 72 71 (by decide) * pointwiseHeatMajorant w 2 * sharpTailRatio ^ (K-1)

/-- The SAME first-tail cap divided by the produced fixed early floor.
This is (20736/1055)*w^8*(1/72)^(K-1). -/
def nomeRelativeTailCap (w : Q') (K : Nat) : Q' :=
  Q'.mkPos 2304 1055 (by decide) * pointwiseHeatMajorant w 2 * sharpTailRatio ^ (K-1)

theorem nomeRelativeTailCap_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤ nomeRelativeTailCap w K :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (YMGap.Continuum.BondMovingScaledNorm.tailTerm_nonneg hw0 2 2))
    (Q'.pow_nonneg sharpTailRatio sharpTailRatio_nonnegative (K-1))

theorem nomeTailCap_relative_floor (w : Q') (K : Nat) :
    nomeTailCap w K ≈ nomeRelativeTailCap w K * floor := by
  unfold nomeTailCap nomeRelativeTailCap
  have h : Q'.mkPos 72 71 (by decide) ≈ Q'.mkPos 2304 1055 (by decide) * floor := by
    decide
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ h))
    (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.var 1)) (by decide)
      (fun
        | 0 => Q'.mkPos 2304 1055 (by decide)
        | 1 => floor
        | 2 => pointwiseHeatMajorant w 2
        | _ => sharpTailRatio ^ (K-1)))

theorem nomeRelativeTailCap_zero (K : Nat) : nomeRelativeTailCap 0 K ≈ 0 := by
  unfold nomeRelativeTailCap
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide :
      Q'.mkPos 2304 1055 (by decide) * pointwiseHeatMajorant 0 2 ≈ 0))
    (Q'.zero_mul_eqv _)

/-- The old corridor cap is recovered exactly at its endpoint. -/
theorem nomeRelativeTailCap_half (K : Nat) :
    nomeRelativeTailCap half K ≈ relativeTailCap K := by
  unfold nomeRelativeTailCap relativeTailCap
  exact Q'.mul_eqv_congr_right _ _ _ (by decide)

/-- Actual finite tail with its nome dependence intact, including zero nome. -/
theorem nome_shifted_majorant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K : Nat) (hK : 1 ≤ K) (L : Nat) :
    finSum (fun j => pointwiseHeatMajorant w (K+1+j)) L ≤ nomeTailCap w K := by
  let a := pointwiseHeatMajorant w 2
  let r := sharpTailRatio
  let p := r ^ (K-1)
  have hdom := CharacterTail.geom_dom
    (fun j => pointwiseHeatMajorant w (2+j)) a r sharpTailRatio_nonnegative
    (by simpa only [Nat.add_zero] using Q'.le_of_eqv (Q'.eqv_refl a))
    (fun j => by
      change pointwiseHeatMajorant w (2+(j+1)) ≤ r * pointwiseHeatMajorant w (2+j)
      rw [show 2+(j+1) = (2+j)+1 by omega]
      exact pointwiseHeatMajorant_succ_le hw0 hw (2+j) (by omega))
  have hhead : pointwiseHeatMajorant w (K+1) ≤ a*p := by
    simpa only [show 2+(K-1) = K+1 by omega] using hdom (K-1)
  apply CharacterTail.geom_series_le (fun j => pointwiseHeatMajorant w (K+1+j))
    (a*p) r (nomeTailCap w K) sharpTailRatio_nonnegative
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (YMGap.Continuum.BondMovingScaledNorm.tailTerm_nonneg hw0 2 2))
      (Q'.pow_nonneg sharpTailRatio sharpTailRatio_nonnegative (K-1)))
    (by simpa only [Nat.add_zero] using hhead)
    (fun j => by
      change pointwiseHeatMajorant w (K+1+(j+1)) ≤ r * pointwiseHeatMajorant w (K+1+j)
      rw [show K+1+(j+1) = (K+1+j)+1 by omega]
      exact pointwiseHeatMajorant_succ_le hw0 hw (K+1+j) (by omega))
  have hscalar : (1 : Q') + sharpTailRatio * Q'.mkPos 72 71 (by decide) ≈
      Q'.mkPos 72 71 (by decide) := by decide
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.mul (.mul (.var 3) (.var 0)) (.var 1))))
      (.mul (.add (.const 1) (.mul (.var 2) (.var 3))) (.mul (.var 0) (.var 1)))
      (by decide) (fun
        | 0 => a
        | 1 => p
        | 2 => r
        | _ => Q'.mkPos 72 71 (by decide)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hscalar)
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

/-- Produced Type-valued interval on the literal ORIGINAL slab face tail. -/
def nomeFaceTailInterval {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K) :
    Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (nomeTailCap w K) :=
  (Interval.finiteRange _ _ (fun j => termInterval hw0
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi)))
    (K+1+j)) L).weaken (nome_shifted_majorant_bound hw0 hw K hK L)

/-- ORIGINAL spectator factors, indexed by (physical face, inclusive cutoff).
The list may repeat a face and give its occurrences different cutoffs. -/
def background (w : Q') (extent : Nat) (entries : List (Nat × Nat)) : RatPoly :=
  polynomialProduct (fun e => faceHeatPolynomial w e.2 extent e.1) entries

def backgroundCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (extent : Nat) :
    (entries : List (Nat × Nat)) →
    (∀ e, e ∈ entries → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2) →
    Certificate (blocks extent) (background w extent entries)
  | [], _ => .one _
  | e::es, h => (faceCertificate hw0 hw e.2 extent e.1
      (h e List.mem_cons_self).1 (h e List.mem_cons_self).2).mul
      (backgroundCertificate hw0 hw extent es
        (fun j hj => h j (List.mem_cons_of_mem e hj)))

theorem background_mass_positive {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent : Nat) : (entries : List (Nat × Nat)) →
    (∀ e, e ∈ entries → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2) →
    (0 : Q') < quaternionHaar (blocks extent) (background w extent entries)
  | [], _ => Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.ge_of_eqv (QPolyHaarPositiveSubstitution.haar_one _))
  | e::es, h => by
      have hes := fun j hj => h j (List.mem_cons_of_mem e hj)
      have H := backgroundCertificate hw0 hw extent es hes
      have hf := floor_insertion H
        (faceFloorCertificate hw0 hw e.2 extent e.1
          (h e List.mem_cons_self).1 (h e List.mem_cons_self).2)
      have hp := Q'.mul_pos floor_positive (background_mass_positive hw0 hw extent es hes)
      exact Q'.pos_of_lt_of_le hp (Q'.le_trans' _ _ _ hf
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

private theorem insertion_difference (w : Q') (K L extent id : Nat) (p : RatPoly) :
    quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w (K+L) extent id)) +
      -(quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id))) ≈
    quaternionHaar (blocks extent) (polyMul p (faceHeatTail w extent id (K+1) L)) := by
  rw [faceHeatPolynomial_cutoff_append]
  have h := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p
    (faceHeatPolynomial w K extent id) (faceHeatTail w extent id (K+1) L)))
    (quaternionHaar_append (blocks extent) _ _)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun
        | 0 => quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id))
        | _ => quaternionHaar (blocks extent) (polyMul p (faceHeatTail w extent id (K+1) L))))

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
  (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K)
  {B : RatPoly} (H : Certificate (blocks extent) B)

include hw0 hw hi hK H

private theorem mass_difference_bound {eta : Q'} (he : (0 : Q') ≤ eta)
    (R : Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (eta*floor)) :
    Q'.abs (faceMass w (K+L) extent id B + -(faceMass w K extent id B)) ≤
      eta * faceMass w (K+L) extent id B := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (insertion_difference w K L extent id B)))
    (Q'.le_trans' _ _ _ (R.weighted_haar_bound H)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (floor_insertion H (faceFloorCertificate hw0 hw (K+L) extent id hi (by omega)))
          he)))

private theorem moment_difference_bound {eta : Q'} (he : (0 : Q') ≤ eta)
    (R : Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (eta*floor))
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w (K+L) extent id B p + -(faceMoment w K extent id B p)) ≤
      (c*eta) * faceMass w (K+L) extent id B := by
  have hp := @haar_of_coeff (blocks extent) _ _
    (((RatPolyCoeffEqv.mul_comm p B).mul_right (faceHeatTail w extent id (K+1) L)).trans
      (RatPolyCoeffEqv.mul_assoc B p _))
  have hc := Q'.mul_nonneg _ _ P.nonnegative he
  have horder : (c*(eta*floor))*quaternionHaar (blocks extent) B ≈
      (c*eta)*(floor*quaternionHaar (blocks extent) B) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
      (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _
      (insertion_difference w K L extent id (polyMul p B)) hp)))
    (Q'.le_trans' _ _ _ ((P.mul R).weighted_haar_bound H)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (floor_insertion H (faceFloorCertificate hw0 hw (K+L) extent id hi (by omega))) hc)))

private theorem old_moment_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w K extent id B p) ≤ c*faceMass w K extent id B := by
  have hp := @haar_of_coeff (blocks extent) _ _
    ((RatPolyCoeffEqv.mul_assoc p B (faceHeatPolynomial w K extent id)).trans
      (RatPolyCoeffEqv.mul_comm p (polyMul B (faceHeatPolynomial w K extent id))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (P.weighted_haar_bound (H.mul (faceCertificate hw0 hw K extent id hi hK)))

private theorem determinant_bound {eta : Q'} (he : (0 : Q') ≤ eta)
    (R : Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (eta*floor))
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w (K+L) extent id B p * faceMass w K extent id B +
      -(faceMoment w K extent id B p * faceMass w (K+L) extent id B)) ≤
      (2*c*eta)*(faceMass w (K+L) extent id B * faceMass w K extent id B) :=
  RationalRelativePerturbation.relative_determinant_bound _ _ _ _ c eta
    P.nonnegative he
    (H.mul (faceCertificate hw0 hw K extent id hi hK)).haar_nonnegative
    (H.mul (faceCertificate hw0 hw (K+L) extent id hi (by omega))).haar_nonnegative
    (old_moment_bound hw0 hw K extent id hi hK H P)
    (moment_difference_bound hw0 hw K L extent id hi hK H he R P)
    (mass_difference_bound hw0 hw K L extent id hi hK H he R)

omit K L hK in
private theorem faceMass_positive (J : Nat) (hJ : 1 ≤ J)
    (hB : (0 : Q') < quaternionHaar (blocks extent) B) :
    (0 : Q') < faceMass w J extent id B :=
  Q'.pos_of_lt_of_le (Q'.mul_pos floor_positive hB)
    (floor_insertion H (faceFloorCertificate hw0 hw J extent id hi hJ))

omit H in
/-- Shared cancellation machinery for a produced Type-valued tail interval.
The concrete tail producers supply R; it is not a new analytic input. -/
theorem original_background_normalized_from_tail {eta : Q'} (he : (0 : Q') ≤ eta)
    (R : Interval (blocks extent) (faceHeatTail w extent id (K+1) L) (eta*floor))
    (entries : List (Nat × Nat))
    (hentries : ∀ e, e ∈ entries → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let B := background w extent entries
    let H := backgroundCertificate hw0 hw extent entries hentries
    let hB := background_mass_positive hw0 hw extent entries hentries
    Q'.abs
      (faceMoment w (K+L) extent id B p * Q'.recipPos (faceMass w (K+L) extent id B)
          (faceMass_positive hw0 hw extent id hi H (K+L) (by omega) hB) +
       -(faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B)
          (faceMass_positive hw0 hw extent id hi H K hK hB))) ≤ 2*c*eta := by
  dsimp only
  exact ratio_difference_bound _ _ _ _ (2*c*eta) _ _
    (determinant_bound hw0 hw K L extent id hi hK
      (backgroundCertificate hw0 hw extent entries hentries) he R P)

omit H in
/-- NORMALIZED original one-face change. Every spectator factor and both
positive OWN partitions are produced from the literal heat action.
No background positivity or mass-floor hypothesis is left to the caller. -/
theorem original_background_normalized (entries : List (Nat × Nat))
    (hentries : ∀ e, e ∈ entries → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let B := background w extent entries
    let H := backgroundCertificate hw0 hw extent entries hentries
    let hB := background_mass_positive hw0 hw extent entries hentries
    Q'.abs
      (faceMoment w (K+L) extent id B p * Q'.recipPos (faceMass w (K+L) extent id B)
          (faceMass_positive hw0 hw extent id hi H (K+L) (by omega) hB) +
       -(faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B)
          (faceMass_positive hw0 hw extent id hi H K hK hB))) ≤ 2*c*relativeTailCap K :=
  original_background_normalized_from_tail hw0 hw K L extent id hi hK
    (relativeTailCap_nonnegative K)
    ((faceTailInterval_early hw0 hw K L extent id hi hK).changeCap (tailCap_relative_floor K))
    entries hentries P

#print axioms tailCap
#print axioms relativeTailCap
#print axioms relativeTailCap_nonnegative
#print axioms tailCap_relative_floor
#print axioms shifted_majorant_bound
#print axioms tailInterval
#print axioms faceTailInterval_early
#print axioms background
#print axioms backgroundCertificate
#print axioms background_mass_positive
#print axioms original_background_normalized
#print axioms nomeTailCap
#print axioms nomeRelativeTailCap
#print axioms nomeRelativeTailCap_nonnegative
#print axioms nomeTailCap_relative_floor
#print axioms nomeRelativeTailCap_zero
#print axioms nomeRelativeTailCap_half
#print axioms nome_shifted_majorant_bound
#print axioms nomeFaceTailInterval
#print axioms original_background_normalized_from_tail

end YMGap.Continuum.BF4ExactSlabSmallNomeOneFaceCutoffStability
