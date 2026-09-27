/-
# Sharp finite product-Haar Efron--Stein inequality

The in-place coordinate projections give an exact squared-norm telescope.
Commutation and one-coordinate contraction then bound each telescope piece
by the corresponding fluctuation of the original polynomial. The constant
is one, including the zero-block carrier. This is the unweighted Haar law;
it is not an interacting Yang--Mills coercivity statement.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockTelescope
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2QuaternionHaarEfronStein

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockTelescope
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local infix:50 " ≈ " => Q'.eqv

def haarSquare (blocks : Nat) (p : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul p p)

local notation "square" => haarSquare

/-- The exact energy of the ordinary-Haar telescope. -/
def telescopeEnergy (blocks count : Nat) (p : RatPoly) : Q' :=
  qListSum ((List.range count).map (fun i => square blocks (term i p)))

/-- The sum of the original single-coordinate fluctuation energies. -/
def fluctuationEnergy (blocks : Nat) (p : RatPoly) : Q' :=
  qListSum ((List.range blocks).map (fun i => square blocks (fluctuation i p)))

private theorem sum_append (xs ys : List Q') :
    qListSum (xs ++ ys) ≈ qListSum xs + qListSum ys := by
  induction xs with
  | nil => exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | cons x xs ih =>
      change x + qListSum (xs ++ ys) ≈ (x + qListSum xs) + qListSum ys
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ ih)
        (Q'.eqv_symm (Q'.add_assoc_eqv x (qListSum xs) (qListSum ys)))

private theorem energy_succ (blocks count : Nat) (p : RatPoly) :
    telescopeEnergy blocks (count+1) p ≈
      telescopeEnergy blocks count p + square blocks (term count p) := by
  unfold telescopeEnergy
  rw [List.range_succ, List.map_append, List.map_singleton]
  exact Q'.eqv_trans _ _ _ (sum_append _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: ps => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 _) (haar_neg blocks ps))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks s hs

private theorem haar_cap_mul (blocks : Nat) (c : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (cap c) p) ≈ c * quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p))
    (quaternionHaar_polySmul blocks c p)

private theorem haar_cap (blocks : Nat) (c : Q') :
    quaternionHaar blocks (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (haar_one blocks)) (Q'.mul_one_eqv c))

/-- Exact Pythagorean sum of the successive free conditional losses. -/
theorem square_telescope (blocks count : Nat) (p : RatPoly)
    (hc : count ≤ blocks) :
    square blocks p ≈
      square blocks (partialProjection count p) +
        telescopeEnergy blocks count p := by
  revert hc
  induction count with
  | zero =>
      intro _
      change square blocks p ≈ square blocks p + 0
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
  | succ count ih =>
      intro hc
      have hb : count < blocks := Nat.lt_of_succ_le hc
      have hsplit := square_decomposition blocks count hb (partialProjection count p)
      have hbase := ih (Nat.le_of_lt hb)
      have he := energy_succ blocks count p
      have hs : square blocks (partialProjection count p) ≈
          square blocks (project count (partialProjection count p)) +
            square blocks (term count p) := hsplit
      rw [partialProjection_succ]
      exact Q'.eqv_trans _ _ _ hbase
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hs)
          (Q'.eqv_trans _ _ _
            (poly_identity_of_normal_eq
              (.add (.add (.var 0) (.var 1)) (.var 2))
              (.add (.var 0) (.add (.var 2) (.var 1)))
              (by decide)
              (fun | 0 => square blocks (project count (partialProjection count p))
                   | 1 => square blocks (term count p)
                   | _ => telescopeEnergy blocks count p))
            (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm he))))

private theorem project_fluctuation_comm (a b : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (project a (fluctuation b p))
      (fluctuation b (project a p)) := by
  unfold fluctuation
  rw [project_add]
  exact ((RatPolyCoeffEqv.refl _).add (project_neg a _)).trans
    ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.neg (project_comm a b p)))

private theorem partialProjection_fluctuation_comm (count block : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (partialProjection count (fluctuation block p))
      (fluctuation block (partialProjection count p)) := by
  induction count with
  | zero => exact RatPolyCoeffEqv.refl _
  | succ count ih =>
      rw [partialProjection_succ, partialProjection_succ]
      exact (project_congr count ih).trans
        (project_fluctuation_comm count block (partialProjection count p))

private theorem partialProjection_square_le (blocks count : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hc : count ≤ blocks) :
    square blocks (partialProjection count p) ≤ square blocks p := by
  induction count with
  | zero => exact Q'.le_refl' _
  | succ count ih =>
      have hb : count < blocks := Nat.lt_of_succ_le hc
      rw [partialProjection_succ]
      exact Q'.le_trans' _ _ _
        (project_square_contraction blocks count hb (partialProjection count p)
          (partialProjection_supported count hp))
        (ih (Nat.le_of_lt hb))

private theorem term_square_le (blocks i : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hi : i < blocks) :
    square blocks (term i p) ≤ square blocks (fluctuation i p) := by
  have he := partialProjection_fluctuation_comm i i p
  have hp' := fluctuation_supported i hp
  have hsq : square blocks (term i p) ≈
      square blocks (partialProjection i (fluctuation i p)) :=
    Q'.eqv_symm (haar_of_coeff (he.mul he))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
    (partialProjection_square_le blocks i (fluctuation i p) hp' (Nat.le_of_lt hi))

private theorem sum_le (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    telescopeEnergy blocks blocks p ≤ fluctuationEnergy blocks p := by
  unfold telescopeEnergy fluctuationEnergy
  have go : ∀ xs : List Nat,
      (∀ i, i ∈ xs → i < blocks) →
      qListSum (xs.map (fun i => square blocks (term i p))) ≤
        qListSum (xs.map (fun i => square blocks (fluctuation i p))) := by
    intro xs
    induction xs with
    | nil => intro _; exact Q'.le_refl' _
    | cons i xs ih =>
        intro hs
        exact Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ _
            (term_square_le blocks i p hp (hs i List.mem_cons_self)))
          (Q'.add_le_add_left _ _ _
            (ih (fun j hj => hs j (List.mem_cons_of_mem i hj))))
  exact go (List.range blocks) (fun i hi => List.mem_range.mp hi)

private theorem endpoint_square (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    square blocks (partialProjection blocks p) ≈
      quaternionHaar blocks p * quaternionHaar blocks p := by
  let m := quaternionHaar blocks p
  let s := partialProjection blocks p
  have hs : SupportedQuaternionBlocks blocks s := partialProjection_supported blocks hp
  have h := (partialProjection_constant blocks p hp) s hs
  have hc : quaternionHaar blocks (polyMul s (cap m)) ≈
      m * quaternionHaar blocks s :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (haar_cap_mul blocks m s)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ hc
      (Q'.mul_eqv_congr_left m _ _ (partialProjection_mean blocks blocks p (Nat.le_refl _))))

/-- The literal Haar-centered polynomial, with no division by a partition. -/
def haarCentered (blocks : Nat) (p : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (cap (quaternionHaar blocks p)))

private theorem centered_square (blocks : Nat) (p : RatPoly) :
    square blocks (haarCentered blocks p) ≈
      square blocks p +
        -(quaternionHaar blocks p * quaternionHaar blocks p) := by
  let m := quaternionHaar blocks p
  have he : RatPolyCoeffEqv
      (polyMul (haarCentered blocks p) (haarCentered blocks p))
      (polyAdd (polyMul p p)
        (polyAdd (polyNeg (polyMul (cap m) p))
          (polyAdd (polyNeg (polyMul (cap m) p))
            (polyMul (cap m) (cap m))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))
      (.add (.mul (.var 0) (.var 0))
        (.add (.neg (.mul (.var 1) (.var 0)))
          (.add (.neg (.mul (.var 1) (.var 0)))
            (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => p | _ => cap m)
  have hcp : quaternionHaar blocks (polyMul (cap m) p) ≈ m*m :=
    haar_cap_mul blocks m p
  have hcc : quaternionHaar blocks (polyMul (cap m) (cap m)) ≈ m*m :=
    Q'.eqv_trans _ _ _ (haar_cap_mul blocks m (cap m))
      (Q'.mul_eqv_congr_left m _ _ (haar_cap blocks m))
  have hn : quaternionHaar blocks (polyNeg (polyMul (cap m) p)) ≈ -(m*m) :=
    Q'.eqv_trans _ _ _ (haar_neg blocks _)
      (Q'.neg_eqv_congr _ _ hcp)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
            (Q'.add_eqv_congr' hn
              (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
                (Q'.add_eqv_congr' hn hcc)))))
        (poly_identity_of_normal_eq
          (.add (.var 0)
            (.add (.neg (.var 1)) (.add (.neg (.var 1)) (.var 1))))
          (.add (.var 0) (.neg (.var 1)))
          (by decide) (fun | 0 => square blocks p | _ => m*m))))

/-- Sharp finite product-Haar Efron--Stein estimate on the same supported
polynomial carrier. No positivity of an interacting action is assumed. -/
theorem haar_efron_stein (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    square blocks (haarCentered blocks p) ≤ fluctuationEnergy blocks p := by
  have ht := square_telescope blocks blocks p (Nat.le_refl _)
  have he := endpoint_square blocks p hp
  have hc := centered_square blocks p
  have hstep1 : square blocks p +
      -(quaternionHaar blocks p * quaternionHaar blocks p) ≈
      (square blocks (partialProjection blocks p) +
        telescopeEnergy blocks blocks p) +
          -(quaternionHaar blocks p * quaternionHaar blocks p) :=
    Q'.add_eqv_congr_right _ _ _ ht
  have hstep2 : (square blocks (partialProjection blocks p) +
      telescopeEnergy blocks blocks p) +
        -(quaternionHaar blocks p * quaternionHaar blocks p) ≈
      ((quaternionHaar blocks p * quaternionHaar blocks p) +
        telescopeEnergy blocks blocks p) +
          -(quaternionHaar blocks p * quaternionHaar blocks p) :=
    Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _ he)
  have hsplit : square blocks (haarCentered blocks p) ≈
      telescopeEnergy blocks blocks p :=
    Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ hstep1
        (Q'.eqv_trans _ _ _ hstep2
          (poly_identity_of_normal_eq
            (.add (.add (.var 1) (.var 0)) (.neg (.var 1))) (.var 0)
            (by decide)
            (fun | 0 => telescopeEnergy blocks blocks p
                 | _ => quaternionHaar blocks p * quaternionHaar blocks p))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) (sum_le blocks p hp)

#print axioms haarSquare
#print axioms telescopeEnergy
#print axioms fluctuationEnergy
#print axioms square_telescope
#print axioms haarCentered
#print axioms haar_efron_stein

end YMGap.Continuum.SU2QuaternionHaarEfronStein
