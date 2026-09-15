/-
# Conditional Schur contraction with arbitrary retained polynomial coefficients

Only the sixteen moments of two head coordinates are reduced by the kernel.
All tail polynomials remain opaque throughout the proof. A finite linear
combination of head coordinates contracts to its coefficient dot product
with the exact normalized S^3 factor 1/4. No tail degree or support bound,
independence between tail factors, or replacement of a tail measure is used.
-/

import YMGap.Continuum.SU2QuaternionPartialSphereGaussian
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionHeadLinearHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction

local infix:50 " ≈ " => Q'.eqv

theorem liftHead_mul (p q : RatPoly) :
    liftHead (polyMul p q) = polyMul (liftHead p) (liftHead q) := by
  simp only [liftHead, polyMul, List.map_flatMap, List.flatMap_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatPoly => p.flatMap f)
  funext s
  apply congrArg (fun f : RatTerm → RatTerm => q.map f)
  funext t
  rfl

private theorem headMoment_lift (m n : List Nat) :
    headQuaternionMoment (monoMul m (0::0::0::0::n)) = headQuaternionMoment m := by
  simp only [headQuaternionMoment, exponentAt_monoMul]
  simp [exponentAt]

private theorem pull_row (s : RatTerm) : ∀ q : RatPoly,
    RatPolyTermwiseEqv
      (directPartialHaarProductRaw [s] (liftHead q))
      (polyMul [partialHaarHeadTerm s] q)
  | [] => True.intro
  | t::q => by
      refine ⟨rfl, ?_, pull_row s q⟩
      change (s.2*t.2)*headQuaternionMoment (monoMul s.1 (0::0::0::0::t.1)) ≈
        (s.2*headQuaternionMoment s.1)*t.2
      rw [headMoment_lift]
      exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

private theorem pull_terms : ∀ p q : RatPoly,
    RatPolyTermwiseEqv (directPartialHaarProductRaw p (liftHead q))
      (polyMul (partialHaarHead p) q)
  | [], _ => True.intro
  | s::p, q => by
      simpa only [directPartialHaarProductRaw, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, partialHaarHead, List.map_cons, polyMul] using
        RatPolyTermwiseEqv.append (pull_row s q) (pull_terms p q)

/-- Retain arbitrary tail coefficients before any subsequent integration. -/
theorem partialHaarHead_mul_lift (p q : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p (liftHead q)))
      (polyMul (partialHaarHead p) q) := by
  rw [partialHaarHead_polyMul_eq_directRaw]
  exact fun weight => ratWeightedSum_termwise_eqv weight (pull_terms p q)

def coordinateMoment (i j : Fin 4) : Q' :=
  if i = j then Q'.mkPos 1 4 (by decide) else 0

theorem coordinate_pair : ∀ i j : Fin 4,
    RatPolyCoeffEqv (partialHaarHead (polyMul (polyVar i.val) (polyVar j.val)))
      (polySmul (coordinateMoment i j) polyOne) := by
  have h : ∀ i j : Fin 4, RatPolyTermwiseEqv
      (canonRat (partialHaarHead (polyMul (polyVar i.val) (polyVar j.val))))
      (canonRat (polySmul (coordinateMoment i j) polyOne)) := by decide +kernel
  exact fun i j => RatPolyCoeffEqv.of_canon_termwise (h i j)

def atom (i : Fin 4) (p : RatPoly) : RatPoly := polyMul (polyVar i.val) (liftHead p)

theorem atom_pair (i j : Fin 4) (p q : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (atom i p) (atom j q)))
      (polySmul (coordinateMoment i j) (polyMul p q)) := by
  have h : RatPolyCoeffEqv (polyMul (atom i p) (atom j q))
      (polyMul (polyMul (polyVar i.val) (polyVar j.val)) (liftHead (polyMul p q))) := by
    rw [liftHead_mul]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun k => match k with
        | 0 => polyVar i.val | 1 => liftHead p | 2 => polyVar j.val | _ => liftHead q)
  exact (partialHaarHead_congr h).trans
    ((partialHaarHead_mul_lift _ _).trans
      (((coordinate_pair i j).mul_right (polyMul p q)).trans
        ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
          ((RatPolyCoeffEqv.one_mul _).smul _))))

def linear : List (Fin 4 × RatPoly) → RatPoly
  | [] => polyZero
  | (i,p)::xs => polyAdd (atom i p) (linear xs)

def gramRow (i : Fin 4) (p : RatPoly) : List (Fin 4 × RatPoly) → RatPoly
  | [] => polyZero
  | (j,q)::ys => polyAdd (polySmul (coordinateMoment i j) (polyMul p q)) (gramRow i p ys)

def gram : List (Fin 4 × RatPoly) → List (Fin 4 × RatPoly) → RatPoly
  | [], _ => polyZero
  | (i,p)::xs, ys => polyAdd (gramRow i p ys) (gram xs ys)

private theorem partial_add (p q : RatPoly) :
    partialHaarHead (polyAdd p q) = polyAdd (partialHaarHead p) (partialHaarHead q) := List.map_append

private theorem atom_linear (i : Fin 4) (p : RatPoly) : ∀ ys,
    RatPolyCoeffEqv (partialHaarHead (polyMul (atom i p) (linear ys))) (gramRow i p ys)
  | [] => partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right _)
  | (j,q)::ys => by
      have h := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right (atom i p) (atom j q) (linear ys))
      rw [partial_add] at h
      exact h.trans ((atom_pair i j p q).add (atom_linear i p ys))

/-- The finite dot-product Schur rule with every tail coefficient retained. -/
theorem linear_pair : ∀ xs ys,
    RatPolyCoeffEqv (partialHaarHead (polyMul (linear xs) (linear ys))) (gram xs ys)
  | [], _ => RatPolyCoeffEqv.refl _
  | (i,p)::xs, ys => by
      change RatPolyCoeffEqv (partialHaarHead (polyMul (polyAdd (atom i p) (linear xs)) (linear ys))) _
      rw [polyMul_add_left_exact, partial_add]
      exact (atom_linear i p ys).add (linear_pair xs ys)

def four (p : Fin 4 → RatPoly) : List (Fin 4 × RatPoly) :=
  [(0,p 0),(1,p 1),(2,p 2),(3,p 3)]

def quarter : Q' := Q'.mkPos 1 4 (by decide)

private theorem row_four (i : Fin 4) (p : RatPoly) (q : Fin 4 → RatPoly) :
    RatPolyCoeffEqv (gramRow i p (four q)) (polySmul quarter (polyMul p (q i))) := by
  rcases i with ⟨i,hi⟩
  match i with
  | 0 => exact (((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.zero_smul _).add ((RatPolyCoeffEqv.zero_smul _).add
        ((RatPolyCoeffEqv.zero_smul _).add (RatPolyCoeffEqv.refl _))))).trans
      (RatPolyCoeffEqv.add_zero _))
  | 1 => exact (((RatPolyCoeffEqv.zero_smul _).add
      ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.zero_smul _).add
        ((RatPolyCoeffEqv.zero_smul _).add (RatPolyCoeffEqv.refl _))))).trans
      (RatPolyCoeffEqv.add_zero _))
  | 2 => exact (((RatPolyCoeffEqv.zero_smul _).add
      ((RatPolyCoeffEqv.zero_smul _).add ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.zero_smul _).add (RatPolyCoeffEqv.refl _))))).trans
      (RatPolyCoeffEqv.add_zero _))
  | 3 => exact (((RatPolyCoeffEqv.zero_smul _).add
      ((RatPolyCoeffEqv.zero_smul _).add ((RatPolyCoeffEqv.zero_smul _).add
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.refl _))))).trans
      (RatPolyCoeffEqv.add_zero _))
  | n+4 =>
      have hf : False := by omega
      exact hf.elim

/-- Four arbitrary polynomial coefficients, without orthogonality assumptions
on the retained variables. -/
theorem four_pair (p q : Fin 4 → RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (linear (four p)) (linear (four q))))
      (polySmul quarter (polyAdd (polyMul (p 0) (q 0))
        (polyAdd (polyMul (p 1) (q 1))
          (polyAdd (polyMul (p 2) (q 2)) (polyMul (p 3) (q 3)))))) := by
  refine (linear_pair (four p) (four q)).trans ?_
  have h := (row_four 0 (p 0) q).add ((row_four 1 (p 1) q).add
    ((row_four 2 (p 2) q).add (((row_four 3 (p 3) q).add
      (RatPolyCoeffEqv.refl polyZero)).trans (RatPolyCoeffEqv.add_zero _))))
  exact (h.trans ((RatPolyCoeffEqv.refl _).add
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_add _ _ _).symm).trans
      (RatPolyCoeffEqv.smul_add _ _ _).symm))).trans
        (RatPolyCoeffEqv.smul_add _ _ _).symm

end YMGap.Continuum.SU2QuaternionHeadLinearHaar

#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.liftHead_mul
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.partialHaarHead_mul_lift
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.coordinateMoment
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.coordinate_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.atom
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.atom_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.linear
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.gramRow
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.gram
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.linear_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.four
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.quarter
#print axioms YMGap.Continuum.SU2QuaternionHeadLinearHaar.four_pair
