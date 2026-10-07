/-
# Transfer matrix (2b): the torus plaquette product in slice order (choice-free)

ADDITIVE.  **Labels:** algebra and geometry only, valid for every coupling and every plaquette
weight (Wilson T_K in particular); also true for U(1), not gap evidence.

* `prod_perm`: `l ~ l' → Π_{p∈l} F p ≅ Π_{p∈l'} F p`.  Proved by induction on `List.Perm`,
  using only `mul_assoc`/`mul_comm`.
* `peel`: `l ~ Π-concat over t < N of l.filter (time = t)`, when every time is `< N`.
* `torus_slice_perm`: `torusPlaquettes N ~ sliceOrder N`, where
  `sliceOrder N = concat_{t<N} (slicePS N t ++ slicePT N t)`.
* `torus_prod_slice`: `Π_{p∈torus} F p ≅ Π_{t<N} (Π_{slicePS t} F · Π_{slicePT t} F)`.  This is
  the `Π_t A(U_t)·B(U_t,V_t,U_{t+1})` form of the integrand, with `SU2TorusSlice`.
-/

import YMGap.Continuum.SU2TorusSlice
import YMGap.Continuum.SU2WilsonPolymerIdentity

namespace YMGap.Continuum.SU2SliceOrder

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusSlice

local infix:50 " ≅ " => RatPolyCoeffEqv

theorem prod_append (F : Z4Plaq → RatPoly) : ∀ l l' : List Z4Plaq,
    prodPoly F (l ++ l') ≅ polyMul (prodPoly F l) (prodPoly F l')
  | [], _ => (RatPolyCoeffEqv.one_mul _).symm
  | _ :: l, l' => (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) (prod_append F l l')).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm

theorem prod_perm (F : Z4Plaq → RatPoly) {l l' : List Z4Plaq} (h : l.Perm l') :
    prodPoly F l ≅ prodPoly F l' := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons x _ ih => exact RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) ih
  | swap x y l =>
    show polyMul (F y) (polyMul (F x) _) ≅ polyMul (F x) (polyMul (F y) _)
    exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ((RatPolyCoeffEqv.mul
      (RatPolyCoeffEqv.mul_comm _ _) (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.mul_assoc _ _ _))
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem fnil {α : Type} (p : α → Bool) : ∀ l : List α, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_neg (by rw [h a List.mem_cons_self]; exact Bool.false_ne_true)]
    exact fnil p l fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- Pieces by time, for `t < k`. -/
def pieces {α : Type} (f : α → Nat) (l : List α) (k : Nat) : List α :=
  (List.range k).flatMap fun t => l.filter fun x => f x == t

theorem peel_lt {α : Type} (f : α → Nat) (l : List α) : ∀ k : Nat,
    (l.filter fun x => decide (f x < k)).Perm (pieces f l k)
  | 0 => by
    rw [fnil _ l (fun a _ => decide_eq_false (Nat.not_lt_zero _))]
    exact List.Perm.refl _
  | k + 1 => by
    have hs := List.filter_append_perm (fun x => decide (f x < k)) (l.filter fun x => decide (f x < k + 1))
    rw [List.filter_filter, List.filter_filter] at hs
    have e1 : (l.filter fun a => decide (f a < k) && decide (f a < k + 1)) = l.filter fun x => decide (f x < k) :=
      List.filter_congr fun x _ => by
        by_cases h : f x < k
        · rw [decide_eq_true h, decide_eq_true (Nat.lt_succ_of_lt h)]; rfl
        · rw [decide_eq_false h]; rfl
    have e2 : (l.filter fun a => !decide (f a < k) && decide (f a < k + 1)) = l.filter fun x => f x == k :=
      List.filter_congr fun x _ => by
        by_cases h : f x = k
        · rw [h, decide_eq_false (Nat.lt_irrefl k), decide_eq_true (Nat.lt_succ_self k)]
          exact (beq_iff_eq.mpr rfl).symm
        · rw [beq_eq_false_iff_ne.mpr h]
          by_cases h' : f x < k
          · rw [decide_eq_true h']; rfl
          · rw [decide_eq_false h', decide_eq_false (show ¬ f x < k + 1 by omega)]; rfl
    rw [e1, e2] at hs
    refine hs.symm.trans ?_
    unfold pieces
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Perm.append (peel_lt f l k) (List.Perm.refl _)

theorem peel {α : Type} (f : α → Nat) (l : List α) (N : Nat) (h : ∀ x ∈ l, f x < N) :
    l.Perm (pieces f l N) := by
  have := peel_lt f l N
  rwa [List.filter_eq_self.mpr (fun a ha => decide_eq_true (h a ha))] at this

/-! ## The torus in slice order -/

def sliceOrder (N : Nat) : List Z4Plaq := (List.range N).flatMap fun t => slicePS N t ++ slicePT N t

theorem flatMap_perm {α β : Type} (f g : α → List β) : ∀ l : List α, (∀ a ∈ l, (f a).Perm (g a)) →
    (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact List.Perm.append (h a List.mem_cons_self) (flatMap_perm f g l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem slice_split (N t : Nat) :
    ((torusPlaquettes N).filter fun p => p.1.1 == t).Perm (slicePS N t ++ slicePT N t) := by
  have hs := List.filter_append_perm (fun p : Z4Plaq => !isTimelike p) ((torusPlaquettes N).filter fun p => p.1.1 == t)
  rw [List.filter_filter, List.filter_filter] at hs
  have e1 : ((torusPlaquettes N).filter fun a => !isTimelike a && (a.1.1 == t)) = slicePS N t :=
    List.filter_congr fun x _ => Bool.and_comm _ _
  have e2 : ((torusPlaquettes N).filter fun a => !!isTimelike a && (a.1.1 == t)) = slicePT N t :=
    List.filter_congr fun x _ => by rw [Bool.not_not, Bool.and_comm]
  rw [e1, e2] at hs
  exact hs.symm

theorem torus_slice_perm (N : Nat) : (torusPlaquettes N).Perm (sliceOrder N) :=
  (peel (fun p : Z4Plaq => p.1.1) (torusPlaquettes N) N fun p hp => by
    obtain ⟨v, P⟩ := p
    exact ((mem_torusPlaquettes N v P).mp hp).1).trans
    (flatMap_perm _ _ _ fun t _ => slice_split N t)

/-- Product over a slice-indexed concatenation. -/
def sliceProd (F : Z4Plaq → RatPoly) (N : Nat) : List Nat → RatPoly
  | [] => polyOne
  | t :: ts => polyMul (polyMul (prodPoly F (slicePS N t)) (prodPoly F (slicePT N t))) (sliceProd F N ts)

theorem prod_flat (F : Z4Plaq → RatPoly) (N : Nat) : ∀ ts : List Nat,
    prodPoly F (ts.flatMap fun t => slicePS N t ++ slicePT N t) ≅ sliceProd F N ts
  | [] => RatPolyCoeffEqv.refl _
  | t :: ts => by
    simp only [List.flatMap_cons]
    exact (prod_append F _ _).trans (RatPolyCoeffEqv.mul (prod_append F _ _) (prod_flat F N ts))

/-- **Slice factorisation of the torus integrand (PROVED):**
`Π_{p∈torus} F p ≅ Π_{t<N} (Π_{p∈PS_t} F p · Π_{p∈PT_t} F p)`. -/
theorem torus_prod_slice (F : Z4Plaq → RatPoly) (N : Nat) :
    prodPoly F (torusPlaquettes N) ≅ sliceProd F N (List.range N) :=
  (prod_perm F (torus_slice_perm N)).trans (prod_flat F N _)

end YMGap.Continuum.SU2SliceOrder
