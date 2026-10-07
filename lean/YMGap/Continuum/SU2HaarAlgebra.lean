/-
# R1 commit 4: commutative-algebra layer for the multi-link Haar functional

ADDITIVE.  `quaternionHaar` acts on raw term lists, so `polyMul` is neither commutative nor
associative as a list.  Here the Haar functional is shown to see it as commutative and
associative.  This holds in every multiplicative context.

* `phi n X m = Σ_{x∈X} x.c · H_n(m·x.m)`: the moment functional of `X` shifted by a monomial `m`.
  `quaternionHaar n X = phi n X []`.
* `PE n X Y := ∀ m, phi n X m ≈ phi n Y m`, a context-stable Haar equivalence.
  * `pe_haar`: equal Haar integrals.
  * `pe_mulL`, `pe_mulR`, `pe_append`: closed under products and sums.
* `pe_comm`, `pe_assoc`, `pe_one`, `pe_const`: commutativity, associativity, unit, and scalar
  `c ≈ 1`.
* `pe_extract`: `Π_{Q₁ ++ q :: Q₂} G ≡ G q · Π_{Q₁ ++ Q₂} G`, which pulls one factor to the front.
-/

import YMGap.Continuum.SU2PlaqSupport
import YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

namespace YMGap.Continuum.SU2HaarAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization (monoMul_comm monoMul_assoc)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## Finite sums -/

def sm {β : Type} (f : β → Q') : List β → Q'
  | [] => 0
  | a :: l => f a + sm f l

theorem sm_congr {β : Type} {f g : β → Q'} : ∀ l : List β, (∀ a ∈ l, (f a).eqv (g a)) →
    (sm f l).eqv (sm g l)
  | [], _ => Q'.eqv_refl _
  | a :: l, h => Q'.add_eqv_congr' (h a (List.mem_cons_self ..))
      (sm_congr l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sm_append {β : Type} (f : β → Q') : ∀ l r : List β, (sm f (l ++ r)).eqv (sm f l + sm f r)
  | [], r => by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0) (PolyExpr.const 0 + V 0) (by decide) (fun _ => sm f r)
  | a :: l, r => by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl (f a)) (sm_append f l r)) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) ((V 0 + V 1) + V 2) (by decide)
      (fun | 0 => f a | 1 => sm f l | _ => sm f r)

theorem sm_map {β γ : Type} (f : γ → Q') (g : β → γ) : ∀ l : List β,
    sm f (l.map g) = sm (fun a => f (g a)) l
  | [] => rfl
  | a :: l => by
    show f (g a) + sm f (l.map g) = _
    rw [sm_map f g l]; rfl

theorem sm_flatMap {β γ : Type} (f : γ → Q') (g : β → List γ) : ∀ l : List β,
    (sm f (l.flatMap g)).eqv (sm (fun a => sm f (g a)) l)
  | [] => Q'.eqv_refl _
  | a :: l => by
    rw [List.flatMap_cons]
    exact Q'.eqv_trans _ _ _ (sm_append f _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_flatMap f g l))

theorem sm_mul {β : Type} (c : Q') (f : β → Q') : ∀ l : List β,
    (c * sm f l).eqv (sm (fun a => c * f a) l)
  | [] => Q'.mul_zero_eqv c
  | _ :: l => Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_mul c f l))

theorem sm_zero {β : Type} : ∀ l : List β, (sm (fun _ => (0 : Q')) l).eqv 0
  | [] => Q'.eqv_refl _
  | _ :: l => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl 0) (sm_zero l)) (by decide)

theorem sm_add {β : Type} (f g : β → Q') : ∀ l : List β,
    (sm f l + sm g l).eqv (sm (fun a => f a + g a) l)
  | [] => show ((0 : Q') + 0).eqv 0 from by decide
  | a :: l => by
    refine Q'.eqv_trans _ ((f a + g a) + (sm f l + sm g l)) _ ?_
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_add f g l))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq ((V 0 + V 1) + (V 2 + V 3)) ((V 0 + V 2) + (V 1 + V 3))
      (by decide) (fun | 0 => f a | 1 => sm f l | 2 => g a | _ => sm g l)

theorem sm_swap {β γ : Type} (f : β → γ → Q') (r : List γ) : ∀ l : List β,
    (sm (fun a => sm (fun b => f a b) r) l).eqv (sm (fun b => sm (fun a => f a b) l) r)
  | [] => Q'.eqv_symm (sm_zero r)
  | _ :: l => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_swap f r l))
      (sm_add _ _ r)

/-! ## The shifted moment functional -/

variable (n : Nat)

def phi (X : RatPoly) (m : List Nat) : Q' :=
  sm (fun x : List Nat × Q' => x.2 * quaternionHaarMono n (monoMul m x.1)) X

theorem haar_phi : ∀ X : RatPoly, quaternionHaar n X = phi n X []
  | [] => rfl
  | t :: X => by
    show t.2 * quaternionHaarMono n t.1 + quaternionHaar n X = _
    rw [haar_phi X]; rfl

theorem phi_mul (Z X : RatPoly) (m : List Nat) :
    (phi n (polyMul Z X) m).eqv (sm (fun z => z.2 * phi n X (monoMul m z.1)) Z) := by
  refine Q'.eqv_trans _ _ _ (sm_flatMap _ _ Z) (sm_congr Z fun z _ => ?_)
  rw [sm_map]
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (sm_mul _ _ X))
  refine sm_congr X fun x _ => ?_
  show ((z.2 * x.2) * quaternionHaarMono n (monoMul m (monoMul z.1 x.1))).eqv
    (z.2 * (x.2 * quaternionHaarMono n (monoMul (monoMul m z.1) x.1)))
  rw [monoMul_assoc]
  exact Q'.mul_assoc_eqv _ _ _

/-- Context-stable Haar equivalence. -/
def PE (X Y : RatPoly) : Prop := ∀ m, (phi n X m).eqv (phi n Y m)

theorem pe_refl (X : RatPoly) : PE n X X := fun _ => Q'.eqv_refl _
theorem pe_symm {X Y : RatPoly} (h : PE n X Y) : PE n Y X := fun m => Q'.eqv_symm (h m)
theorem pe_trans {X Y Z : RatPoly} (h : PE n X Y) (h' : PE n Y Z) : PE n X Z :=
  fun m => Q'.eqv_trans _ _ _ (h m) (h' m)

theorem pe_haar {X Y : RatPoly} (h : PE n X Y) : (quaternionHaar n X).eqv (quaternionHaar n Y) := by
  rw [haar_phi, haar_phi]; exact h []

theorem pe_mulL (Z : RatPoly) {X Y : RatPoly} (h : PE n X Y) : PE n (polyMul Z X) (polyMul Z Y) :=
  fun m => Q'.eqv_trans _ _ _ (phi_mul n Z X m) (Q'.eqv_trans _ _ _
    (sm_congr Z fun _ _ => Q'.mul_eqv_congr_left _ _ _ (h _)) (Q'.eqv_symm (phi_mul n Z Y m)))

theorem pe_append {X X' Y Y' : RatPoly} (h : PE n X X') (h' : PE n Y Y') :
    PE n (X ++ Y) (X' ++ Y') := fun m =>
  Q'.eqv_trans _ _ _ (sm_append _ X Y) (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (h m) (h' m)) (Q'.eqv_symm (sm_append _ X' Y')))

/-- Both orders expand to the same double sum. -/
theorem phi_mul2 (X Y : RatPoly) (m : List Nat) :
    (phi n (polyMul X Y) m).eqv (sm (fun x => sm (fun y : List Nat × Q' =>
      x.2 * (y.2 * quaternionHaarMono n (monoMul m (monoMul x.1 y.1)))) Y) X) := by
  refine Q'.eqv_trans _ _ _ (phi_mul n X Y m) (sm_congr X fun x _ => ?_)
  refine Q'.eqv_trans _ _ _ (sm_mul _ _ Y) (sm_congr Y fun y _ => ?_)
  show (x.2 * (y.2 * quaternionHaarMono n (monoMul (monoMul m x.1) y.1))).eqv _
  rw [monoMul_assoc]; exact Q'.eqv_refl _

theorem pe_comm (X Y : RatPoly) : PE n (polyMul X Y) (polyMul Y X) := fun m => by
  refine Q'.eqv_trans _ _ _ (phi_mul2 n X Y m) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (phi_mul2 n Y X m))
  refine Q'.eqv_trans _ _ _ (sm_swap _ Y X) (sm_congr Y fun y _ => sm_congr X fun x _ => ?_)
  rw [monoMul_comm x.1 y.1]
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
    (fun | 0 => x.2 | 1 => y.2 | _ => quaternionHaarMono n (monoMul m (monoMul y.1 x.1)))

theorem pe_mulR (Z : RatPoly) {X Y : RatPoly} (h : PE n X Y) : PE n (polyMul X Z) (polyMul Y Z) :=
  pe_trans n (pe_comm n X Z) (pe_trans n (pe_mulL n Z h) (pe_comm n Z Y))

theorem pe_assoc (X Y Z : RatPoly) :
    PE n (polyMul (polyMul X Y) Z) (polyMul X (polyMul Y Z)) := fun m => by
  refine Q'.eqv_trans _ _ _ (phi_mul n _ Z m) ?_
  refine Q'.eqv_trans _ _ _ (sm_flatMap _ _ X) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (phi_mul n X _ m))
  refine sm_congr X fun x _ => ?_
  rw [sm_map]
  refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (phi_mul n Y Z _)))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (sm_mul _ _ Y))
  refine sm_congr Y fun y _ => ?_
  show ((x.2 * y.2) * phi n Z (monoMul m (monoMul x.1 y.1))).eqv
    (x.2 * (y.2 * phi n Z (monoMul (monoMul m x.1) y.1)))
  rw [monoMul_assoc]; exact Q'.mul_assoc_eqv _ _ _

theorem monoMul_nil_right : ∀ m : List Nat, monoMul m [] = m
  | [] => rfl
  | _ :: _ => rfl

theorem pe_const (c : Q') (hc : c.eqv 1) (X : RatPoly) : PE n (polyMul [([], c)] X) X := fun m => by
  refine Q'.eqv_trans _ _ _ (phi_mul n _ X m) ?_
  show (c * phi n X (monoMul m []) + 0).eqv _
  rw [monoMul_nil_right]
  let V := PolyExpr.var
  refine Q'.eqv_trans _ (1 * phi n X m + 0) _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.eqv_refl 0)) ?_
  exact poly_identity_of_normal_eq (PolyExpr.const 1 * V 0 + PolyExpr.const 0) (V 0) (by decide)
    (fun _ => phi n X m)

theorem pe_one (X : RatPoly) : PE n (polyMul X polyOne) X :=
  pe_trans n (pe_comm n X polyOne) (pe_const n 1 (Q'.eqv_refl 1) X)

/-- Pull one factor of a product to the front. -/
theorem pe_extract (G : Z4Plaq → RatPoly) (q : Z4Plaq) (Q₂ : List Z4Plaq) :
    ∀ Q₁ : List Z4Plaq, PE n (prodPoly G (Q₁ ++ q :: Q₂)) (polyMul (G q) (prodPoly G (Q₁ ++ Q₂)))
  | [] => pe_refl n _
  | x :: Q₁ => by
    show PE n (polyMul (G x) (prodPoly G (Q₁ ++ q :: Q₂)))
      (polyMul (G q) (polyMul (G x) (prodPoly G (Q₁ ++ Q₂))))
    refine pe_trans n (pe_mulL n (G x) (pe_extract G q Q₂ Q₁)) ?_
    refine pe_trans n (pe_symm n (pe_assoc n _ _ _)) ?_
    exact pe_trans n (pe_mulR n _ (pe_comm n _ _)) (pe_assoc n _ _ _)

end YMGap.Continuum.SU2HaarAlgebra
