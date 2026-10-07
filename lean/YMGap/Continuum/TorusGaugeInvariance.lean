/-
# Gauge invariance of the torus Wilson action (class-function weights)

ADDITIVE; proved algebra over `RepTheory.ConstructiveGroup` (setoid laws only).

* Gauge transform `g : Z4Vertex → G.Carrier`:
  `(g·U)(w,a) = g(w) · U(w,a) · g(w+â)⁻¹` (periodic `tAdd`).
* `holonomy_gauge`: `hol_{g·U}(w,P) ≈ g(w) · hol_U(w,P) · g(w)⁻¹` (setoid).
  Uses `tAdd_comm` (the plaquette's far corner is reached either way).
* `ClassFunction G`: weight `f` respecting the setoid with `f(ghg⁻¹) ≈ f(h)`.
* `wilsonAction_gauge_invariant`: `S_f(g·U) ≈ S_f(U)` for every class function.

Group-generic (U(1) satisfies it too): structural, not a gap input.
Choice-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.TorusWilsonAction

namespace YMGap.Continuum.TorusGaugeInvariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.TorusWilsonAction
open YMGap.RepTheory

section GroupAlgebra

variable (G : ConstructiveGroup.{0})

local infix:50 " ≋ " => G.setoid.r

theorem gsymm {x y : G.Carrier} (h : x ≋ y) : y ≋ x := G.setoid.iseqv.symm h
theorem gtrans {x y z : G.Carrier} (h1 : x ≋ y) (h2 : y ≋ z) : x ≋ z :=
  G.setoid.iseqv.trans h1 h2
theorem grefl (x : G.Carrier) : x ≋ x := G.setoid.iseqv.refl x

theorem cancel_inv_right (a h : G.Carrier) : G.mul (G.mul a (G.inv h)) h ≋ a :=
  gtrans G (G.mul_assoc _ _ _)
    (gtrans G (G.mul_congr (grefl G a) (G.inv_mul h)) (G.mul_one a))

theorem cancel_right (a h : G.Carrier) : G.mul (G.mul a h) (G.inv h) ≋ a :=
  gtrans G (G.mul_assoc _ _ _)
    (gtrans G (G.mul_congr (grefl G a) (G.mul_inv h)) (G.mul_one a))

/-- `t a u b = a · u · b⁻¹`. -/
def tw (a u b : G.Carrier) : G.Carrier := G.mul (G.mul a u) (G.inv b)

theorem tw_pair (a u h v b : G.Carrier) :
    G.mul (tw G a u h) (tw G h v b) ≋ tw G a (G.mul u v) b := by
  unfold tw
  have s1 : G.mul (G.mul (G.mul a u) (G.inv h)) (G.mul h v) ≋ G.mul a (G.mul u v) :=
    gtrans G (gsymm G (G.mul_assoc _ _ _))
      (gtrans G (G.mul_congr (cancel_inv_right G _ h) (grefl G v)) (G.mul_assoc _ _ _))
  exact gtrans G (gsymm G (G.mul_assoc _ _ _)) (G.mul_congr s1 (grefl G _))

theorem inv_mul_rev (x y : G.Carrier) :
    G.inv (G.mul x y) ≋ G.mul (G.inv y) (G.inv x) := by
  have hprod : G.mul (G.mul x y) (G.mul (G.inv y) (G.inv x)) ≋ G.one :=
    gtrans G (gsymm G (G.mul_assoc _ _ _))
      (gtrans G (G.mul_congr (cancel_right G x y) (grefl G _)) (G.mul_inv x))
  have a1 : G.inv (G.mul x y) ≋ G.mul (G.inv (G.mul x y)) G.one := gsymm G (G.mul_one _)
  have a2 := G.mul_congr (grefl G (G.inv (G.mul x y))) (gsymm G hprod)
  have a3 := gsymm G (G.mul_assoc (G.inv (G.mul x y)) (G.mul x y)
    (G.mul (G.inv y) (G.inv x)))
  have a4 := G.mul_congr (G.inv_mul (G.mul x y)) (grefl G (G.mul (G.inv y) (G.inv x)))
  exact gtrans G a1 (gtrans G a2 (gtrans G a3 (gtrans G a4 (G.one_mul _))))

theorem inv_inv (x : G.Carrier) : G.inv (G.inv x) ≋ x := by
  have a1 : G.inv (G.inv x) ≋ G.mul (G.inv (G.inv x)) G.one := gsymm G (G.mul_one _)
  have a2 := G.mul_congr (grefl G (G.inv (G.inv x))) (gsymm G (G.inv_mul x))
  have a3 := gsymm G (G.mul_assoc (G.inv (G.inv x)) (G.inv x) x)
  have a4 := G.mul_congr (G.inv_mul (G.inv x)) (grefl G x)
  exact gtrans G a1 (gtrans G a2 (gtrans G a3 (gtrans G a4 (G.one_mul x))))

theorem tw_inv (a u b : G.Carrier) : G.inv (tw G a u b) ≋ tw G b (G.inv u) a := by
  unfold tw
  have a1 := inv_mul_rev G (G.mul a u) (G.inv b)
  have a2 := G.mul_congr (inv_inv G b) (inv_mul_rev G a u)
  exact gtrans G a1 (gtrans G a2 (gsymm G (G.mul_assoc _ _ _)))

end GroupAlgebra

/-! ## Gauge transforms on the torus -/

theorem tAdd_comm (N : Nat) (w : Z4Vertex) (a b : Dir4) :
    tAdd N (tAdd N w a) b = tAdd N (tAdd N w b) a := by
  obtain ⟨x, y, z, u⟩ := w
  cases a <;> cases b <;> rfl

/-- Gauge transform `(g·U)(w,a) = g(w) · U(w,a) · g(w+â)⁻¹`. -/
def gaugeTransform (G : ConstructiveGroup.{0}) (N : Nat) (g : Z4Vertex → G.Carrier)
    (U : GaugeConfig G) : GaugeConfig G :=
  fun ℓ => tw G (g ℓ.1) (U ℓ) (g (tAdd N ℓ.1 ℓ.2))

/-- **Holonomy conjugates** under a gauge transform. -/
theorem holonomy_gauge (G : ConstructiveGroup.{0}) (N : Nat) (g : Z4Vertex → G.Carrier)
    (U : GaugeConfig G) (p : Z4Plaq) :
    G.setoid.r (holonomy G N (gaugeTransform G N g U) p)
      (tw G (g p.1) (holonomy G N U p) (g p.1)) := by
  obtain ⟨w, P⟩ := p
  unfold holonomy gaugeTransform
  simp only []
  rw [tAdd_comm N w (dirsOf P).2 (dirsOf P).1]
  have h12 := tw_pair G (g w) (U (w, (dirsOf P).1)) (g (tAdd N w (dirsOf P).1))
    (U (tAdd N w (dirsOf P).1, (dirsOf P).2)) (g (tAdd N (tAdd N w (dirsOf P).1) (dirsOf P).2))
  have i3 := tw_inv G (g (tAdd N w (dirsOf P).2)) (U (tAdd N w (dirsOf P).2, (dirsOf P).1))
    (g (tAdd N (tAdd N w (dirsOf P).1) (dirsOf P).2))
  have i4 := tw_inv G (g w) (U (w, (dirsOf P).2)) (g (tAdd N w (dirsOf P).2))
  have h34 := gtrans G (G.mul_congr i3 i4) (tw_pair G _ _ _ _ _)
  exact gtrans G (G.mul_congr h12 h34) (tw_pair G _ _ _ _ _)

/-- A setoid-respecting class function `f(ghg⁻¹) ≈ f(h)`. -/
structure ClassFunction (G : ConstructiveGroup.{0}) where
  f : G.Carrier → Q'
  congr : ∀ x y, G.setoid.r x y → (f x).eqv (f y)
  conj : ∀ g h, (f (G.mul (G.mul g h) (G.inv g))).eqv (f h)

theorem qsum_map_congr {α : Type} (f₁ f₂ : α → Q') :
    ∀ (l : List α), (∀ x, x ∈ l → (f₁ x).eqv (f₂ x)) →
      (qsum (l.map f₁)).eqv (qsum (l.map f₂))
  | [], _ => Q'.eqv_refl _
  | x :: l, h => Q'.add_eqv_congr' (h x List.mem_cons_self)
      (qsum_map_congr f₁ f₂ l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- **Gauge invariance of the torus Wilson action** for class-function weights. -/
theorem wilsonAction_gauge_invariant (G : ConstructiveGroup.{0}) (N : Nat)
    (F : ClassFunction G) (g : Z4Vertex → G.Carrier) (U : GaugeConfig G) :
    (wilsonAction G N F.f (gaugeTransform G N g U)).eqv (wilsonAction G N F.f U) :=
  qsum_map_congr _ _ _ (fun p _ =>
    Q'.eqv_trans _ _ _ (F.congr _ _ (holonomy_gauge G N g U p)) (F.conj _ _))

end YMGap.Continuum.TorusGaugeInvariance
