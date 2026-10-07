/-
# R1 commit 16: the two-root formula for the truncated χ₁ correlator

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.  The Wilson counterpart of the polymer decay is Realizer's
`SU2WilsonLinkDecay`.

* `diff_root`: if u = z off a block B of pairwise-incompatible polymers,
  `Ξ(u;H) − Ξ(z;H) ≈ Σ_{b∈H, B b} (u_b − z_b)·Ξ(z; H ∩ cpt b)`.
* `two_root`: a nested root split, by p first and then by q.  Here `A` is the set of polymers
  through p and `Bq` the set of polymers through q.  With `d⁰_a = u^p_a − z_a`,
  `η_b = u^q_b − z_b` and `ε_a = (u^{pq}_a − u^q_a) − d⁰_a`:
  `Ξ(u^{pq})Ξ(z) − Ξ(u^p)Ξ(u^q) ≈ Σ_{a∈A} d⁰_a Σ_{b∈Bq} η_b K(a,b) + Σ_{a∈A} ε_a Ξ(u^q;G_a)Ξ(z;G)`.
  Here `K(a,b) = T(b,a;G)` if a and b are compatible, and `−Ξ(G_b)Ξ(G_a)` if they are not.
  Also, `ε_a = 0` unless a contains both p and q.
* `two_root_obs`: the instance on the observable activities z^S of `SU2ObsInsertion`, together
  with `trunc_eq_Xi`, giving `Zpq·Z − Zp·Zq ≈` the right-hand side above.
-/

import YMGap.Continuum.SU2ObsRoot
import YMGap.Continuum.PolymerRemovalChain

namespace YMGap.Continuum.SU2TwoRoot

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2HaarAlgebra (sm sm_congr)
open YMGap.Continuum.SignedPolymerKP (Xi cpt)
open YMGap.Continuum.SizeWeightedPolymerKP (sumd)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkKP (Xi_congr)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2ObsInsertion
open YMGap.Continuum.SU2ObsRoot (root_split sm_sub hasP inc_of_mem)
open YMGap.Continuum.PolymerRemovalChain (T filter_comm)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## Finite-sum helpers -/

theorem sm_eq {β : Type} (f : β → Q') : ∀ l : List β, sm f l = sumd f l
  | [] => rfl
  | a :: l => by show f a + sm f l = f a + sumd f l; rw [sm_eq f l]

theorem sumd_congr {β : Type} {f g : β → Q'} : ∀ l : List β, (∀ a ∈ l, (f a).eqv (g a)) →
    (sumd f l).eqv (sumd g l) := fun l h => by rw [← sm_eq, ← sm_eq]; exact sm_congr l h

theorem sumd_add {β : Type} (f g : β → Q') : ∀ l : List β,
    (sumd f l + sumd g l).eqv (sumd (fun a => f a + g a) l)
  | [] => by show ((0 : Q') + 0).eqv 0; decide
  | a :: l => by
    refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sumd_add f g l))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + V 1 + (V 2 + V 3)) (V 0 + V 2 + (V 1 + V 3)) (by decide)
      (fun | 0 => f a | 1 => sumd f l | 2 => g a | _ => sumd g l)

theorem sumd_sub {β : Type} (f g : β → Q') (l : List β) :
    (sumd f l + -(sumd g l)).eqv (sumd (fun a => f a + -g a) l) := by
  rw [← sm_eq, ← sm_eq, ← sm_eq]; exact sm_sub f g l

theorem sumd_mulR {β : Type} (f : β → Q') (c : Q') : ∀ l : List β,
    (sumd f l * c).eqv (sumd (fun a => f a * c) l)
  | [] => by show ((0 : Q') * c).eqv 0; exact Q'.zero_mul_eqv c
  | a :: l => by
    refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sumd_mulR f c l))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq ((V 0 + V 1) * V 2) (V 0 * V 2 + V 1 * V 2) (by decide)
      (fun | 0 => f a | 1 => sumd f l | _ => c)

theorem sumd_mulL {β : Type} (f : β → Q') (c : Q') (l : List β) :
    (c * sumd f l).eqv (sumd (fun a => c * f a) l) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.eqv_trans _ _ _ (sumd_mulR f c l)
    (sumd_congr l fun _ _ => Q'.mul_comm_eqv _ _))

theorem sumd_filter {β : Type} (f : β → Q') (c : β → Bool) : ∀ l : List β,
    (sumd f (l.filter c)).eqv (sumd (fun b => if c b = true then f b else 0) l)
  | [] => Q'.eqv_refl _
  | a :: l => by
    cases h : c a
    · rw [List.filter_cons_of_neg (by simp [h])]
      show (sumd f (l.filter c)).eqv ((if c a = true then f a else 0) + sumd (fun b => if c b = true then f b else 0) l)
      rw [if_neg (by simp [h])]
      rw [Q'.zero_add']; exact sumd_filter f c l
    · rw [List.filter_cons_of_pos h]
      show (f a + _).eqv ((if c a = true then f a else 0) + _)
      rw [if_pos h]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (sumd_filter f c l)

variable (N : Nat)

/-! ## One-block difference -/

theorem filter_drop (b : List Z4Plaq) (B : List Z4Plaq → Bool) : ∀ H : List (List Z4Plaq),
    (∀ x, x ∈ H → B x = true → incL N b x = true) →
    (H.filter (fun x => !B x)).filter (cpt (incL N) b) = H.filter (cpt (incL N) b)
  | [], _ => rfl
  | x :: H, h => by
    have ih := filter_drop b B H (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hb : B x
    · simp only [List.filter_cons, hb, Bool.not_false, if_true]
      split <;> simp_all
    · have hi := h x List.mem_cons_self hb
      simp only [List.filter_cons, hb, Bool.not_true, cpt, hi]
      simp_all

/-- **One-block difference formula (PROVED).** -/
theorem diff_root (z u : List Z4Plaq → Q') (B : List Z4Plaq → Bool) (H : List (List Z4Plaq))
    (hB : ∀ a, a ∈ H → B a = true → ∀ b, b ∈ H → B b = true → incL N a b = true)
    (hoff : ∀ x, x ∈ H → B x = false → u x = z x) :
    (Xi u (incL N) H + -Xi z (incL N) H).eqv
      (sumd (fun b => (u b + -z b) * Xi z (incL N) (H.filter (cpt (incL N) b))) (H.filter B)) := by
  let H0 := H.filter (fun x => !B x)
  have cg : ∀ L : List (List Z4Plaq), (∀ x, x ∈ L → x ∈ H0) → Xi u (incL N) L = Xi z (incL N) L :=
    fun L hL => Xi_congr _ _ _ L.length L (Nat.le_refl _) fun a ha => by
      have h := List.mem_filter.mp (hL a ha)
      exact hoff a h.1 (by simpa using h.2)
  have eu := root_split N u B H hB
  have ez := root_split N z B H hB
  rw [cg H0 (fun _ h => h)] at eu
  have eu' : (Xi u (incL N) H).eqv (Xi z (incL N) H0 +
      sm (fun a => u a * Xi z (incL N) (H0.filter (cpt (incL N) a))) (H.filter B)) :=
    Q'.eqv_trans _ _ _ eu (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_congr _ fun a _ => by
      rw [cg _ (fun x hx => (List.mem_filter.mp hx).1)]; exact Q'.eqv_refl _))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' eu' (Q'.neg_eqv_congr _ _ ez)) ?_
  let X := fun a => Xi z (incL N) (H0.filter (cpt (incL N) a))
  rw [sm_eq, sm_eq]
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_trans _ _ _
    (sumd_sub (fun a => u a * X a) (fun a => z a * X a) _) (sumd_congr _ fun a ha => ?_))
  · let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + V 1 + -(V 0 + V 2)) (V 1 + -V 2) (by decide)
      (fun | 0 => Xi z (incL N) H0 | 1 => sumd (fun a => u a * X a) (H.filter B)
           | _ => sumd (fun a => z a * X a) (H.filter B))
  · have hm := List.mem_filter.mp ha
    show (u a * X a + -(z a * X a)).eqv _
    have e : X a = Xi z (incL N) (H.filter (cpt (incL N) a)) := by
      show Xi z (incL N) (H0.filter _) = _
      rw [filter_drop N a B H (fun x hx hbx => hB a hm.1 hm.2 x hx hbx)]
    rw [e]
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 2 + -(V 1 * V 2)) ((V 0 + -V 1) * V 2) (by decide)
      (fun | 0 => u a | 1 => z a | _ => Xi z (incL N) (H.filter (cpt (incL N) a)))

/-! ## The two-root formula -/

/-- Pair kernel: `T(b,a;G)` for compatible a, b, and `−Ξ(G_b)Ξ(G_a)` otherwise. -/
def K (z : List Z4Plaq → Q') (G : List (List Z4Plaq)) (a b : List Z4Plaq) : Q' :=
  if cpt (incL N) a b = true then T z (incL N) b a G
  else -(Xi z (incL N) (G.filter (cpt (incL N) b)) * Xi z (incL N) (G.filter (cpt (incL N) a)))

/-- **Two-root formula (PROVED).** -/
theorem two_root (z up uq upq : List Z4Plaq → Q') (B1 B2 : List Z4Plaq → Bool) (G : List (List Z4Plaq))
    (hB1 : ∀ a, a ∈ G → B1 a = true → ∀ b, b ∈ G → B1 b = true → incL N a b = true)
    (hB2 : ∀ a, a ∈ G → B2 a = true → ∀ b, b ∈ G → B2 b = true → incL N a b = true)
    (h1 : ∀ x, x ∈ G → B1 x = false → up x = z x ∧ upq x = uq x)
    (h2 : ∀ x, x ∈ G → B2 x = false → uq x = z x) :
    (Xi upq (incL N) G * Xi z (incL N) G + -(Xi up (incL N) G * Xi uq (incL N) G)).eqv
      (sumd (fun a => (up a + -z a) * sumd (fun b => (uq b + -z b) * K N z G a b) (G.filter B2))
          (G.filter B1) +
        sumd (fun a => (upq a + -uq a + -(up a + -z a)) * Xi uq (incL N) (G.filter (cpt (incL N) a)) *
          Xi z (incL N) G) (G.filter B1)) := by
  let X := fun (v : List Z4Plaq → Q') (L : List (List Z4Plaq)) => Xi v (incL N) L
  let Ga := fun a => G.filter (cpt (incL N) a)
  have E1 := diff_root N uq upq B1 G hB1 (fun x hx hb => (h1 x hx hb).2)
  have E0 := diff_root N z up B1 G hB1 (fun x hx hb => (h1 x hx hb).1)
  have I0 := diff_root N z uq B2 G hB2 h2
  let d1 := fun a => upq a + -uq a
  let d0 := fun a => up a + -z a
  let η := fun b => uq b + -z b
  -- step A: pure algebra
  have sA : (X upq G * X z G + -(X up G * X uq G)).eqv
      ((X upq G + -X uq G) * X z G + -((X up G + -X z G) * X uq G)) := by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 2 * V 3)) ((V 0 + -V 3) * V 1 + -((V 2 + -V 1) * V 3))
      (by decide) (fun | 0 => X upq G | 1 => X z G | 2 => X up G | _ => X uq G)
  refine Q'.eqv_trans _ _ _ sA ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ E1)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ E0))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sumd_mulR _ _ _) (Q'.neg_eqv_congr _ _ (sumd_mulR _ _ _))) ?_
  refine Q'.eqv_trans _ _ _ (sumd_sub _ _ _) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (sumd_add _ _ _))
  refine sumd_congr _ fun a ha => ?_
  have hm := List.mem_filter.mp ha
  -- inner difference on G_a
  have I1 := diff_root N z uq B2 (Ga a)
    (fun x hx hx' y hy hy' => hB2 x (List.mem_filter.mp hx).1 hx' y (List.mem_filter.mp hy).1 hy')
    (fun x hx hb => h2 x (List.mem_filter.mp hx).1 hb)
  have inner : ((X uq (Ga a) + -X z (Ga a)) * X z G + -(X z (Ga a) * (X uq G + -X z G))).eqv
      (sumd (fun b => η b * K N z G a b) (G.filter B2)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ I1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ I0))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sumd_mulR _ _ _) (Q'.neg_eqv_congr _ _ (sumd_mulL _ _ _))) ?_
    have hf : (Ga a).filter B2 = (G.filter B2).filter (cpt (incL N) a) := filter_comm _ _ G
    rw [hf]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sumd_filter _ _ _) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ _ _ (sumd_sub _ _ _) (sumd_congr _ fun b _ => ?_)
    show (_ + -(X z (Ga a) * (η b * X z (G.filter (cpt (incL N) b))))).eqv (η b * K N z G a b)
    unfold K
    cases hc : cpt (incL N) a b
    · simp only [Bool.false_eq_true, if_false]
      rw [Q'.zero_add']
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (-(V 0 * (V 1 * V 2))) (V 1 * -(V 2 * V 0)) (by decide)
        (fun | 0 => X z (Ga a) | 1 => η b | _ => X z (G.filter (cpt (incL N) b)))
    · simp only [if_true]
      show (η b * X z ((Ga a).filter (cpt (incL N) b)) * X z G + _).eqv
        (η b * (X z G * X z ((Ga a).filter (cpt (incL N) b)) + -(X z (G.filter (cpt (incL N) b)) * X z (Ga a))))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 1 * V 3 * V 4 + -(V 0 * (V 1 * V 2)))
        (V 1 * (V 4 * V 3 + -(V 2 * V 0))) (by decide)
        (fun | 0 => X z (Ga a) | 1 => η b | 2 => X z (G.filter (cpt (incL N) b))
             | 3 => X z ((Ga a).filter (cpt (incL N) b)) | _ => X z G)
  show (d1 a * X uq (Ga a) * X z G + -(d0 a * X z (Ga a) * X uq G)).eqv
    (d0 a * sumd (fun b => η b * K N z G a b) (G.filter B2) + (d1 a + -d0 a) * X uq (Ga a) * X z G)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ inner) (Q'.eqv_refl _))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 2 * V 3 + -(V 1 * V 4 * V 5))
    (V 1 * ((V 2 + -V 4) * V 3 + -(V 4 * (V 5 + -V 3))) + (V 0 + -V 1) * V 2 * V 3) (by decide)
    (fun | 0 => d1 a | 1 => d0 a | 2 => X uq (Ga a) | 3 => X z G | 4 => X z (Ga a) | _ => X uq G)

/-! ## Observable instance -/

variable (w : Q') (M : Nat) (links : List Z4Link)

theorem prod_agree (S S' : List Z4Plaq) : ∀ γ : List Z4Plaq, (∀ r, r ∈ γ → (r ∈ S ↔ r ∈ S')) →
    prodPoly (gObs w M links N S) γ = prodPoly (gObs w M links N S') γ
  | [], _ => rfl
  | r :: γ, h => by
    show polyMul _ _ = polyMul _ _
    rw [prod_agree S S' γ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have e : gObs w M links N S r = gObs w M links N S' r := by
      unfold gObs
      by_cases hr : r ∈ S
      · rw [if_pos hr, if_pos ((h r List.mem_cons_self).mp hr)]
      · rw [if_neg hr, if_neg (fun h' => hr ((h r List.mem_cons_self).mpr h'))]
    rw [e]

theorem zObs_agree (S S' γ : List Z4Plaq) (h : ∀ r, r ∈ γ → (r ∈ S ↔ r ∈ S')) :
    zObs w M links N S γ = zObs w M links N S' γ := by
  unfold zObs; rw [prod_agree N w M links S S' γ h]

theorem hasP_false {p : Z4Plaq} {x : List Z4Plaq} (h : hasP p x = false) : p ∉ x := by
  intro hp; simp [hasP, hp] at h

/-- **Two-root formula for the truncated χ₁ correlator (PROVED).**  With
`Z, Zp, Zq, Zpq` as in `trunc_eq_Xi`, `z^S = zObs S`, G = gas, A = polymers through p and
Bq = polymers through q. -/
theorem two_root_obs (P : List Z4Plaq) (hL : ∀ r ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N r)
    (p q : Z4Plaq) :
    let Z := ZObs w M links N P []
    let Zp := ZObs w M links N P [p] + -Z
    let Zq := ZObs w M links N P [q] + -Z
    let Zpq := ZObs w M links N P [p, q] + -ZObs w M links N P [p] + -ZObs w M links N P [q] + Z
    let z := zObs w M links N []
    let G := gas N P
    (Zpq * Z + -(Zp * Zq)).eqv
      (sumd (fun a => (zObs w M links N [p] a + -z a) *
          sumd (fun b => (zObs w M links N [q] b + -z b) * K N z G a b) (G.filter (hasP q)))
          (G.filter (hasP p)) +
        sumd (fun a => (zObs w M links N [p, q] a + -zObs w M links N [q] a +
            -(zObs w M links N [p] a + -z a)) *
          Xi (zObs w M links N [q]) (incL N) (G.filter (cpt (incL N) a)) * Xi z (incL N) G)
          (G.filter (hasP p))) := by
  intro Z Zp Zq Zpq z G
  refine Q'.eqv_trans _ _ _ (trunc_eq_Xi w M links N P hL p q) ?_
  have hB : ∀ s : Z4Plaq, ∀ a, a ∈ G → hasP s a = true → ∀ b, b ∈ G → hasP s b = true →
      incL N a b = true :=
    fun _ a _ ha b _ hb => inc_of_mem N (of_decide_eq_true ha) (of_decide_eq_true hb)
  refine two_root N z _ _ _ (hasP p) (hasP q) G (hB p) (hB q) (fun x _ hx => ⟨?_, ?_⟩) (fun x _ hx => ?_)
  · exact zObs_agree N w M links _ _ x fun r hr => by
      have := hasP_false hx
      constructor
      · intro h; rw [List.mem_singleton.mp h] at hr; exact absurd hr this
      · intro h; exact absurd h List.not_mem_nil
  · exact zObs_agree N w M links _ _ x fun r hr => by
      have := hasP_false hx
      have hrp : r ≠ p := fun e => this (e ▸ hr)
      simp [hrp]
  · exact zObs_agree N w M links _ _ x fun r hr => by
      have := hasP_false hx
      constructor
      · intro h; rw [List.mem_singleton.mp h] at hr; exact absurd hr this
      · intro h; exact absurd h List.not_mem_nil

end YMGap.Continuum.SU2TwoRoot
