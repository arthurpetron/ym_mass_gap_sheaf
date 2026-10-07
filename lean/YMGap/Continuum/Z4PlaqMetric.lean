/-
# ℓ∞ plaquette metrics on the Z4 box and torus (commit C, part 2)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).

* `boxMetric : PlaqMetric z4Chain`: ℓ∞ distance of base vertices, `max_i |p_i − q_i|`.
* `torusMetric N : PlaqMetric (torusChain N)`: torus-wrapped ℓ∞ distance,
  `max_i min(|p̄_i − q̄_i|, N − |p̄_i − q̄_i|)` with `x̄ = x mod N`.

For either metric, plaquettes sharing a link are at distance `≤ 1`.  So `lattice_decay` applies
with `R = dist(supp y, supp g)`.
-/

import YMGap.Continuum.PolymerLatticeDecay
import YMGap.Continuum.Z4TorusPolymerKP

namespace YMGap.Continuum.Z4PlaqMetric

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.PolymerLatticeDecay
open YMGap.Constructive
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.HeatKernelPolymerActivityR1

/-- Coordinatewise max of a coordinate distance. -/
def ld4 (cd : Nat → Nat → Nat) (u v : Z4Vertex) : Nat :=
  max (max (cd u.1 v.1) (cd u.2.1 v.2.1)) (max (cd u.2.2.1 v.2.2.1) (cd u.2.2.2 v.2.2.2))

theorem ld4_self (cd : Nat → Nat → Nat) (h : ∀ a, cd a a = 0) (u : Z4Vertex) : ld4 cd u u = 0 := by
  unfold ld4; rw [h, h, h, h]; rfl

theorem ld4_tri (cd : Nat → Nat → Nat) (h : ∀ a b c, cd a c ≤ cd a b + cd b c) (u v w : Z4Vertex) :
    ld4 cd u w ≤ ld4 cd u v + ld4 cd v w := by
  unfold ld4
  have := h u.1 v.1 w.1; have := h u.2.1 v.2.1 w.2.1
  have := h u.2.2.1 v.2.2.1 w.2.2.1; have := h u.2.2.2 v.2.2.2 w.2.2.2
  omega

/-- `w` is `v` or a one-step successor of `v` (successor `sc`) in each coordinate. -/
def near (sc : Nat → Nat) (v w : Z4Vertex) : Prop :=
  (w.1 = v.1 ∨ w.1 = sc v.1) ∧ (w.2.1 = v.2.1 ∨ w.2.1 = sc v.2.1) ∧
  (w.2.2.1 = v.2.2.1 ∨ w.2.2.1 = sc v.2.2.1) ∧ (w.2.2.2 = v.2.2.2 ∨ w.2.2.2 = sc v.2.2.2)

theorem near_refl (sc : Nat → Nat) (v : Z4Vertex) : near sc v v :=
  ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem near_edges (sc : Nat → Nat) (st : Z4Vertex → Dir4 → Z4Vertex)
    (hst : ∀ v μ, near sc v (st v μ)) (p : Z4Plaq) (ℓ : Z4Link)
    (h : ℓ ∈ [(p.1, (dirsOf p.2).1), (p.1, (dirsOf p.2).2),
      (st p.1 (dirsOf p.2).2, (dirsOf p.2).1), (st p.1 (dirsOf p.2).1, (dirsOf p.2).2)]) :
    near sc p.1 ℓ.1 := by
  rcases List.mem_cons.mp h with e | h
  · rw [e]; exact near_refl sc _
  rcases List.mem_cons.mp h with e | h
  · rw [e]; exact near_refl sc _
  rcases List.mem_cons.mp h with e | h
  · rw [e]; exact hst _ _
  rcases List.mem_cons.mp h with e | h
  · rw [e]; exact hst _ _
  exact absurd h List.not_mem_nil

theorem ld4_le_one (cd : Nat → Nat → Nat) (sc : Nat → Nat) (u v l : Z4Vertex)
    (hc : ∀ a b x, (x = a ∨ x = sc a) → (x = b ∨ x = sc b) → cd a b ≤ 1)
    (hu : near sc u l) (hv : near sc v l) : ld4 cd u v ≤ 1 := by
  unfold ld4
  have := hc _ _ _ hu.1 hv.1; have := hc _ _ _ hu.2.1 hv.2.1
  have := hc _ _ _ hu.2.2.1 hv.2.2.1; have := hc _ _ _ hu.2.2.2 hv.2.2.2
  omega

/-! ## Box -/

def dn (a b : Nat) : Nat := (a - b) + (b - a)

theorem near_addE (v : Z4Vertex) (μ : Dir4) : near Nat.succ v (addE v μ) := by
  obtain ⟨a, b, c, d⟩ := v
  cases μ
  · exact ⟨Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩

/-- **The box ℓ∞ plaquette metric (PROVED).** -/
def boxMetric : PlaqMetric z4Chain where
  ld p q := ld4 dn p.1 q.1
  self p := ld4_self dn (fun a => by unfold dn; omega) p.1
  tri p q r := ld4_tri dn (fun a b c => by unfold dn; omega) p.1 q.1 r.1
  adj p q h := ld4_le_one dn Nat.succ p.1 q.1 h.link.1
    (fun a b x h1 h2 => by unfold dn; omega)
    (near_edges Nat.succ addE near_addE p h.link (of_decide_eq_true h.on_p))
    (near_edges Nat.succ addE near_addE q h.link (of_decide_eq_true h.on_q))

/-! ## Torus -/

def tw (N a b : Nat) : Nat := min (dn (a % N) (b % N)) (N - dn (a % N) (b % N))

theorem mod_cases (N a : Nat) : a % N < N ∨ N = 0 := by
  cases N with
  | zero => exact Or.inr rfl
  | succ n => exact Or.inl (Nat.mod_lt _ (Nat.succ_pos n))

theorem tw_self (N a : Nat) : tw N a a = 0 := by unfold tw dn; omega

theorem tw_tri (N a b c : Nat) : tw N a c ≤ tw N a b + tw N b c := by
  unfold tw dn
  have ha := mod_cases N a; have hb := mod_cases N b; have hc := mod_cases N c
  generalize a % N = x at *; generalize b % N = y at *; generalize c % N = w at *
  omega

theorem succ_mod {N x : Nat} (hx : x < N) : (x + 1) % N = x + 1 ∨ (x + 1 = N ∧ (x + 1) % N = 0) := by
  rcases Nat.lt_or_ge (x + 1) N with h | h
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · have e : x + 1 = N := Nat.le_antisymm hx h
    exact Or.inr ⟨e, by rw [e]; exact Nat.mod_self N⟩

theorem tw_adj (N a b x : Nat) (ha : a < N) (hb : b < N)
    (h1 : x = a ∨ x = (a + 1) % N) (h2 : x = b ∨ x = (b + 1) % N) : tw N a b ≤ 1 := by
  unfold tw dn
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have sa := succ_mod ha; have sb := succ_mod hb
  generalize (a + 1) % N = u at *; generalize (b + 1) % N = v at *
  omega

theorem near_tAdd (N : Nat) (v : Z4Vertex) (μ : Dir4) : near (fun x => (x + 1) % N) v (tAdd N v μ) := by
  obtain ⟨a, b, c, d⟩ := v
  cases μ
  · exact ⟨Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩
  · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩

theorem box_parts {N : Nat} {p : Z4Plaq} {ℓ : Z4Link} (h : torusBoundary N p ℓ = true) :
    InBox N p.1 ∧ ℓ ∈ torusEdgesOf N p := by
  unfold torusBoundary at h
  rw [Bool.and_eq_true] at h
  exact ⟨inBox_of N p.1 h.1, of_decide_eq_true h.2⟩

/-- **The torus-wrapped ℓ∞ plaquette metric (PROVED).** -/
def torusMetric (N : Nat) : PlaqMetric (torusChain N) where
  ld p q := ld4 (tw N) p.1 q.1
  self p := ld4_self (tw N) (tw_self N) p.1
  tri p q r := ld4_tri (tw N) (tw_tri N) p.1 q.1 r.1
  adj p q h := by
    have hp := box_parts h.on_p
    have hq := box_parts h.on_q
    have np := near_edges _ (tAdd N) (near_tAdd N) p h.link hp.2
    have nq := near_edges _ (tAdd N) (near_tAdd N) q h.link hq.2
    show ld4 (tw N) p.1 q.1 ≤ 1
    unfold ld4
    have := tw_adj N _ _ _ hp.1.1 hq.1.1 np.1 nq.1
    have := tw_adj N _ _ _ hp.1.2.1 hq.1.2.1 np.2.1 nq.2.1
    have := tw_adj N _ _ _ hp.1.2.2.1 hq.1.2.2.1 np.2.2.1 nq.2.2.1
    have := tw_adj N _ _ _ hp.1.2.2.2 hq.1.2.2.2 np.2.2.2 nq.2.2.2
    omega

/-! ## Concrete corollaries: zHeat at w = 1/40, rate (6/7)^R in ℓ∞ lattice separation R -/

/-- **Box (PROVED).** -/
theorem zheat_box_decay (d0 : Z4Plaq) (B : Z4BoxGas z4Chain) (M : Nat) (y g : Poly z4Chain)
    (l : List (Poly z4Chain)) (R : Nat) (hsep : sepL boxMetric y g R)
    (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U (zHeat M) shareB y g l) ≤
      (lam ^ R * etaL ^ sz g) * (Xi (zHeat M) shareB l * Xi (zHeat M) shareB (g :: l)) :=
  zheat_lattice_decay boxMetric rfl d0 B M y g l R hsep hG

/-- **Torus, every N (PROVED).** -/
theorem zheat_torus_decay (N : Nat) (d0 : Z4Plaq) (B : Z4BoxGas (torusChain N)) (M : Nat)
    (y g : Poly (torusChain N)) (l : List (Poly (torusChain N))) (R : Nat)
    (hsep : sepL (torusMetric N) y g R) (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U (zHeat M) shareB y g l) ≤
      (lam ^ R * etaL ^ sz g) * (Xi (zHeat M) shareB l * Xi (zHeat M) shareB (g :: l)) :=
  zheat_lattice_decay (torusMetric N) rfl d0 B M y g l R hsep hG

end YMGap.Continuum.Z4PlaqMetric
