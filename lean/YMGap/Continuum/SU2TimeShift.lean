/-
# Transfer matrix (2f): time translation of slices and of the plaquette weight

ADDITIVE.  **Labels:** geometry and algebra, every coupling; also true for U(1), not gap evidence.

* `vs N t (a,b,c,d) = ((a+t) % N, b, c, d)` and `shv N t (v, x) = (vs N t v, x)` (links and plaquettes).
* `tAdd_vs`: `tAdd N (vs N t v) d = vs N t (tAdd N v d)`.
* `perm_shift`: for `t < N`, a slice family with membership `InBox ∧ time = s ∧ Q` satisfies
  `l t ~ (l 0).map (shv N t)`.  Instances: `ps_perm`, `pt_perm`, `v_perm`.
* `TKi ι p`: the Wilson weight with link variables placed by an arbitrary index map `ι`.
  `TK links = TKi (idxOf)`, and `tk_shift`: `TK links (shv t p) = TKi (idxOf ∘ shv t) p`.
  So the weight of a translated plaquette is the SAME polynomial function with translated
  variables.
-/

import YMGap.Continuum.SU2WilsonSliceGood
import YMGap.Continuum.SU2TorusRPPermExt

namespace YMGap.Continuum.SU2TimeShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2TorusSlice

def vs (N t : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) => ((a + t) % N, b, c, d)

def shv {β : Type} (N t : Nat) (x : Z4Vertex × β) : Z4Vertex × β := (vs N t x.1, x.2)

theorem tAdd_vs (N t : Nat) (v : Z4Vertex) (d : Dir4) : tAdd N (vs N t v) d = vs N t (tAdd N v d) := by
  obtain ⟨a, b, c, e⟩ := v
  cases d with
  | x0 =>
    show (((a + t) % N + 1) % N, b, c, e) = (((a + 1) % N + t) % N, b, c, e)
    rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]
  | x1 => rfl
  | x2 => rfl
  | x3 => rfl

theorem nodup_map_on {α : Type} (f : α → α) : ∀ l : List α, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hn => by
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_on f l
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hn).2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have := h b (List.mem_cons_of_mem _ hb) a List.mem_cons_self e
    exact (List.nodup_cons.mp hn).1 (this ▸ hb)

/-- **Slice translation as a permutation (PROVED).** -/
theorem perm_shift {β : Type} [DecidableEq β] (N t : Nat) (ht : t < N) (l : Nat → List (Z4Vertex × β))
    (Q : β → Prop) (hmem : ∀ s x, x ∈ l s ↔ InBox N x.1 ∧ x.1.1 = s ∧ Q x.2) (hnd : ∀ s, (l s).Nodup) :
    (l t).Perm ((l 0).map (shv N t)) := by
  refine YMGap.Continuum.SU2TorusRPPermExt.perm_ext' _ _ (hnd t) (nodup_map_on _ _ ?_ (hnd 0)) fun x => ?_
  · intro x hx y hy e
    obtain ⟨⟨a, b, c, d⟩, P⟩ := x
    obtain ⟨⟨a', b', c', d'⟩, P'⟩ := y
    have h0 : a = 0 := ((hmem 0 _).mp hx).2.1
    have h0' : a' = 0 := ((hmem 0 _).mp hy).2.1
    subst h0; subst h0'
    cases e; rfl
  · obtain ⟨⟨a, b, c, d⟩, P⟩ := x
    constructor
    · intro hx
      obtain ⟨⟨_, hb, hc, hd⟩, ha, hQ⟩ := (hmem t _).mp hx
      refine List.mem_map.mpr ⟨((0, b, c, d), P), (hmem 0 _).mpr ⟨⟨show 0 < N by omega, hb, hc, hd⟩, rfl, hQ⟩, ?_⟩
      show (((0 + t) % N, b, c, d), P) = _
      rw [Nat.zero_add, Nat.mod_eq_of_lt ht]
      exact ha ▸ rfl
    · intro hx
      obtain ⟨⟨⟨a', b', c', d'⟩, P'⟩, hy, e⟩ := List.mem_map.mp hx
      obtain ⟨⟨_, hb, hc, hd⟩, ha, hQ⟩ := (hmem 0 _).mp hy
      have ha' : a' = 0 := ha
      subst ha'
      cases e
      refine (hmem t _).mpr ⟨⟨Nat.mod_lt _ (by omega), hb, hc, hd⟩, ?_, hQ⟩
      show (0 + t) % N = t
      rw [Nat.zero_add, Nat.mod_eq_of_lt ht]

theorem ps_perm (N t : Nat) (ht : t < N) : (slicePS N t).Perm ((slicePS N 0).map (shv N t)) :=
  perm_shift N t ht (slicePS N) (fun P => decide ((dirsOf P).1 = .x0) = false)
    (fun s x => mem_slicePS N s x) (fun _ => (torusPlaquettes_nodup N).filter _)

theorem pt_perm (N t : Nat) (ht : t < N) : (slicePT N t).Perm ((slicePT N 0).map (shv N t)) :=
  perm_shift N t ht (slicePT N) (fun P => decide ((dirsOf P).1 = .x0) = true)
    (fun s x => mem_slicePT N s x) (fun _ => (torusPlaquettes_nodup N).filter _)

theorem mem_sliceV' (N s : Nat) (x : Z4Link) : x ∈ sliceV N s ↔ InBox N x.1 ∧ x.1.1 = s ∧ x.2 = .x0 := by
  rw [mem_sliceV]
  obtain ⟨⟨a, b, c, e⟩, d⟩ := x
  cases d with
  | x0 => exact ⟨fun ⟨h, h'⟩ => ⟨h, (Prod.mk.inj h').1, rfl⟩, fun ⟨h, h', _⟩ => ⟨h, h' ▸ rfl⟩⟩
  | x1 => exact ⟨fun ⟨_, h'⟩ => absurd (Prod.mk.inj h').2 Bool.false_ne_true, fun ⟨_, _, h⟩ => Dir4.noConfusion h⟩
  | x2 => exact ⟨fun ⟨_, h'⟩ => absurd (Prod.mk.inj h').2 Bool.false_ne_true, fun ⟨_, _, h⟩ => Dir4.noConfusion h⟩
  | x3 => exact ⟨fun ⟨_, h'⟩ => absurd (Prod.mk.inj h').2 Bool.false_ne_true, fun ⟨_, _, h⟩ => Dir4.noConfusion h⟩

theorem v_perm (N t : Nat) (ht : t < N) : (sliceV N t).Perm ((sliceV N 0).map (shv N t)) :=
  perm_shift N t ht (sliceV N) (fun d => d = .x0) (mem_sliceV' N) (fun _ => (torusLinks_nodup N).filter _)

/-! ## The weight with variables placed by an index map -/

variable (N : Nat) (β : Q') (K : Nat)

def wordI (ι : Z4Link → Nat) (p : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul (PolyQuaternion.coordinateVariable (ι (p.1, (dirsOf p.2).1)))
      (PolyQuaternion.coordinateVariable (ι (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2))))
    (PolyQuaternion.mul
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (ι (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1))))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (ι (p.1, (dirsOf p.2).2)))))

/-- The Wilson weight `T_K(p)` with variables placed by `ι`. -/
def TKi (ι : Z4Link → Nat) (p : Z4Plaq) : RatPoly :=
  YMGap.Continuum.SU2WilsonCharacterPower.wilsonPoly (wordI N ι p).scalar
    (YMGap.Continuum.SU2WilsonActivity.wilsonA β) K

theorem tk_eq (links : List Z4Link) (p : Z4Plaq) :
    YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K p = TKi N β K (fun ℓ => links.idxOf ℓ) p := rfl

/-- **Translated plaquette weight (PROVED).**  `T_K(τ_t p) = T_K^{ι∘τ_t}(p)`. -/
theorem tk_shift (links : List Z4Link) (t : Nat) (p : Z4Plaq) :
    YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K (shv N t p) =
      TKi N β K (fun ℓ => links.idxOf (shv N t ℓ)) p := by
  rw [tk_eq]
  obtain ⟨v, P⟩ := p
  show YMGap.Continuum.SU2WilsonCharacterPower.wilsonPoly (wordI N _ (vs N t v, P)).scalar _ K = _
  unfold wordI
  rw [tAdd_vs, tAdd_vs]
  rfl

end YMGap.Continuum.SU2TimeShift
