/-
# Transfer matrix (1): time-slice geometry of the torus, compatible with `SU2TorusRPGeom`

ADDITIVE.  **Labels:** geometry only, valid for every coupling; also true for U(1), not gap evidence.
Realizer's `SU2TorusRPGeom` is imported, not edited or duplicated.

Time is coordinate `x0`.  The slice variables at time t are:
* `U_t`, the spatial links `(v, d)` with `d ≠ x0` and `v.1 = t`;
* `V_t`, the temporal links `(v, x0)` with `v.1 = t`.
`linkSlice ℓ = (t, isTemporal)`.

* `plaq_slice_spatial`: a spatial plaquette at time t has all four links in `U_t`.
* `plaq_slice_time`: a timelike plaquette `(v, (x0,d))` at time t has exactly the links
  `(v,x0) ∈ V_t`, `(v+e0, d) ∈ U_{t+1}`, `(v+e_d, x0) ∈ V_t`, `(v,d) ∈ U_t`.
  So the torus weight factorises as `Π_t A(U_t) · B(U_t, V_t, U_{t+1})`.
* `mem_sliceU/V`, `mem_slicePS/PT`: membership in the filtered slice lists.
* `slice_cover_link/plaq`: every torus link and plaquette lies in exactly one slice class.
* `refl_slice_spatial` / `refl_slice_temporal`: the RP reflection `reflLink` of `SU2TorusRPGeom`
  maps `U_t` to `U_{rt t}` and `V_t` to `V_{rt(t+1)}`.  This is the slice-level form of Θ
  that the transfer and RP statements share.
-/

import YMGap.Continuum.SU2TorusRPGeom

namespace YMGap.Continuum.SU2TorusSlice

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (rt reflLink rv)

/-- `(time, isTemporal)`. -/
def linkSlice : Z4Link → Nat × Bool
  | (v, .x0) => (v.1, true)
  | (v, _) => (v.1, false)

def isTimelike (p : Z4Plaq) : Bool := decide ((dirsOf p.2).1 = .x0)

theorem plaq_slice_spatial (N : Nat) (p : Z4Plaq) (hs : isTimelike p = false) :
    ∀ ℓ ∈ plaqLinks N p, linkSlice ℓ = (p.1.1, false) := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  cases P <;> simp [isTimelike, dirsOf] at hs <;>
    simp [plaqLinks, dirsOf, tAdd, linkSlice]

theorem plaq_slice_time (N : Nat) (v : Z4Vertex) (P : Z4Plane) (ht : isTimelike (v, P) = true) :
    (dirsOf P).1 = .x0 ∧ (dirsOf P).2 ≠ .x0 ∧
    plaqLinks N (v, P) = [(v, .x0), (tAdd N v .x0, (dirsOf P).2), (tAdd N v (dirsOf P).2, .x0),
      (v, (dirsOf P).2)] ∧
    linkSlice (v, .x0) = (v.1, true) ∧
    linkSlice (tAdd N v .x0, (dirsOf P).2) = (wrapSucc N v.1, false) ∧
    linkSlice (tAdd N v (dirsOf P).2, .x0) = (v.1, true) ∧
    linkSlice (v, (dirsOf P).2) = (v.1, false) := by
  obtain ⟨a, b, c, d⟩ := v
  cases P <;> simp [isTimelike, dirsOf] at ht <;>
    simp [plaqLinks, dirsOf, tAdd, linkSlice]

/-! ## Slice lists -/

def sliceU (N t : Nat) : List Z4Link := (torusLinks N).filter fun ℓ => linkSlice ℓ == (t, false)
def sliceV (N t : Nat) : List Z4Link := (torusLinks N).filter fun ℓ => linkSlice ℓ == (t, true)
/-- Spatial plaquettes of slice t (weight `A(U_t)`). -/
def slicePS (N t : Nat) : List Z4Plaq :=
  (torusPlaquettes N).filter fun p => p.1.1 == t && !isTimelike p
/-- Timelike plaquettes between t and t+1 (weight `B(U_t, V_t, U_{t+1})`). -/
def slicePT (N t : Nat) : List Z4Plaq :=
  (torusPlaquettes N).filter fun p => p.1.1 == t && isTimelike p

theorem mem_sliceU (N t : Nat) (ℓ : Z4Link) :
    ℓ ∈ sliceU N t ↔ InBox N ℓ.1 ∧ linkSlice ℓ = (t, false) := by
  obtain ⟨v, d⟩ := ℓ
  simp [sliceU, mem_torusLinks]

theorem mem_sliceV (N t : Nat) (ℓ : Z4Link) :
    ℓ ∈ sliceV N t ↔ InBox N ℓ.1 ∧ linkSlice ℓ = (t, true) := by
  obtain ⟨v, d⟩ := ℓ
  simp [sliceV, mem_torusLinks]

theorem mem_slicePS (N t : Nat) (p : Z4Plaq) :
    p ∈ slicePS N t ↔ InBox N p.1 ∧ p.1.1 = t ∧ isTimelike p = false := by
  obtain ⟨v, P⟩ := p
  simp [slicePS, mem_torusPlaquettes]

theorem mem_slicePT (N t : Nat) (p : Z4Plaq) :
    p ∈ slicePT N t ↔ InBox N p.1 ∧ p.1.1 = t ∧ isTimelike p = true := by
  obtain ⟨v, P⟩ := p
  simp [slicePT, mem_torusPlaquettes]

theorem linkSlice_fst (ℓ : Z4Link) : (linkSlice ℓ).1 = ℓ.1.1 := by
  obtain ⟨v, d⟩ := ℓ; cases d <;> rfl

/-- Every torus link is in exactly one slice class (its own time, temporal or not). -/
theorem slice_cover_link (N : Nat) (ℓ : Z4Link) (h : InBox N ℓ.1) :
    (ℓ ∈ sliceU N ℓ.1.1 ∨ ℓ ∈ sliceV N ℓ.1.1) ∧
    ∀ t b, linkSlice ℓ = (t, b) → t = ℓ.1.1 := by
  refine ⟨?_, fun t b e => by rw [← linkSlice_fst ℓ, e]⟩
  rw [mem_sliceU, mem_sliceV]
  obtain ⟨v, d⟩ := ℓ
  cases d <;> simp [linkSlice, h]

theorem slice_cover_plaq (N : Nat) (p : Z4Plaq) (h : InBox N p.1) :
    (p ∈ slicePS N p.1.1 ∨ p ∈ slicePT N p.1.1) ∧ ¬ (p ∈ slicePS N p.1.1 ∧ p ∈ slicePT N p.1.1) := by
  rw [mem_slicePS, mem_slicePT]
  cases hp : isTimelike p <;> simp [h]

/-! ## Compatibility with the RP reflection -/

theorem refl_slice_spatial (M : Nat) (v : Z4Vertex) (d : Dir4) (hd : d ≠ .x0) :
    linkSlice (reflLink M (v, d)) = (rt M v.1, false) := by
  obtain ⟨a, b, c, e⟩ := v
  cases d <;> first | exact absurd rfl hd | rfl

theorem refl_slice_temporal (M : Nat) (v : Z4Vertex) :
    linkSlice (reflLink M (v, .x0)) = (rt M (wrapSucc (2 * M) v.1), true) := by
  obtain ⟨a, b, c, e⟩ := v
  rfl

end YMGap.Continuum.SU2TorusSlice
