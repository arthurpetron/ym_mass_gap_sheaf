/-
# Torus RP (d8b): the block selector on the layout and half-swap admissibility

`layT links b`: temporal-ness of the link at block `b` for `b < |links|`, `true` on fresh blocks.
* `refl_dir`: `Θ` preserves the direction.
* `lay_HD`: every `ℓ ∈ P` is half-swap admissible (`HD`) on the layout `P ++ C ++ P.map Θ` with `a = |P| + |C|`.
* `layT_fresh`: blocks `≥ |links|` are selected (the fresh split partners).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayout

namespace YMGap.Continuum.SU2TorusRPLayoutT

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0 getD_idxOf)
open YMGap.Continuum.SU2TorusRPHalfSwap (HD)

def layT (links : List Z4Link) (b : Nat) : Bool :=
  if b < links.length then isT (links.getD b d0).2 else true

theorem refl_dir (M : Nat) (ℓ : Z4Link) : (reflLink M ℓ).2 = ℓ.2 := by
  obtain ⟨v, d⟩ := ℓ; cases d <;> rfl

theorem layT_fresh (links : List Z4Link) (b : Nat) (hb : links.length ≤ b) : layT links b = true := by
  unfold layT; rw [if_neg (by omega)]

theorem layT_link (links : List Z4Link) (ℓ : Z4Link) (h : ℓ ∈ links) : layT links (links.idxOf ℓ) = isT ℓ.2 := by
  unfold layT; rw [if_pos (YMGap.Continuum.SU2TorusRPLayout.idxOf_lt ℓ links h), getD_idxOf h]

theorem lay_HD (M : Nat) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
    (ℓ : Z4Link) (hℓ : ℓ ∈ P) (hinj : ∀ x ∈ P, reflLink M x = reflLink M ℓ → x = ℓ) :
    HD (P.length + C.length) (layT (P ++ C ++ P.map (reflLink M))) (P ++ C ++ P.map (reflLink M)) M ℓ := by
  obtain ⟨h1, h2⟩ := YMGap.Continuum.SU2TorusRPLayout.lay_pos P C (reflLink M) hnd ℓ hℓ hinj
  refine ⟨h1, h2, ?_⟩
  rw [← h2, layT_link _ _ (List.mem_append_right _ (List.mem_map_of_mem hℓ)), refl_dir]

end YMGap.Continuum.SU2TorusRPLayoutT

#print axioms YMGap.Continuum.SU2TorusRPLayoutT.lay_HD
#print axioms YMGap.Continuum.SU2TorusRPLayoutT.layT_fresh
