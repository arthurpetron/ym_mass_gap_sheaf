/-
# Torus RP (g6): the RP reflection conjugates the time shift to its inverse (geometry)

The RP reflection `reflLink M` (time plane between sites 0 and 1, plus `M + ½`) satisfies, on the box,
`reflLink (shv x ℓ) = shv (2M − x % 2M) (reflLink ℓ)` (`refl_shift`). This is the link-level form of
`Θ∘τ_x = τ_{−x}∘Θ`. **OPEN**: the polynomial-level `Θ∘τ_x ≡ τ_{−x}∘Θ`, via `like_img`, `tau_lv` and `qconj_sub`,
and the correlator identity.
-/

import YMGap.Continuum.SU2TorusShiftPerm
import YMGap.Continuum.SU2TorusRPGeom

namespace YMGap.Continuum.SU2TorusReflShift

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TimeShift (vs shv tAdd_vs)
open YMGap.Continuum.SU2TorusShiftPerm (shift_eq m2)

theorem rt_shift (M x a : Nat) (hM : 1 ≤ M) (ha : a < 2 * M) :
    YMGap.Continuum.SU2TorusRPGeom.rt M ((a + x) % (2 * M)) =
      (YMGap.Continuum.SU2TorusRPGeom.rt M a + (2 * M - x % (2 * M))) % (2 * M) := by
  have hN : 0 < 2 * M := by omega
  have hr := Nat.mod_lt x hN
  have hb : YMGap.Continuum.SU2TorusRPGeom.rt M a < 2 * M := by
    unfold YMGap.Continuum.SU2TorusRPGeom.rt
    split
    · omega
    · split <;> omega
  rw [shift_eq _ x a hN ha, shift_eq _ (2 * M - x % (2 * M)) _ hN hb, m2 (2 * M - x % (2 * M)) (2 * M) (by omega)]
  generalize x % (2 * M) = r at *
  unfold YMGap.Continuum.SU2TorusRPGeom.rt at hb ⊢
  repeat' split
  all_goals omega

theorem rv_shift (M x : Nat) (hM : 1 ≤ M) (v : Z4Vertex) (hv : InBox (2 * M) v) :
    YMGap.Continuum.SU2TorusRPGeom.rv M (vs (2 * M) x v) =
      vs (2 * M) (2 * M - x % (2 * M)) (YMGap.Continuum.SU2TorusRPGeom.rv M v) := by
  obtain ⟨a, b, c, d⟩ := v
  show (YMGap.Continuum.SU2TorusRPGeom.rt M ((a + x) % (2 * M)), b, c, d) = _
  rw [rt_shift M x a hM hv.1]; rfl

/-- **Link-level `Θ∘τ_x = τ_{−x}∘Θ`.** -/
theorem refl_shift (M x : Nat) (hM : 1 ≤ M) (ℓ : Z4Link) (hℓ : InBox (2 * M) ℓ.1) :
    YMGap.Continuum.SU2TorusRPGeom.reflLink M (shv (2 * M) x ℓ) =
      shv (2 * M) (2 * M - x % (2 * M)) (YMGap.Continuum.SU2TorusRPGeom.reflLink M ℓ) := by
  obtain ⟨v, d⟩ := ℓ
  have hN : 0 < 2 * M := by omega
  cases d with
  | x0 =>
    show (YMGap.Continuum.SU2TorusRPGeom.rv M (tAdd (2 * M) (vs (2 * M) x v) .x0), Dir4.x0) = _
    rw [tAdd_vs, rv_shift M x hM _ (tAdd_inBox hN hℓ _)]; rfl
  | x1 => show (YMGap.Continuum.SU2TorusRPGeom.rv M (vs (2 * M) x v), Dir4.x1) = _; rw [rv_shift M x hM v hℓ]; rfl
  | x2 => show (YMGap.Continuum.SU2TorusRPGeom.rv M (vs (2 * M) x v), Dir4.x2) = _; rw [rv_shift M x hM v hℓ]; rfl
  | x3 => show (YMGap.Continuum.SU2TorusRPGeom.rv M (vs (2 * M) x v), Dir4.x3) = _; rw [rv_shift M x hM v hℓ]; rfl

end YMGap.Continuum.SU2TorusReflShift

#print axioms YMGap.Continuum.SU2TorusReflShift.rt_shift
#print axioms YMGap.Continuum.SU2TorusReflShift.refl_shift
