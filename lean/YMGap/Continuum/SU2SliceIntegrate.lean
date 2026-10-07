/-
# Transfer matrix (2d): integrate each slice's private blocks inside its own factor

ADDITIVE.  **Labels:** algebra only, valid for every coupling and every factor (Wilson T_K in
particular); also true for U(1), not gap evidence.

The torus integrand in slice order is `Π_t W_t`, where `W_t` depends on `U_t`, `V_t` and `U_{t+1}`.
The blocks of `V_t` occur only in `W_t`.  So the Haar integral may integrate the `V_t` blocks
inside `W_t` (in place, no renumbering), and the kernel is `T_t = ∫dV_t W_t`:

* `slice_integrate`: if `Good blocks Ws` holds, then
  `H(Π_t W_t) ≈ H(Π_t integrateQuaternionBlocks S_t W_t)`.

`Good` says that the schedule `S_t` is in range, and that every other factor is block-local away
from `S_t`.  No support beyond that is assumed.  This is the "partial Haar integral over V" step of
`Z = Tr T^{N_t}`, in in-place form (commit 28 gives the trailing-block form).
-/

import YMGap.Continuum.SU2CharacterHaarBound

namespace YMGap.Continuum.SU2SliceIntegrate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (integrateQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

/-- Product of the factors. -/
def kprod : List (RatPoly × List Nat) → RatPoly
  | [] => polyOne
  | w :: ws => polyMul w.1 (kprod ws)

/-- Each factor with its own private blocks integrated out. -/
def kint (ws : List (RatPoly × List Nat)) : List (RatPoly × List Nat) :=
  ws.map fun w => (integrateQuaternionBlocks w.2 w.1, w.2)

def allS (ws : List (RatPoly × List Nat)) : List Nat := ws.flatMap (·.2)

/-- Private-block hypotheses. -/
def Good (blocks : Nat) : List (RatPoly × List Nat) → Prop
  | [] => True
  | w :: ws => (∀ b ∈ w.2, b < blocks) ∧ BlockLocal blocks (· ∉ allS ws) w.1 ∧
      (∀ v ∈ ws, BlockLocal blocks (· ∉ w.2) v.1) ∧ Good blocks ws

theorem local_weaken {blocks : Nat} {a a' : Nat → Prop} {p : RatPoly} (h : ∀ b, a b → a' b)
    (hp : BlockLocal blocks a p) : BlockLocal blocks a' p :=
  fun t ht b hb hn => hp t ht b hb fun ha => hn (h b ha)

theorem kprod_local {blocks : Nat} {a : Nat → Prop} : ∀ ws : List (RatPoly × List Nat),
    (∀ v ∈ ws, BlockLocal blocks a v.1) → BlockLocal blocks a (kprod ws)
  | [], _ => BlockLocal.one _ _
  | w :: ws, h => BlockLocal.mul (h w List.mem_cons_self)
      (kprod_local ws fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem kint_local {blocks : Nat} {a : Nat → Prop} (ws : List (RatPoly × List Nat))
    (h : ∀ v ∈ ws, BlockLocal blocks a v.1) : ∀ v ∈ kint ws, BlockLocal blocks a v.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact local_weaken (fun _ hb => hb.1) (integrateBlocks_local w.2 (h w hw))

/-- Generalised form with a spectator `X`. -/
theorem slice_integrate_spec (blocks : Nat) : ∀ (ws : List (RatPoly × List Nat)) (X : RatPoly),
    Good blocks ws → BlockLocal blocks (· ∉ allS ws) X →
    quaternionHaar blocks (polyMul X (kprod ws)) ≈ quaternionHaar blocks (polyMul X (kprod (kint ws)))
  | [], _, _, _ => Q'.eqv_refl _
  | w :: ws, X, ⟨hr, hW, hO, hG⟩, hX => by
    have hXs : BlockLocal blocks (· ∉ allS ws) X :=
      local_weaken (fun b hb hm => hb (List.mem_append.mpr (Or.inr hm))) hX
    have hXS : BlockLocal blocks (· ∉ w.2) X :=
      local_weaken (fun b hb hm => hb (List.mem_append.mpr (Or.inl hm))) hX
    have ih := slice_integrate_spec blocks ws (polyMul X w.1) hG (BlockLocal.mul hXs hW)
    have hP : BlockLocal blocks (· ∉ w.2) (kprod (kint ws)) := kprod_local _ (kint_local ws hO)
    have hblk := quaternionHaar_polyMul_eq_after_integratingBlocks blocks w.2 (polyMul X (kprod (kint ws)))
      w.1 hr fun b hb => independent_of_local (BlockLocal.mul hXS hP) (hr b hb) (fun h => h hb)
    show quaternionHaar blocks (polyMul X (polyMul w.1 (kprod ws))) ≈
      quaternionHaar blocks (polyMul X (polyMul (integrateQuaternionBlocks w.2 w.1) (kprod (kint ws))))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ ih ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc _ _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm _ _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ hblk ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc _ _ _ _) ?_
    exact quaternionHaar_polyMul_middle_comm _ _ _ _

/-- **Slice integration (PROVED).**  `H(Π_t W_t) ≈ H(Π_t ∫dS_t W_t)`. -/
theorem slice_integrate (blocks : Nat) (ws : List (RatPoly × List Nat)) (h : Good blocks ws) :
    quaternionHaar blocks (kprod ws) ≈ quaternionHaar blocks (kprod (kint ws)) := by
  have hone : BlockLocal blocks (· ∉ allS ws) polyOne := BlockLocal.one _ _
  refine Q'.eqv_trans _ _ _ (SU2CharacterHaarBound.haar_coeff (RatPolyCoeffEqv.one_mul _).symm blocks) ?_
  refine Q'.eqv_trans _ _ _ (slice_integrate_spec blocks ws polyOne h hone) ?_
  exact SU2CharacterHaarBound.haar_coeff (RatPolyCoeffEqv.one_mul _) blocks

end YMGap.Continuum.SU2SliceIntegrate
