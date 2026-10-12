/-
# Expression anchor trajectories: the anchor/path/window layer for ANY slab expression

Companion to `audits/AUDIT-EXPR-ANCHOR-TRAJECTORY-2026-10-06.md`. ADDITIVE: no existing
definition or theorem is changed. `Y_j` (`DyadicSmoothedTrajectory`) is untouched.
`BF4WilsonAllNomeExprAnchorRegression` shows that it is an instance.

The current anchor layer is typed through the plaquette family `familyState`. The
consumers use only:
* the centered completed vector `x = centeredExcitation ψ` of an
  `IntrinsicExpression ψ`;
* its one-sided box smoothing `Y_M = orbitSum x (timeKernel M)`;
* the moment pins `B(x, T^n x) = centeredTimeMoment n ψ ψ`.
Here all of these are stated for an arbitrary `ψ`.

`ExprAnchorTrajectory`: per scale `j`, a schedule nome `w_j`, a carrier width
`width j` (a free function of `j`), a smoothing radius `M_j`, and a slab
expression `ψ_j : IntrinsicExpression (width j)`.
* The anchor block is the dyadic `side j = 2^j` with spacing `2^-j`, exactly as for
  `Y_j`.
* Keeping `width` generic is the structure that a fixed-physical-volume carrier
  (FV1, held) would need.

The per-scale nondegeneracy inputs are explicit OPEN Props:
* `ExprHVar tr v`: `0 < v_j ≤ B(x_j, x_j)`, a centered-variance floor;
* `ExprHRay tr ρ`: `0 < ρ_j` and `ρ_j B(x_j,x_j) ≤ B(x_j, T x_j)`, a lag-one
  Rayleigh floor.

Proved here:
* `exprResponse_ge_vector_response`: `R_x(2M+n) ≤ R_Y(n)`. The box kernel has lags
  `0..M`, the responses are antitone, and the kernel mass is 1.
* `exprResponse_floor`: `ρ^(2M+n)·v ≤ R_Y(n)`, via `response_geometric_lower`.
* `exprShiftedNondegenerate_of_hvar_hray`: the shifted anchor needs a floor at lag
  `n = side_j` (the norm of `T^(side_j/2) Y_j`). So
  `fl_j = ρ_j^(2M_j + side_j) · v_j`, the same exponent as `paddedNondegFloor`.
* `exprShiftedEpsBound_of_windowSurvival`: backward-window survival gives the
  shifted H1, with `2(1-θ) ≤ θ c0` and `1 ≤ c0`.

OPEN, not proved: `ExprHVar` and `ExprHRay` for any non-plaquette expression
(e.g. an NS-smoothed loop), and window survival. No smearing word is constructed.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival
import YMGap.Continuum.BF4WilsonAllNomeResponseLower

namespace YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredExcitation centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_add VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (orbitSum responseSum orbitSum_time orbitSum_pairing orbitSum_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg timeKernel kernelMass timeKernel_mass)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (boxSum_ge_const response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeResponseLower (response_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (OneStepEpsBound shift_norm_pin shift_response_pin)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (window_epsBound oneStepEpsBound_one)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Local scalar helpers (standard private copies) -/

private theorem ea_pow_pos (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos ha (ea_pow_pos a ha n)

private theorem ea_pow_nonneg (a : Q') (ha : (0 : Q') ≤ a) :
    ∀ n : Nat, (0 : Q') ≤ a^n
  | 0 => by change (0 : Q') ≤ 1; decide
  | n+1 => Q'.mul_nonneg _ _ ha (ea_pow_nonneg a ha n)

private theorem ea_scale_rational (r v : Q') :
    RCscale r (Rq v) = Rq (r*v) :=
  Quotient.sound (CRealAlg.ofQ'_mul r v).symm

private theorem ea_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ea_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ea_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem ea_one_sub_nonneg {theta : Q'} (h1 : theta ≤ 1) : (0 : Q') ≤ 1 + -theta := by
  have h' := Q'.add_le_add_right _ _ (-theta) h1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv theta)) h'

/-- Scalar bookkeeping for the path window `p = S/2`, `n = S - S/2`
(copy of the private `ws_coeff`). -/
private theorem ea_coeff (S n : Nat) (hS : S ≤ 2*(n+1)) (theta c0 : Q') (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) :
    Q'.ofNat S * (1 + -theta) ≤ theta * Q'.ofNat (n+1) * c0 := by
  have hd := ea_one_sub_nonneg h1
  have a1 : Q'.ofNat S * (1 + -theta) ≤ Q'.ofNat (2*(n+1)) * (1 + -theta) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (ea_ofNat_le hS) hd
  have a2 : Q'.ofNat (2*(n+1)) * (1 + -theta) ≈
      Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ea_ofNat_mul 2 (n+1)))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
        (fun | 0 => Q'.ofNat 2 | 1 => Q'.ofNat (n+1) | _ => 1 + -theta))
  have a3 : Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) ≤ Q'.ofNat (n+1) * (theta * c0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hc0 (ea_ofNat_nonneg _)
  have a4 : Q'.ofNat (n+1) * (theta * c0) ≈ theta * Q'.ofNat (n+1) * c0 :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => Q'.ofNat (n+1) | 1 => theta | _ => c0)
  exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv a2)
    (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv a4)))

private theorem ea_traj_halves (j : Nat) (hj : 1 ≤ j) : side j/2+side j/2 = side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

/-! ## 1. Smoothing of an arbitrary centered slab expression -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (ψ : IntrinsicExpression width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (centeredExcitation hw0 hw1 ψ)

/-- One-sided box smoothing `Y_M = Σ_{m ≤ M} (M+1)^(-1) T^m x` of the centered
completed vector `x` of `ψ`. -/
def exprSmoothedVector (M : Nat) : Completion hw0 hw1 width :=
  orbitSum hw0 hw1 (centeredExcitation hw0 hw1 ψ).val (timeKernel M)

/-- The same vector as a state of the vacuum complement. -/
def exprSmoothedState (M : Nat) : VacuumComplement hw0 hw1 (width := width) :=
  ⟨exprSmoothedVector hw0 hw1 width ψ M, orbitSum_orthogonal hw0 hw1 x0
    (centeredExcitation hw0 hw1 ψ).property (timeKernel M)⟩

/-- `R_M(n) = B(Y_M, T^n Y_M)`. -/
def exprResponse (M n : Nat) : RC :=
  B (exprSmoothedVector hw0 hw1 width ψ M) (T n (exprSmoothedVector hw0 hw1 width ψ M))

/-- Double kernel expansion with all signed cross terms. -/
theorem exprResponse_orbit_expand (M n : Nat) :
    exprResponse hw0 hw1 width ψ M n =
      responseSum (timeKernel M) (fun m => responseSum (timeKernel M)
        (fun k => B x0 (T (m+k+n) x0))) := by
  unfold exprResponse exprSmoothedVector
  rw [orbitSum_time hw0 hw1 x0 (timeKernel M) n, orbitSum_pairing]
  apply congrArg (responseSum (timeKernel M))
  funext m
  apply congrArg (responseSum (timeKernel M))
  funext k
  rw [completedTime_add hw0 hw1 (m+k) n x0]

/-- Pin to the centered time moments of `ψ` itself. -/
theorem exprResponse_pin (M n : Nat) :
    exprResponse hw0 hw1 width ψ M n =
      responseSum (timeKernel M) (fun m => responseSum (timeKernel M)
        (fun k => Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 (m+k+n) ψ ψ))) := by
  rw [exprResponse_orbit_expand]
  apply congrArg (responseSum (timeKernel M))
  funext m
  apply congrArg (responseSum (timeKernel M))
  funext k
  exact centeredVector_time_pairing hw0 hw1 (m+k+n) ψ

/-- `R_x(2M+n) ≤ R_Y(n)`: lags `0..M` (one-sided), antitone responses, unit mass. -/
theorem exprResponse_ge_vector_response (M n : Nat) :
    RCle (B x0 (T (2*M+n) x0)) (exprResponse hw0 hw1 width ψ M n) := by
  have hr := smoothingWeight_nonneg M
  rw [exprResponse_orbit_expand hw0 hw1 width ψ M n]
  have hinner : ∀ m, m ≤ M →
      RCle (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+n) x0)))
        (responseSum (timeKernel M) (fun k => B x0 (T (m+k+n) x0))) := fun m hm =>
    boxSum_ge_const hr (fun k => B x0 (T (m+k+n) x0)) _ M
      (fun k hk => response_le_of_le hw0 hw1 width x0 (by omega : m+k+n ≤ 2*M+n))
  have houter : RCle (RCscale (kernelMass (timeKernel M))
        (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+n) x0))))
      (responseSum (timeKernel M)
        (fun m => responseSum (timeKernel M) (fun k => B x0 (T (m+k+n) x0)))) :=
    boxSum_ge_const hr _ _ M hinner
  have hm := timeKernel_mass M
  have hmm : kernelMass (timeKernel M) * kernelMass (timeKernel M) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.one_mul_eqv 1))
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hmm, RCscale_one] at houter
  exact houter

/-- **Floor from H-var + H-ray (fixed scale).** With `v ≤ B(x,x)` and
`ρ B(x,x) ≤ B(x,Tx)` (`0 ≤ ρ`): `ρ^(2M+n) · v ≤ R_Y(n)`. -/
theorem exprResponse_floor (M n : Nat) (v rho : Q') (hrho : (0 : Q') ≤ rho)
    (hv : RCle (Rq v) (B x0 x0))
    (hray : RCle (RCscale rho (B x0 x0)) (B x0 (T 1 x0))) :
    RCle (Rq (rho^(2*M+n) * v)) (exprResponse hw0 hw1 width ψ M n) := by
  have h1 := RCscale_mono (ea_pow_nonneg rho hrho (2*M+n)) hv
  rw [ea_scale_rational] at h1
  have h2 := response_geometric_lower hw0 hw1 x0 rho hrho hray (2*M+n)
  exact RCle_trans h1 (RCle_trans h2 (exprResponse_ge_vector_response hw0 hw1 width ψ M n))

end Generic

/-! ## 2. Expression anchor trajectories -/

/-- Per scale `j`: nome schedule, carrier width `width j` (free; the structure FV1
would need), smoothing radius `M_j`, and a slab expression `ψ_j`. The anchor block
is the dyadic `side j`. -/
structure ExprAnchorTrajectory : Type where
  schedule : NomeSchedule
  width : Nat → Nat
  radius : Nat → Nat
  expr : (j : Nat) → IntrinsicExpression (width j)

namespace ExprAnchorTrajectory

variable (tr : ExprAnchorTrajectory)

/-- Centered unsmoothed vector `x_j`. -/
def vector (j : Nat) :
    Completion (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j) :=
  Subtype.val (centeredExcitation (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.expr j))

/-- Smoothed anchor state `Y_j = Y_{M_j}(ψ_j)`. -/
def state (j : Nat) :
    Completion (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j) :=
  exprSmoothedVector (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.expr j) (tr.radius j)

/-- `R_j(n) = B(Y_j, T^n Y_j)`. -/
def response (j n : Nat) : RC :=
  exprResponse (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.expr j) (tr.radius j) n

end ExprAnchorTrajectory

open ExprAnchorTrajectory

/-- **H-var (OPEN).** Centered-variance floor `0 < v_j ≤ B(x_j, x_j)`. -/
def ExprHVar (tr : ExprAnchorTrajectory) (v : Nat → Q') : Prop :=
  ∀ j, (0 : Q') < v j ∧
    RCle (Rq (v j)) (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.vector j) (tr.vector j))

/-- **H-ray (OPEN).** Lag-one Rayleigh floor `ρ_j B(x_j,x_j) ≤ B(x_j, T x_j)`, `0 < ρ_j`. -/
def ExprHRay (tr : ExprAnchorTrajectory) (rho : Nat → Q') : Prop :=
  ∀ j, (0 : Q') < rho j ∧
    RCle (RCscale (rho j) (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (tr.vector j) (tr.vector j)))
      (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.vector j)
        (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) 1 (tr.vector j)))

/-- Qualitative shifted nondegeneracy `fl_j ≤ R_j(side_j)`. -/
def ExprShiftedNondegenerate (tr : ExprAnchorTrajectory) (fl : Nat → Q') : Prop :=
  ∀ j, RCle (Rq (fl j)) (tr.response j (side j))

/-- Shifted H1 on `T^(side_j/2) Y_j` (OPEN). -/
def ExprShiftedEpsBound (tr : ExprAnchorTrajectory) (c0 : Q') : Prop :=
  ∀ j, OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
      (tr.state j)) (side j) c0

/-- Backward-window survival `θ R_j(side_j/2) ≤ R_j(side_j + 1)`, `j ≥ 1` (OPEN). -/
def ExprShiftedWindowSurvival (tr : ExprAnchorTrajectory) (theta : Q') : Prop :=
  ∀ j, 1 ≤ j → RCle (RCscale theta (tr.response j (side j / 2))) (tr.response j (side j + 1))

/-- The floor `fl_j = ρ_j^(2M_j + side_j) · v_j`. -/
def exprNondegFloor (tr : ExprAnchorTrajectory) (v rho : Nat → Q') (j : Nat) : Q' :=
  rho j ^ (2 * tr.radius j + side j) * v j

theorem exprNondegFloor_pos (tr : ExprAnchorTrajectory) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) : ∀ j, (0 : Q') < exprNondegFloor tr v rho j :=
  fun j => Q'.mul_pos (ea_pow_pos _ (Hr j).1 _) (Hv j).1

/-- **Nondegeneracy from H-var + H-ray.** -/
theorem exprShiftedNondegenerate_of_hvar_hray (tr : ExprAnchorTrajectory) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) :
    ExprShiftedNondegenerate tr (exprNondegFloor tr v rho) := fun j =>
  exprResponse_floor (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.expr j) (tr.radius j) (side j) (v j) (rho j) (Q'.le_of_lt (Hr j).1) (Hv j).2 (Hr j).2

/-- Response form of the shifted H1 at `j ≥ 1`. -/
theorem exprShiftedEpsBound_iff_response (tr : ExprAnchorTrajectory) (c0 : Q')
    (j : Nat) (hj : 1 ≤ j) :
    OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
        (tr.state j)) (side j) c0 ↔
    RCle (RCscale (Q'.ofNat (side j)) (RCsub (tr.response j (side j))
        (tr.response j (side j + 1))))
      (RCscale c0 (tr.response j (side j))) := by
  have hh := ea_traj_halves j hj
  unfold OneStepEpsBound
  rw [shift_norm_pin (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.state j) (side j / 2),
    shift_response_pin (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.state j) (side j / 2) 1,
    show 2*(side j/2) = side j by omega, show 1 + side j = side j + 1 by omega]
  exact Iff.rfl

/-- **Window ⟹ shifted H1.** `0 < θ ≤ 1`, `2(1-θ) ≤ θ c0`, `1 ≤ c0`. -/
theorem exprShiftedEpsBound_of_windowSurvival (tr : ExprAnchorTrajectory) (c0 theta : Q')
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (Hw : ExprShiftedWindowSurvival tr theta) : ExprShiftedEpsBound tr c0 := by
  intro j
  match j with
  | 0 =>
      exact oneStepEpsBound_one (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0)
        (tr.width 0) _ c0 hc1
  | j+1 =>
      have hj : 1 ≤ j+1 := Nat.succ_pos j
      rw [exprShiftedEpsBound_iff_response tr c0 (j+1) hj]
      have hpn : side (j+1) / 2 + (side (j+1) - side (j+1) / 2) = side (j+1) := by omega
      have hS : side (j+1) ≤ 2 * ((side (j+1) - side (j+1) / 2) + 1) := by omega
      exact window_epsBound (tr.schedule.nome_pos (j+1)) (tr.schedule.nome_lt_one (j+1))
        (tr.width (j+1)) (tr.state (j+1)) (side (j+1) / 2) (side (j+1) - side (j+1) / 2)
        (side (j+1)) (side (j+1)) hpn theta c0 h0 h1
        (ea_coeff (side (j+1)) (side (j+1) - side (j+1) / 2) hS theta c0 h1 hc0)
        (Hw (j+1) hj)

#print axioms exprSmoothedVector
#print axioms exprSmoothedState
#print axioms exprResponse_orbit_expand
#print axioms exprResponse_pin
#print axioms exprResponse_ge_vector_response
#print axioms exprResponse_floor
#print axioms ExprAnchorTrajectory
#print axioms ExprHVar
#print axioms ExprHRay
#print axioms exprNondegFloor_pos
#print axioms exprShiftedNondegenerate_of_hvar_hray
#print axioms exprShiftedEpsBound_iff_response
#print axioms exprShiftedEpsBound_of_windowSurvival

end YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
