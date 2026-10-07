/-
# R1 commit 20: ratio form of the truncated χ₁ correlator decay at w₀

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.

* `ratio_of` (pure algebra): if Z > 0 and `|Zpq·Z − Zp·Zq| ≤ B·Z²`, then
  `|Zpq/Z − (Zp/Z)(Zq/Z)| ≤ B`, where `/Z` means `· recip Z`.
* `trunc_ratio`: `|⟨χ_pχ_q⟩ − ⟨χ_p⟩⟨χ_q⟩| ≤ C·λ^d` at w₀, uniform in N, M and P.  Here
  `⟨χ_p⟩ = Zp/Z = ⟨1+χ_p⟩ − 1`, and for p ≠ q `⟨χ_pχ_q⟩ = Zpq/Z`.  By `SU2ObsRoot.ZObs_factor`,
  `ZObs S / Z` is the heat-kernel Gibbs expectation of `Π_{r∈S}(1+χ_r)`.
-/

import YMGap.Continuum.SU2TruncDecay

namespace YMGap.Continuum.SU2TruncRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.SU2PolymerIdentity (gas)
open YMGap.Continuum.SU2HaarL1Activity (w0)
open YMGap.Continuum.SU2ObsInsertion
open YMGap.Continuum.SU2TruncDecay (Ctr trunc_decay)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-- **Ratio form (PROVED, pure algebra).** -/
theorem ratio_of {Z Zpq Zp Zq B : Q'} (hZ : (0 : Q') < Z) (h : Q'.abs (Zpq * Z + -(Zp * Zq)) ≤ B * (Z * Z)) :
    Q'.abs (Zpq * Q'.recip Z + -((Zp * Q'.recip Z) * (Zq * Q'.recip Z))) ≤ B := by
  let ρ := Q'.recip Z
  have hzr : (Z * ρ).eqv 1 := Q'.mul_recip_eqv Z hZ
  have hρ2 : (0 : Q') ≤ ρ * ρ := Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recip_pos _)) (Q'.le_of_lt (Q'.recip_pos _))
  have r1 : ((Zpq * Z + -(Zp * Zq)) * (ρ * ρ)).eqv (Zpq * (Z * ρ) * ρ + -((Zp * ρ) * (Zq * ρ))) := by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq ((V 0 * V 1 + -(V 2 * V 3)) * (V 4 * V 4))
      (V 0 * (V 1 * V 4) * V 4 + -((V 2 * V 4) * (V 3 * V 4))) (by decide)
      (fun | 0 => Zpq | 1 => Z | 2 => Zp | 3 => Zq | _ => ρ)
  have r2 : (Zpq * (Z * ρ) * ρ).eqv (Zpq * ρ) := Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hzr) (Q'.mul_one_eqv _))
  have e : (Zpq * ρ + -((Zp * ρ) * (Zq * ρ))).eqv ((Zpq * Z + -(Zp * Zq)) * (ρ * ρ)) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ r1 (Q'.add_eqv_congr' r2 (Q'.eqv_refl _)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr e)) (Q'.le_trans' _ _ _
    (YMGap.Continuum.PolymerChainDecay.abs_mul_nonneg_le hρ2) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h hρ2) (Q'.le_of_eqv ?_)))
  have r3 : (B * (Z * Z) * (ρ * ρ)).eqv (B * ((Z * ρ) * (Z * ρ))) := by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 1) * (V 2 * V 2)) (V 0 * ((V 1 * V 2) * (V 1 * V 2)))
      (by decide) (fun | 0 => B | 1 => Z | _ => ρ)
  exact Q'.eqv_trans _ _ _ r3 (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hzr) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hzr) (Q'.mul_one_eqv _)))) (Q'.mul_one_eqv _))

variable (M : Nat) (links : List Z4Link) (N : Nat) (P : List Z4Plaq) (hP : P.Nodup)
  (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)

include hP hbox in
/-- **Truncated χ₁ correlator, ratio form (PROVED; heat-kernel at w₀ = 10⁻⁸; uniform in N, M, P).**
`|Zpq/Z − (Zp/Z)(Zq/Z)| ≤ C·λ^{ld(q,p)}`, with C = `Ctr` and λ = 6/7. -/
theorem trunc_ratio (hL : ∀ r ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N r) (p q : Z4Plaq) :
    let Z := ZObs w0 M links N P []
    let Zp := ZObs w0 M links N P [p] + -Z
    let Zq := ZObs w0 M links N P [q] + -Z
    let Zpq := ZObs w0 M links N P [p, q] + -ZObs w0 M links N P [p] + -ZObs w0 M links N P [q] + Z
    Q'.abs (Zpq * Q'.recip Z + -((Zp * Q'.recip Z) * (Zq * Q'.recip Z))) ≤
      Ctr * lam ^ (torusMetric N).ld q p := by
  intro Z Zp Zq Zpq
  have hG : YMGap.Continuum.PolymerChainDecay.Good (gas N P) (gas N P) :=
    ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have hX := (YMGap.Continuum.SU2ObsActivity.env_w0 M links N P hP hbox (gas N P) hG [p]).1
  have hZ : (0 : Q') < Z := YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le hX
    (Q'.ge_of_eqv (ZObs_eq_Xi w0 M links N P [] hL))
  refine ratio_of hZ (Q'.le_trans' _ _ _ (trunc_decay M links N P hP hbox hL p q) (Q'.le_of_eqv ?_))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * (V 1 * (V 2 * V 2))) (V 1 * V 0 * (V 2 * V 2)) (by decide)
    (fun | 0 => lam ^ (torusMetric N).ld q p | 1 => Ctr | _ => Z)

end YMGap.Continuum.SU2TruncRatio
