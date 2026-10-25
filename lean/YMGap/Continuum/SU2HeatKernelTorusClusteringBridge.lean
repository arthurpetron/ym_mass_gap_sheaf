/-
# Same-action heat-kernel torus clustering bridge (`SU2TruncRatio` ↔ `BF4StrongCouplingClusteringBridge`)

**Labels: U(1)-true. Fixed-coupling heat-kernel action (`coeffW`). Conditional on the explicit
observable-to-semigroup hypothesis `hcov` (`HeatKernelTorusSemigroupBridge`). NOT evidence for a
non-abelian mass gap.**

Companion to `BF4StrongCouplingClusteringBridge`, `WilsonHeatCoeffDominationNoGo`, and
`SU2TruncRatio`. ADDITIVE.

`BF4StrongCouplingClusteringBridge` stated its torus bridge (`TorusChiBridge`) for the Wilson
Taylor-truncated torus (`SU2TorusNormalizedRatio.Ehat` at `β_S`), while
`WilsonHeatCoeffDominationNoGo` showed that the Wilson `T_K` character coefficients are not
dominated by the BF4 heat-kernel weight `coeffW w s = (s+1) w^{s(s+2)}` uniformly in `K`.

This file connects `BF4StrongCouplingClusteringBridge` directly to `SU2TruncRatio`'s
**same-action** heat-kernel torus (`ZObs w0 S_trunc` on `torusLinks (2M)` and
`torusPlaquettes (2M)`, built from the identical `BondMovingStep.coeffW` heat-kernel plaquette
weights):

* `ZHK S_trunc` and `ZHK_pos`: the heat-kernel torus partition function at spin cutoff `S_trunc`
  and polymer nome `w0 = 10⁻⁸` is strictly positive (`0 < ZHK S_trunc`) for every `1 ≤ M` and
  `S_trunc`.
* `covHK S_trunc b c d plane n` and `EhatHK S_trunc b c d plane m := covHK ... (2m)`: the
  normalized χ₁ plaquette covariance at lag `n` (between `pA = mir M p` at time `0` and
  `pB n = shv (2M) n p` at time `1 + n`) and its even-lag subsequence on the heat-kernel torus.
* `covHK_decay` and `ehatHK_polymer_decay`: unconditional heat-kernel torus clustering from
  `SU2TruncRatio.trunc_ratio` and `SU2ClusterBridge.dist_mir_shift`:
  `|covHK n| ≤ Ctr · λ^(n+1)` (`n + 1 ≤ M`) and
  `EhatHK m ≤ (Ctr · λ) · (λ²)^m` (`2m + 1 ≤ M`, `λ = 6/7`), uniform in `M` and `S_trunc`.
* `HeatKernelTorusSemigroupBridge`: isolates the explicit remaining observable-to-semigroup
  hypothesis (`hcov`) comparing `EhatHK m` on the heat-kernel torus to the BF4 heat-kernel
  transfer-semigroup correlator `C · B(y, T^(2m) y)` for a vacuum-orthogonal state `y`.
* `ehatHK_semigroup_decay_of_bridge` and `pilot_ehatHK_semigroup_decay_of_bridge`: conditional
  decay theorem proving `EhatHK m ≤ C · (r²)^m · B(y,y)` (and `r = timeRate = 1/4` at the pilot
  nome) from `hcov`, plus `pilot_ehatHK_two_rate_envelope` combining the unconditional polymer
  bound and the conditional semigroup bound on the same heat-kernel torus observable.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4StrongCouplingClusteringBridge
import YMGap.Continuum.SU2TruncRatio

namespace YMGap.Continuum.SU2HeatKernelTorusClusteringBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq Z4Plane dirsOf)
open YMGap.Continuum.Z4TorusGeometry (torusLinks torusPlaquettes torusPlaquettes_nodup)
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.SU2HaarL1Activity (w0)
open YMGap.Continuum.SU2ObsInsertion (ZObs ZObs_eq_Xi)
open YMGap.Continuum.SU2TruncDecay (Ctr)
open YMGap.Continuum.SU2TruncRatio (trunc_ratio)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusGapCond (pow_two_mul)
open YMGap.Continuum.SU2ClusterBridge (lk_torus dist_mir_shift pA pB)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)
open YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
  (existingNome_allNome_strongCoupling)
open YMGap.Continuum.BF4StrongCouplingClusteringBridge (even_correlator_decay)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Same-action heat-kernel torus partition function and χ₁ covariance -/

section Torus

variable {M : Nat} (hM : 1 ≤ M) (S_trunc b c d : Nat) (plane : Z4Plane)

local notation "Ls" => torusLinks (2 * M)
local notation "Ps" => torusPlaquettes (2 * M)

/-- Heat-kernel torus partition function `ZObs w0 S_trunc` on `(Z / 2M Z)⁴` with
`BondMovingStep.coeffW` plaquette weights truncated at spin `S_trunc`. -/
abbrev ZHK : Q' := ZObs w0 S_trunc Ls (2 * M) Ps []

/-- Heat-kernel torus observable-inserted integral `ZObs w0 S_trunc Ls (2M) Ps S`. -/
abbrev ZObsHK (S : List Z4Plaq) : Q' := ZObs w0 S_trunc Ls (2 * M) Ps S

include hM in
/-- **Positivity of the heat-kernel torus partition function (PROVED, constructive in `Q'`).**
Uniform in the torus half-side `M ≥ 1` and spin truncation `S_trunc`. -/
theorem ZHK_pos : (0 : Q') < ZHK (M := M) S_trunc := by
  have hP := torusPlaquettes_nodup (2 * M)
  have hbox : ∀ p, p ∈ Ps → p ∈ Ps := fun _ h => h
  have hG : YMGap.Continuum.PolymerChainDecay.Good
      (YMGap.Continuum.SU2PolymerIdentity.gas (2 * M) Ps)
      (YMGap.Continuum.SU2PolymerIdentity.gas (2 * M) Ps) :=
    ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup (2 * M) Ps hP, fun _ h => h⟩
  have hX := (YMGap.Continuum.SU2ObsActivity.env_w0 S_trunc Ls (2 * M) Ps hP hbox
    (YMGap.Continuum.SU2PolymerIdentity.gas (2 * M) Ps) hG []).1
  exact YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le hX
    (Q'.ge_of_eqv (ZObs_eq_Xi w0 S_trunc Ls (2 * M) Ps [] (lk_torus hM)))

/-- Normalized χ₁ plaquette covariance on the heat-kernel torus between the mirrored source
`pA = mir M ((1,b,c,d), plane)` at time `0` and the shifted sink
`pB n = shv (2M) n ((1,b,c,d), plane)` at time `1 + n`, in `SU2TruncRatio.trunc_ratio` form. -/
abbrev covHK (n : Nat) : Q' :=
  let Z := ZHK (M := M) S_trunc
  let Zp := ZObsHK (M := M) S_trunc [pA (M := M) b c d plane] + -Z
  let Zq := ZObsHK (M := M) S_trunc [pB (M := M) b c d plane n] + -Z
  let Zpq := ZObsHK (M := M) S_trunc [pA (M := M) b c d plane, pB (M := M) b c d plane n] +
    -ZObsHK (M := M) S_trunc [pA (M := M) b c d plane] +
    -ZObsHK (M := M) S_trunc [pB (M := M) b c d plane n] + Z
  Zpq * Q'.recip Z + -((Zp * Q'.recip Z) * (Zq * Q'.recip Z))

/-- Even-lag normalized χ₁ covariance `EhatHK m = covHK (2m)` on the heat-kernel torus. -/
abbrev EhatHK (m : Nat) : Q' := covHK (M := M) S_trunc b c d plane (2 * m)

/-! ## 2. Unconditional polymer clustering on the heat-kernel torus -/

include hM in
/-- **Heat-kernel torus covariance decay at explicit lag (PROVED).**
For a spatial plaquette (`isT (dirsOf plane).1 = false`) and `n + 1 ≤ M`,
`|covHK n| ≤ Ctr · λ^(n+1)` with `λ = 6/7`, uniform in `M` and spin cutoff `S_trunc`. -/
theorem covHK_decay (hsp : isT (dirsOf plane).1 = false) (n : Nat) (hn : n + 1 ≤ M) :
    Q'.abs (covHK (M := M) S_trunc b c d plane n) ≤ Ctr * lam ^ (n + 1) := by
  have h := trunc_ratio S_trunc Ls (2 * M) Ps (torusPlaquettes_nodup (2 * M))
    (fun _ hp => hp) (lk_torus hM) (pA (M := M) b c d plane) (pB (M := M) b c d plane n)
  rw [dist_mir_shift hM b c d plane hsp n hn] at h
  exact h

include hM in
/-- **Even-lag heat-kernel torus clustering (`Q'` form, PROVED).**
For `2m + 1 ≤ M`, `|EhatHK m| ≤ (Ctr · λ) · (λ²)^m`. -/
theorem ehatHK_abs_decay (hsp : isT (dirsOf plane).1 = false) (m : Nat) (hm : 2 * m + 1 ≤ M) :
    Q'.abs (EhatHK (M := M) S_trunc b c d plane m) ≤ (Ctr * lam) * (lam * lam) ^ m := by
  have hcd := covHK_decay hM S_trunc b c d plane hsp (2 * m) hm
  have hpin : Ctr * lam ^ (2 * m + 1) ≈ (Ctr * lam) * (lam * lam) ^ m :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left Ctr _ _ (Q'.mul_eqv_congr_left lam _ _ (pow_two_mul lam m)))
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => Ctr | 1 => lam | _ => (lam * lam) ^ m))
  exact Q'.le_trans' _ _ _ hcd (Q'.le_of_eqv hpin)

include hM in
/-- **Even-lag heat-kernel torus clustering (`CReal` form, PROVED).**
For `2m + 1 ≤ M`, `Rq (EhatHK m) ≤ Rq ((Ctr · λ) · (λ²)^m)`. -/
theorem ehatHK_polymer_decay (hsp : isT (dirsOf plane).1 = false) (m : Nat) (hm : 2 * m + 1 ≤ M) :
    RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
      (Rq ((Ctr * lam) * (lam * lam) ^ m)) :=
  CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (ehatHK_abs_decay hM S_trunc b c d plane hsp m hm)))

end Torus

/-! ## 3. Same-action observable-to-semigroup hypothesis (`hcov`) and conditional decay -/

section Bridge

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- **Explicit observable-to-semigroup hypothesis (`hcov`, OPEN).**
Isolates the remaining identification between the normalized χ₁ covariance `EhatHK m` on the
heat-kernel torus (`ZObs w0 S_trunc` with `coeffW` plaquette weights) and the BF4 heat-kernel
transfer-semigroup correlator `C · B(y, T^(2m) y)` for a vacuum-orthogonal state `y` in the
physical torus window `2m + 1 ≤ M`. -/
def HeatKernelTorusSemigroupBridge {M : Nat} (S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (C : Q') : Prop :=
  ∀ m : Nat, 2 * m + 1 ≤ M →
    RCle (Rq (EhatHK (M := M) S_trunc b c d plane m)) (RCscale C (B y.val (T (2 * m) y.val)))

/-- **Conditional semigroup decay on the heat-kernel torus (PROVED from `hcov`).**
Under `WilsonVacuumSqContraction hw0 hw1 width r` and the explicit observable-to-semigroup
hypothesis `hcov : HeatKernelTorusSemigroupBridge`, the heat-kernel torus covariance `EhatHK m`
decays with the BF4 semigroup rate `(r²)^m` for every `2m + 1 ≤ M`. -/
theorem ehatHK_semigroup_decay_of_bridge (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r)
    {M : Nat} (S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (C : Q') (hC : (0 : Q') ≤ C)
    (hcov : HeatKernelTorusSemigroupBridge hw0 hw1 width (M := M) S_trunc b c d plane y C)
    (m : Nat) (hm : 2 * m + 1 ≤ M) :
    RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
      (RCscale (C * (r * r) ^ m) (B y.val y.val)) := by
  have h1 := RCscale_mono hC (even_correlator_decay hw0 hw1 width r hr h m y)
  rw [RCscale_RCscale] at h1
  exact RCle_trans (hcov m hm) h1

end Bridge

/-! ## 4. Pilot strong-coupling specialization and combined two-rate envelope -/

/-- **Pilot strong-coupling conditional decay on the heat-kernel torus (`timeRate = 1/4`).**
At `w = existingPilotNome = 1/1024`, for every slab width, torus half-side `M`, and spin cutoff
`S_trunc`, the explicit observable-to-semigroup hypothesis `hcov` implies
`EhatHK m ≤ C · (timeRate²)^m · B(y,y)` (`(1/16)^m` per even step) across `2m + 1 ≤ M`. -/
theorem pilot_ehatHK_semigroup_decay_of_bridge :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      ∀ (width M S_trunc b c d : Nat) (plane : Z4Plane)
        (y : VacuumComplement hw0 hw1 (width := width)) (C : Q'),
        (0 : Q') ≤ C →
        HeatKernelTorusSemigroupBridge hw0 hw1 width (M := M) S_trunc b c d plane y C →
        ∀ m : Nat, 2 * m + 1 ≤ M →
          RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
            (RCscale (C * (timeRate * timeRate) ^ m) (completedInner hw0 hw1 y.val y.val)) := by
  intro w
  obtain ⟨hw0, hw1, hpos, _, hc⟩ := existingNome_allNome_strongCoupling
  have hr : (0 : Q') ≤ timeRate * timeRate :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hpos) (Q'.le_of_lt hpos)
  exact ⟨hw0, hw1, fun width M S_trunc b c d plane y C hC hcov m hm =>
    ehatHK_semigroup_decay_of_bridge hw0 hw1 width timeRate hr (hc width)
      S_trunc b c d plane y C hC hcov m hm⟩

/-- **Combined same-action heat-kernel torus clustering envelope.**
Packages on the SAME heat-kernel torus observable `EhatHK m` (`2m + 1 ≤ M`):
(1) the unconditional polymer clustering bound `(Ctr · λ) · (λ²)^m` (`λ = 6/7`) from
    `SU2TruncRatio.trunc_ratio`, and
(2) the conditional BF4 transfer-semigroup bound `C · (timeRate²)^m · B(y,y)` (`timeRate = 1/4`)
    under the explicit observable-to-semigroup hypothesis `hcov`. -/
theorem pilot_ehatHK_two_rate_envelope :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      ∀ {M : Nat} (width S_trunc b c d : Nat) (plane : Z4Plane),
        1 ≤ M →
        isT (dirsOf plane).1 = false →
        ∀ (y : VacuumComplement hw0 hw1 (width := width)) (C : Q'),
          (0 : Q') ≤ C →
          HeatKernelTorusSemigroupBridge hw0 hw1 width (M := M) S_trunc b c d plane y C →
          (0 : Q') < ZHK (M := M) S_trunc ∧
          ∀ m : Nat, 2 * m + 1 ≤ M →
            RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
              (Rq ((Ctr * lam) * (lam * lam) ^ m)) ∧
            RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
              (RCscale (C * (timeRate * timeRate) ^ m) (completedInner hw0 hw1 y.val y.val)) := by
  intro w
  obtain ⟨hw0, hw1, hpos, _, hc⟩ := existingNome_allNome_strongCoupling
  have hr : (0 : Q') ≤ timeRate * timeRate :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hpos) (Q'.le_of_lt hpos)
  exact ⟨hw0, hw1, fun width S_trunc b c d plane hM hsp y C hC hcov =>
    ⟨ZHK_pos hM S_trunc, fun m hm =>
      ⟨ehatHK_polymer_decay hM S_trunc b c d plane hsp m hm,
        ehatHK_semigroup_decay_of_bridge hw0 hw1 width timeRate hr (hc width)
          S_trunc b c d plane y C hC hcov m hm⟩⟩⟩

end YMGap.Continuum.SU2HeatKernelTorusClusteringBridge
