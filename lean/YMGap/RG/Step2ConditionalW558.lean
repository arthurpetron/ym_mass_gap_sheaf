/-
# Step n = 2 at fine nome 279/500 (instance B): conditional chain hypotheses → fineAtB, widths ≥ 8

Additive DRAFT, W558 instance.  Decision (darthur, Nov 21; `steps25_H2rest_status.md`,
Option A): step 2 moves from 14/25 to w = 279/500 = 0.558.  This file mirrors
`Step2Conditional` over schedule B (`Robust3UndershootAfScheduleW558`, `fineAtB`) and proves
ONE real implication: Chain I with the addendum-G split of (H2), with `H2_rest` now capped at
attached activity `t ≤ tCap = 47/250`, plus explicitly named non-sphere / spin ≥ 1 / KP→fineAtB
bridge hypotheses ⇒ `hfine_step2B_ge8_OPEN`.  `Step2Conditional` (14/25) is kept and untouched
apart from its safe-side rounding fix.

Honesty notes.
* The polymer quantities (σ₁, σ_K, Lemma-Z sums, KP sums, host-charged exponents) are NOT
  formalised.  They enter as the uninterpreted relations of `Step2Conditional.SphereGasModel`,
  here read at the step-2 nome 279/500; every hypothesis is a statement about those relations.
  The proved content is the exact-rational certificate chain (KP supersolution at 279/500, cube
  feedback, Lemma-Z row τ = 0.19) wired through the named hypotheses.
* Real-analytic facts enter only through rational bounds: Padé `e^x ≤ (2+x)/(2−x)` folded into
  the λ-forms of `TreeKP_B` and `HostChargingB`.
* `KPToFineAt_BRIDGE_B` carries the WHOLE analytic link to `fineAtB`; it is NOT in the spec.
* `H2_rest_OPENB` is OPEN.  Its in-plane ≥ 3-component piece (G2-c) is CONJ: it rests on an
  unproven all-shape scaling (scale 1.3873) and holds, if at all, only for t ≤ 0.1880 — it fails
  at the row radius 0.18860.  The off-plane active G4 piece has NO bound; active Γ_tot with
  ≥ 2 components and the A1 / H-up assumptions are also open.  Certified pieces (G1, R₂, G4
  inactive and in-plane active) sum to ≈ 4.49e−3 of the 0.008 room (numerical, not in Lean).
* Covers only `8 ≤ W (0+2+1)`; `W ≤ 7` is `hfine_step2B_small_OPEN` (uncovered).
* Strong-coupling bookkeeping only; not a 279/500 theorem for full SU(2); not chart closure;
  not gap evidence.  U(1) remark unchanged.

Mathlib-free; no sorry/admit/Classical/native_decide/omega/simpa/grind.
-/

import YMGap.RG.Step2Conditional
import YMGap.RG.Steps25OpenW558

namespace YMGap.RG.Step2ConditionalW558

set_option autoImplicit false

/-!
# Step2ConditionalW558 — module documentation

Plain statement of scope (read this first).
* The polymer quantities are UNINTERPRETED: `SphereGasModel` is a bundle of arbitrary
  relations; nothing here constructs or evaluates a polymer sum.
* `KPToFineAt_BRIDGE_B` carries the WHOLE analytic link from the KP / cluster expansion to
  `fineAtB`.  Without it nothing here says anything about `fineAtB`.
* `hfine_step2B_ge8_of_chainI_Gsplit` proves ONLY bookkeeping (wiring of the named
  hypotheses) and exact-rational certificates.
* `H2_rest_OPENB` is open: G2-c (≥ 3 in-plane components) is CONJ (unproven shape scaling);
  off-plane active G4 is unbounded.
* None of this is chart closure, and none of it is non-abelian evidence.
-/

open YMGap.Constructive
open YMGap.RG.Robust3CrossUniformW558 (fineAtB)
open YMGap.RG.Robust3UndershootAfScheduleW558 (robust3UndershootScheduleB)
open YMGap.RG.Steps25OpenW558 (hfine_step2B_OPEN)
open YMGap.RG.Step2Conditional
  (SphereGasModel betaB r018 s018 r01825 s01825 r020 s020 r021 s021 r023 s023 cubeCap
   etaRestClosing thrU1_W12 thrU1_W8to11 thrU1_W3 thrU1_W2 thrChainI thrChainII thrChainIIwit
   thrChainIII ChannelCut DegreeOneVanish ClusterReform TreeKP_B H2_cube_tree
   NonSphereWithinBudget_OPEN SpinGeOneWithinBudget_OPEN)

/-! ## 0. Targets -/

/-- Instance-B step-2 fine factor `1/64` at every width function with `W (0+2+1) ≥ 8`. -/
def hfine_step2B_ge8_OPEN : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → fineAtB W 2 (Q'.mkPos 1 64 (by decide))

/-- OPEN, uncovered: instance-B step-2 widths `W (0+2+1) ≤ 7`. -/
def hfine_step2B_small_OPEN : Prop :=
  ∀ W : Nat → Nat, W (0 + 2 + 1) ≤ 7 → fineAtB W 2 (Q'.mkPos 1 64 (by decide))

/-- PROVED: the two width ranges together give `Steps25OpenW558.hfine_step2B_OPEN`. -/
theorem hfine_step2B_of_small_and_ge8
    (hS : hfine_step2B_small_OPEN) (hL : hfine_step2B_ge8_OPEN) :
    hfine_step2B_OPEN := by
  intro W
  cases Nat.lt_or_ge (W (0 + 2 + 1)) 8 with
  | inl h => exact hS W (Nat.le_of_lt_succ h)
  | inr h => exact hL W h

/-! ## 1. Constants (exact rationals; spec decimals rounded safely) -/

/-- Fine nome of instance-B step 2 as used by `fineAtB W 2`: `nome (0+2+1)`. -/
def wStep2B : Q' := robust3UndershootScheduleB.nome (0 + 2 + 1)
/-- Spin-½ activity `u = w³` (A1). -/
def uStep2B : Q' := wStep2B ^ 3

theorem wStep2B_eqv : wStep2B.eqv (Q'.mkPos 279 500 (by decide)) := by decide
theorem uStep2B_eqv : uStep2B.eqv (Q'.mkPos 21717639 125000000 (by decide)) := by decide

/-- B6 Lemma-Z row τ = 0.19 (`z2_cert_W7.out`): `r` rounded DOWN, `s` rounded UP. -/
def r019 : Q' := Q'.mkPos 18860327 100000000 (by decide)
def s019 : Q' := Q'.mkPos 8167964 10000000000 (by decide)

/-- Activity cap for `H2_rest_OPENB`: `t ≤ 47/250 = 0.188` (G2-c is claimed only there). -/
def tCap : Q' := Q'.mkPos 47 250 (by decide)

/-- Sanity: 279/500 lies above every unconditional U1 threshold and Chain III. -/
theorem step2B_above_U1 :
    thrU1_W12 < wStep2B ∧ thrU1_W8to11 < wStep2B ∧ thrU1_W3 < wStep2B ∧
      thrU1_W2 < wStep2B ∧ thrChainIII < wStep2B := by decide
/-- Sanity: 279/500 lies below the Chain I / II conditional thresholds. -/
theorem step2B_below_conditional :
    wStep2B < thrChainI ∧ wStep2B < thrChainIIwit ∧ wStep2B < thrChainII := by decide

variable (G : SphereGasModel)

/-! ## 2. Chain I at 279/500, W ≥ 8 (hypotheses that depend on the nome or the rows) -/

/-- I.2 `Z2CertTableB` [CERT-NUM; float64 forward-error, not interval arithmetic].  B6 rows on
`T_W`, `W ≥ 8`: τ = 0.18, 0.1825, 0.19, 0.20, 0.21, 0.23 (τ = 0.19 new; τ = 0.20 with the
safe-side rounding `r020 = 0.19740567`, `s020 = 1.441290e−3`). -/
def Z2CertTableB : Prop :=
  ∀ W : Nat, 8 ≤ W →
    G.z2Sum W r018 s018 ∧ G.z2Sum W r01825 s01825 ∧ G.z2Sum W r019 s019 ∧
      G.z2Sum W r020 s020 ∧ G.z2Sum W r021 s021 ∧ G.z2Sum W r023 s023

/-- I.7 `SheetActivityB` (B1 + II.4) at `u = (279/500)³`: if `u·λ ≤ ρ` then `σ₁(λ) ≤ 4Σ_Y ρ^{|Y|}`. -/
def SheetActivityB : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam rho s : Q',
    uStep2B * lam ≤ rho → G.z2Sum W rho s → G.sig1 W lam (4 * s)

/-- G-split glue `HostChargingB` [PROVED-SELF, §26.3] at `u = (279/500)³`:
`σ_K(b) ≤ σ₁(b + η_cube + η_rest)`, attached activity `t ≥ u·e^{b+η}`; λ-form, `E ≥ e^η` (Padé). -/
def HostChargingB : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam t ec er E B : Q',
    (2 + (ec + er)) ≤ E * (2 - (ec + er)) →
    uStep2B * (lam * E) ≤ t →
    G.etaCube W t ec → G.etaRest W t er →
    G.sig1 W (lam * E) B → G.sigK W lam B

/-- `H2_rest_OPENB er` [OPEN].  Non-cube S′, large-S′ tail and non-tree vertices at 279/500,
for attached activities `t ≤ tCap = 47/250` (NOT up to the row radius: G2-c fails there).
Status of the pieces (`steps25_H2rest_status.md`): G1, R₂, G4 inactive (given A1, H-up) and
G4 in-plane active are CERT-NUM (sum ≈ 4.49e−3); the in-plane ≥ 3-component piece G2-c is CONJ
(rests on an unproven all-shape scaling); off-plane active G4 is OPEN with no bound; active
Γ_tot with ≥ 2 components and A1 / H-up are open. -/
def H2_rest_OPENB (er : Q') : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ t : Q', (0 : Q') ≤ t → t ≤ tCap → G.etaRest W t er

/-- `KPToFineAt_BRIDGE_B` [BRIDGE — NOT IN SPEC; no audited proof cited].  All-spin KP
convergence with `6Ψ ≤ a` on the step-2 width ⇒ the instance-B two-step factor `1/64`.
Carries the WHOLE analytic link to `fineAtB`; the polymer quantities are uninterpreted, so the
main theorem proves only bookkeeping and certificates.  Not chart closure. -/
def KPToFineAt_BRIDGE_B : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → ∀ a P : Q', (6 : Q') * P ≤ a →
    G.kpAllSpin (W (0 + 2 + 1)) a P → fineAtB W 2 (Q'.mkPos 1 64 (by decide))

/-! ## 3. Certificate (exact rationals) at 279/500, row τ = 0.19, G-split -/

def psiB : Q' := 4 * s019
def aB : Q' := 6 * psiB
def lamB : Q' := Q'.mkPos 25831 25000 (by decide)
def EB : Q' := Q'.mkPos 1047083 1000000 (by decide)
def tB : Q' := Q'.mkPos 187969 1000000 (by decide)
/-- Self-consistent cube η at 279/500 with η_rest = 0.008 (η_cube ≈ 0.037994, rounded up). -/
def etaCubeB : Q' := Q'.mkPos 38 1000 (by decide)

theorem certB_tree : (2 + aB) * (betaB psiB * betaB psiB) ≤ lamB * (2 - aB) := by decide
theorem certB_exp :
    (2 + (etaCubeB + etaRestClosing)) ≤ EB * (2 - (etaCubeB + etaRestClosing)) := by
  decide
theorem certB_act : uStep2B * (lamB * EB) ≤ tB := by decide
theorem certB_cap : tB ≤ tCap := by decide
theorem certB_radius : tCap ≤ r019 := by decide
theorem certB_cube : (4 : Q') * cubeCap * tB ^ 6 ≤ etaCubeB := by decide
theorem certB_sheet : uStep2B * (lamB * EB) ≤ r019 := by decide

/-! ## 4. Main theorem (G-split, W558) -/

/-- **PROVED (bookkeeping + certificates only).**  Chain I (I.2–I.7 at 279/500) + G-split
(`HostChargingB`, `H2_cube_tree`, `H2_rest_OPENB 0.008`) + `NonSphereWithinBudget_OPEN` +
`SpinGeOneWithinBudget_OPEN` + `KPToFineAt_BRIDGE_B` ⇒ `hfine_step2B_ge8_OPEN`.
Supersolution witness: τ = 0.19 row, Ψ̂ = 4·s019, a = 6Ψ̂, δ = 0, η_cube = 0.038,
η_rest = 0.008, attached activity t = 0.187969 ≤ tCap = 0.188.  Conditional on the OPEN
`H2_rest_OPENB` (G2-c CONJ, off-plane G4 open) and the bridge; not chart closure. -/
theorem hfine_step2B_ge8_of_chainI_Gsplit
    (hZ2 : Z2CertTableB G) (hCH : ChannelCut G) (hV : DegreeOneVanish G)
    (hCR : ClusterReform G) (hTree : TreeKP_B G) (hAct : SheetActivityB G)
    (hHost : HostChargingB G) (hCube : H2_cube_tree G)
    (hRest : H2_rest_OPENB G etaRestClosing)
    (hNS : NonSphereWithinBudget_OPEN G) (hS1 : SpinGeOneWithinBudget_OPEN G)
    (hBr : KPToFineAt_BRIDGE_B G) :
    hfine_step2B_ge8_OPEN := by
  intro W hW
  have hrow : G.z2Sum (W (0 + 2 + 1)) r019 s019 := (hZ2 (W (0 + 2 + 1)) hW).2.2.1
  have hs1 : G.sig1 (W (0 + 2 + 1)) (lamB * EB) (4 * s019) :=
    hAct (W (0 + 2 + 1)) hW (lamB * EB) r019 s019 certB_sheet hrow
  have hc : G.etaCube (W (0 + 2 + 1)) tB etaCubeB :=
    hCube (W (0 + 2 + 1)) hW tB etaCubeB (by decide) certB_cube
  have hr : G.etaRest (W (0 + 2 + 1)) tB etaRestClosing :=
    hRest (W (0 + 2 + 1)) hW tB (by decide) certB_cap
  have hK : G.sigK (W (0 + 2 + 1)) lamB psiB :=
    hHost (W (0 + 2 + 1)) hW lamB tB etaCubeB etaRestClosing EB (4 * s019)
      certB_exp certB_act hc hr hs1
  have hT : G.treeSum (W (0 + 2 + 1)) aB psiB :=
    hTree (W (0 + 2 + 1)) hW psiB aB lamB (by decide) (by decide) (by decide)
      certB_tree hK
  have hSph : G.kpSphere (W (0 + 2 + 1)) aB psiB :=
    hCR hCH hV (W (0 + 2 + 1)) hW aB psiB hT
  have h6 : (6 : Q') * psiB ≤ aB := by decide
  cases hNS (W (0 + 2 + 1)) hW aB psiB h6 hSph with
  | intro P1 hP1 =>
    cases hS1 (W (0 + 2 + 1)) hW aB P1 hP1.1 hP1.2 with
    | intro P2 hP2 => exact hBr W hW aB P2 hP2.1 hP2.2

end YMGap.RG.Step2ConditionalW558

#print axioms YMGap.RG.Step2ConditionalW558.hfine_step2B_of_small_and_ge8
#print axioms YMGap.RG.Step2ConditionalW558.wStep2B_eqv
#print axioms YMGap.RG.Step2ConditionalW558.uStep2B_eqv
#print axioms YMGap.RG.Step2ConditionalW558.step2B_above_U1
#print axioms YMGap.RG.Step2ConditionalW558.step2B_below_conditional
#print axioms YMGap.RG.Step2ConditionalW558.certB_tree
#print axioms YMGap.RG.Step2ConditionalW558.certB_exp
#print axioms YMGap.RG.Step2ConditionalW558.certB_act
#print axioms YMGap.RG.Step2ConditionalW558.certB_cap
#print axioms YMGap.RG.Step2ConditionalW558.certB_radius
#print axioms YMGap.RG.Step2ConditionalW558.certB_cube
#print axioms YMGap.RG.Step2ConditionalW558.certB_sheet
#print axioms YMGap.RG.Step2ConditionalW558.hfine_step2B_ge8_of_chainI_Gsplit
