/-
# Step n = 2 (fine nome 14/25): conditional chain hypotheses → fineAt for widths ≥ 8

Additive DRAFT.  Encodes the hypothesis ledger
`math_frontier_1119/conditional_chain_hyps.md` (Chains I–III + addendum G) and
`steps25_frontier.md` §26.6 / §27 as named `Prop`s, and proves ONE real
implication: Chain I (with the addendum-G split of (H2)) plus explicitly named
non-sphere / spin ≥ 1 / KP→fineAt bridge hypotheses ⇒ `hfine_step2_ge8_OPEN`.

Honesty notes.
* The polymer quantities (σ₁, σ_K, Lemma-Z sums, KP sums, host-charged
  exponents) are NOT formalised here.  They enter as uninterpreted relations in
  `SphereGasModel`; every hypothesis is a statement about those relations.  The
  proved content is the exact-rational certificate chain (KP supersolution at
  14/25, cube feedback, Lemma-Z row) wired through the named hypotheses.
* Real-analytic facts enter only through rational bounds: `e^x ≤ (2+x)/(2−x)`
  (Padé, 0 ≤ x < 2) is folded into the λ-form of `TreeKP_B`, `HostCharging` and
  `H2_cluster_OPEN`, where λ is a rational upper bound for the weight `e^b`.
* `KPToFineAt_BRIDGE` (cluster expansion ⇒ two-step factor 1/64) is NOT in the
  spec; it is an explicit named hypothesis, not hidden.
* Covers only `8 ≤ W (0+2+1)`.  `W ≤ 7` is `hfine_step2_small_OPEN` (uncovered).
* Strong-coupling bookkeeping only; not a 14/25 theorem for full SU(2); not
  chart closure; not gap evidence.

Mathlib-free; no sorry/admit/Classical/native_decide/omega/simpa/grind.
-/

import YMGap.RG.Steps25Open

namespace YMGap.RG.Step2Conditional

set_option autoImplicit false

/-!
# Step2Conditional — module documentation

Plain statement of scope (read this first).
* The polymer quantities are UNINTERPRETED: `SphereGasModel` is a bundle of
  arbitrary relations; nothing here constructs or evaluates a polymer sum.
* `KPToFineAt_BRIDGE` carries the WHOLE analytic link from the KP / cluster
  expansion to `fineAt`.  Without it nothing here says anything about `fineAt`.
* The main theorems (`hfine_step2_ge8_of_chainI_Gsplit`,
  `hfine_step2_ge8_of_chainI_H2cluster`) prove ONLY bookkeeping (wiring of the
  named hypotheses) and exact-rational certificates.
* None of this is chart closure, and none of it is non-abelian evidence.
-/

open YMGap.Constructive
open YMGap.RG.Robust3CrossUniform (fineAt)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule)
open YMGap.RG.Steps25Open (hfine_step2_OPEN)

/-! ## 0. Targets -/

/-- Step-2 fine factor `1/64` at every width function whose step-2 width
`W (0+2+1)` is at least 8.  Same `fineAt` form and arguments as
`Steps25Open.hfine_step2_OPEN` (which is left untouched). -/
def hfine_step2_ge8_OPEN : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → fineAt W 2 (Q'.mkPos 1 64 (by decide))

/-- OPEN, uncovered: step-2 widths `W (0+2+1) ≤ 7`.  Chain I uses the B6
Lemma-Z table (label 7 ⇒ W ≥ 8, B5 torus rule); §27.5 "Small widths 3 ≤ W ≤ 7:
not attempted".  Nothing in this file addresses it. -/
def hfine_step2_small_OPEN : Prop :=
  ∀ W : Nat → Nat, W (0 + 2 + 1) ≤ 7 → fineAt W 2 (Q'.mkPos 1 64 (by decide))

/-- PROVED: the two width ranges together give `Steps25Open.hfine_step2_OPEN`. -/
theorem hfine_step2_of_small_and_ge8
    (hS : hfine_step2_small_OPEN) (hL : hfine_step2_ge8_OPEN) :
    hfine_step2_OPEN := by
  intro W
  cases Nat.lt_or_ge (W (0 + 2 + 1)) 8 with
  | inl h => exact hS W (Nat.le_of_lt_succ h)
  | inr h => exact hL W h

/-! ## 1. Constants (exact rationals; decimals of the spec rounded safely) -/

/-- Fine nome of step 2 as used by `fineAt W 2`: `nome (0+2+1)`. -/
def wStep2 : Q' := robust3UndershootSchedule.nome (0 + 2 + 1)
/-- Spin-½ activity `u = w³` (A1). -/
def uStep2 : Q' := wStep2 ^ 3

theorem wStep2_eqv : wStep2.eqv (Q'.mkPos 14 25 (by decide)) := by decide
theorem uStep2_eqv : uStep2.eqv (Q'.mkPos 2744 15625 (by decide)) := by decide

/-- Bracket B (ψ = 1): `β_B(Ψ) = 1 + 2Ψ + 3Ψ²` (A5). -/
def betaB (P : Q') : Q' := 1 + 2 * P + 3 * (P * P)
/-- Bracket A (ψ ≤ 2/3): `β_A(Ψ) = 1 + (4/3)Ψ + Ψ²` (A5). -/
def betaA (P : Q') : Q' := 1 + Q'.mkPos 4 3 (by decide) * P + P * P

/-- B6 certified Lemma-Z rows `(r_k, s_k)` (exact rational `r`, float-with-error `s`). -/
def r018 : Q' := Q'.mkPos 17925463 100000000 (by decide)
def s018 : Q' := Q'.mkPos 4601068 10000000000 (by decide)
def r01825 : Q' := Q'.mkPos 18162747 100000000 (by decide)
def s01825 : Q' := Q'.mkPos 5312194 10000000000 (by decide)
def r020 : Q' := Q'.mkPos 19740567 100000000 (by decide)
def s020 : Q' := Q'.mkPos 1441290 1000000000 (by decide)
def r021 : Q' := Q'.mkPos 20525262 100000000 (by decide)
def s021 : Q' := Q'.mkPos 2511843 1000000000 (by decide)
def r023 : Q' := Q'.mkPos 21516341 100000000 (by decide)
def s023 : Q' := Q'.mkPos 7167433 1000000000 (by decide)

/-- §27.3 cube charge: `F(Q3) = 20911/81` (exact), per-plaquette cap
`2·5·F(Q3)/12 = 104555/486 ≈ 215.1337`.  (The spec's "215.13" is rounded DOWN,
i.e. in the unsafe direction; the exact value is used here.) -/
def FQ3 : Q' := Q'.mkPos 20911 81 (by decide)
def cubeCap : Q' := Q'.mkPos 104555 486 (by decide)
theorem cubeCap_eqv : cubeCap.eqv ((2 : Q') * 5 * FQ3 * Q'.mkPos 1 12 (by decide)) := by
  decide

/-- Addendum G: spec value of the non-cube η-room at 14/25 (`η_rest ≤ 0.0186`). -/
def etaRestSpec : Q' := Q'.mkPos 186 10000 (by decide)
/-- η_rest value at which the certified chain below actually closes (see §5 note). -/
def etaRestClosing : Q' := Q'.mkPos 8 1000 (by decide)
/-- Self-consistent cube η used in the certificate (spec η* = 0.0405 ignores the
rest-feedback; with η_rest = 0.008 the self-consistent cube value is ≈ 0.0508). -/
def etaCubeCert : Q' := Q'.mkPos 5081 100000 (by decide)

/-- I.8 spec constants: `η ≤ 0.003`, `δ ≤ 1e−4`. -/
def etaH2 : Q' := Q'.mkPos 3 1000 (by decide)
def deltaH2 : Q' := Q'.mkPos 1 10000 (by decide)

/-- B16 surcharge room: κ_max = 1.0713 (bracket A, τ = 0.21) and 1.0610
(bracket B / ψ = 1, τ = 0.20). [PROVED-AUD, audit 24to25 item 4] -/
def kappaMaxA : Q' := Q'.mkPos 10713 10000 (by decide)
def kappaMaxB : Q' := Q'.mkPos 10610 10000 (by decide)

/-- B7 partner-tail constants: `t_c = 0.11694` (μ_sheet ≤ 8.551), certificate
`F = 523/2000`, `R = 130767/100000 ≥ 5^{1/6}`. [PROVED-AUD, audit 13to14] -/
def tcB7 : Q' := Q'.mkPos 11694 100000 (by decide)
def muSheet : Q' := Q'.mkPos 8551 1000 (by decide)
def FB7 : Q' := Q'.mkPos 523 2000 (by decide)
def RB7 : Q' := Q'.mkPos 130767 100000 (by decide)
/-- Certified: `RB7 ≥ 5^{1/6}` in the form `5 ≤ RB7⁶`. -/
theorem RB7_sixth_ge_five : (5 : Q') ≤ RB7 ^ 6 := by decide

/-- Thresholds (U1 [PROVED-AUD, audit 13to14]; conditional ones as labelled). -/
def thrU1_W12 : Q' := Q'.mkPos 4293 10000 (by decide)   -- W ≥ 12
def thrU1_W8to11 : Q' := Q'.mkPos 4252 10000 (by decide) -- 8 ≤ W ≤ 11
def thrU1_W3 : Q' := Q'.mkPos 3650 10000 (by decide)    -- W ≥ 3 (tail only)
def thrU1_W2 : Q' := Q'.mkPos 3262 10000 (by decide)    -- W ≥ 2
def thrChainI : Q' := Q'.mkPos 5704 10000 (by decide)   -- §26.6, conditional
def thrChainII : Q' := Q'.mkPos 5730 10000 (by decide)  -- C ≡ 1 gas (bisection)
def thrChainIIwit : Q' := Q'.mkPos 5729 10000 (by decide) -- witnessed (τ = 0.21)
def thrChainIII : Q' := Q'.mkPos 4380 10000 (by decide) -- parity route, cond. P1″

/-- Sanity: step 2 lies ABOVE every unconditional U1 threshold (U1 does not
cover 14/25) and above Chain III; below the Chain I / II conditional thresholds. -/
theorem step2_above_U1 :
    thrU1_W12 < wStep2 ∧ thrU1_W8to11 < wStep2 ∧ thrU1_W3 < wStep2 ∧
      thrU1_W2 < wStep2 ∧ thrChainIII < wStep2 := by decide
theorem step2_below_conditional :
    wStep2 < thrChainI ∧ wStep2 < thrChainIIwit ∧ wStep2 < thrChainII := by decide

/-! ## 2. Uninterpreted polymer data -/

/-- UNINTERPRETED relations for the spin-½ / all-spin polymer gas at the
step-2 nome on the torus `T_W` (first argument = width `W`).  Upper-bound
relations: `rel W x B` reads "quantity at parameter x is ≤ B".
The fields are arbitrary: nothing in this file defines or computes any polymer
quantity, so every hypothesis below is a statement about these relations only.
The link to `fineAt` is carried entirely by `KPToFineAt_BRIDGE`; the main
theorems prove only bookkeeping and certificates.  Not chart closure; not
non-abelian evidence. -/
structure SphereGasModel where
  /-- `z2Sum W ρ s`: `Σ_{Y∋p, connected Z₂ cycle} ρ^{|Y|} ≤ s` on `T_W` (B4). -/
  z2Sum : Nat → Q' → Q' → Prop
  /-- `sig1 W λ B`: `σ₁ := sup_p Σ_{single sphere sheets S∋p} 4u^{|S|} λ^{|S|} ≤ B`, `λ ≥ e^b`. -/
  sig1 : Nat → Q' → Q' → Prop
  /-- `sigK W λ B`: Γ-cluster sum `σ_K := sup_p Σ_{K∋p} |ρ(K)| λ^{|K|} ≤ B`, `λ ≥ e^b` (A7). -/
  sigK : Nat → Q' → Q' → Prop
  /-- `treeSum W a Ψ`: bracket-B tree sum over link-connected cluster families ≤ Ψ. -/
  treeSum : Nat → Q' → Q' → Prop
  /-- `kpSphere W a Ψ`: `Σ_{X∋p, sphere sector} |z(X)| e^{a|X|} ≤ Ψ` (Chain I conclusion). -/
  kpSphere : Nat → Q' → Q' → Prop
  /-- `kpSpinHalf W a Ψ`: same sum over the FULL spin-½ sector (all sheet types). -/
  kpSpinHalf : Nat → Q' → Q' → Prop
  /-- `kpAllSpin W a Ψ`: same sum over all spins. -/
  kpAllSpin : Nat → Q' → Q' → Prop
  /-- `etaCube W t η`: cube part of the host-charged exponent (§26.3) at attached activity `t` is ≤ η. -/
  etaCube : Nat → Q' → Q' → Prop
  /-- `etaRest W t η`: non-cube S′ + tail + non-tree part of the host-charged exponent ≤ η. -/
  etaRest : Nat → Q' → Q' → Prop
  /-- Statement of Lemma CH (B13), uninterpreted. -/
  channelCut : Prop
  /-- Statement of Lemma V′ (B14), uninterpreted. -/
  degOneVanish : Prop
  /-- Statement of the subcubic two-sphere law (B19 / §27.2), uninterpreted. -/
  twoSphereLawSubcubic : Prop

variable (G : SphereGasModel)

/-! ## 3. Chain I (§26.6), sphere sector, W ≥ 8 -/

/-- I.2 `Z2CertTable` [CERT-NUM, audits 15, 16to18; float64 forward-error, not
interval arithmetic].  B6 rows on `T_W`, `W ≥ 8` (label 7 + B5 torus rule):
τ = 0.18, 0.1825, 0.20, 0.21, 0.23 with the `(r_k, s_k)` above. -/
def Z2CertTable : Prop :=
  ∀ W : Nat, 8 ≤ W →
    G.z2Sum W r018 s018 ∧ G.z2Sum W r01825 s01825 ∧ G.z2Sum W r020 s020 ∧
      G.z2Sum W r021 s021 ∧ G.z2Sum W r023 s023

/-- I.3 `ChannelCut` = Lemma CH (B13) [PROVED-AUD, audit 24to25 item 1].
(§26.6 (H1) still says "proved, unaudited"; the ledger B13 supersedes.) -/
def ChannelCut : Prop := G.channelCut

/-- I.4 `DegreeOneVanish` = Lemma V′ (B14) [PROVED-AUD, audit 24to25 item 2]. -/
def DegreeOneVanish : Prop := G.degOneVanish

/-- I.5 `ClusterReform` (B15) [PROVED-SELF, §26.3; |w| only, the "w ≥ 0" part of
(H1) dropped per addendum G / §27.1]: given Lemma CH and V′, the sphere-sector
KP sum is bounded by the bracket-B tree sum over Γ-cluster families
(inter-cluster factor exactly 1). -/
def ClusterReform : Prop :=
  G.channelCut → G.degOneVanish →
    ∀ W : Nat, 8 ≤ W → ∀ a P : Q', G.treeSum W a P → G.kpSphere W a P

/-- I.6 `TreeKP_B` (B3, bracket B) [PROVED-AUD, audits 9to12, 24to25 item 4],
λ-form: if `σ_K(λ) ≤ Ψ` at a rational weight `λ ≥ e^{a}·β_B(Ψ)²` (with
`e^a ≤ (2+a)/(2−a)`, the Padé bound, and σ_K monotone in λ) and `6Ψ ≤ a`, the
tree sum is ≤ Ψ (supersolution ⇒ Ψ* ≤ Ψ). -/
def TreeKP_B : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ P a lam : Q',
    (0 : Q') ≤ P → (6 : Q') * P ≤ a → a < 2 →
    (2 + a) * (betaB P * betaB P) ≤ lam * (2 - a) →
    G.sigK W lam P → G.treeSum W a P

/-- I.7 `SheetActivity` (B1 `|ζ₀(S)| ≤ 4u^{|S|}` [PROVED-AUD, audit 9to12],
combined with II.4 `SheetAsZ2Cycle` [PROVED-AUD, §15.1/audit 15]: a sphere
sheet's plaquette set is a connected Z₂ cycle): if `u·λ ≤ ρ` then
`σ₁(λ) ≤ 4·Σ_Y ρ^{|Y|}`. -/
def SheetActivity : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam rho s : Q',
    uStep2 * lam ≤ rho → G.z2Sum W rho s → G.sig1 W lam (4 * s)

/-- G-split glue `HostCharging` [PROVED-SELF, §26.3 host-charged exponent,
§26.5 "provable now" for tree-parent loops; non-tree parts are delegated to
`H2_rest_OPEN`]: `σ_K(b) ≤ σ₁(b + η_cube + η_rest)`, with attached activity
`t ≥ u·e^{b+η}`; λ-form with `E ≥ e^{η}` via Padé. -/
def HostCharging : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam t ec er E B : Q',
    (2 + (ec + er)) ≤ E * (2 - (ec + er)) →
    uStep2 * (lam * E) ≤ t →
    G.etaCube W t ec → G.etaRest W t er →
    G.sig1 W (lam * E) B → G.sigK W lam B

/-- `H2_cube_tree` [proved on paper, unaudited = PROVED-SELF, §27.3, tree
attachments only; CERT-NUM constant F(Q3) = 20911/81]:
`η_cube ≤ 4t⁶·(2·5·F(Q3)/12) = 4t⁶·215.1337…` at attached activity `t`. -/
def H2_cube_tree : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ t eta : Q',
    (0 : Q') ≤ t → (4 : Q') * cubeCap * t ^ 6 ≤ eta → G.etaCube W t eta

/-- `H2_rest_OPEN er` [CONJ; addendum G: non-cube S′, the large-S′ tail and
non-tree vertices].  Spec value at 14/25: `er = etaRestSpec = 0.0186`, at
activities up to the certified radius `r(τ=0.20)`. -/
def H2_rest_OPEN (er : Q') : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ t : Q', (0 : Q') ≤ t → t ≤ r020 → G.etaRest W t er

/-- I.8 `H2_cluster_OPEN η δ` [CONJ; the open multi-junction estimate]:
`σ_K(b) ≤ σ₁(b + η) + δ`, λ-form with `E ≥ e^{η}`.  Spec: η ≤ 0.003, δ ≤ 1e−4. -/
def H2_cluster_OPEN (eta delta : Q') : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam E B : Q',
    (2 + eta) ≤ E * (2 - eta) → G.sig1 W (lam * E) B → G.sigK W lam (B + delta)

/-- `NonSphereWithinBudget_OPEN` [CONJ].  Non-sphere sheets (not lattice-2-regular,
incl. self-junction sheets, or resolved χ < 2) are bounded within the same
KP budget: from the sphere-sector bound at `a` one gets a full spin-½ bound
`Ψ'` with `6Ψ' ≤ a` at the same `a`.  §26.6 covers sphere sheets only; this
hypothesis is what removes that restriction (it is NOT baked into the target). -/
def NonSphereWithinBudget_OPEN : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ a P : Q', (6 : Q') * P ≤ a → G.kpSphere W a P →
    ∃ P' : Q', (6 : Q') * P' ≤ a ∧ G.kpSpinHalf W a P'

/-- `SpinGeOneWithinBudget_OPEN` [CONJ; ADDED hypothesis, not in spec
conditional_chain_hyps.md; analogue of II.6, §12.3 sketch κ ≈ 0.24].
Spin ≥ 1 is listed as "NOT covered" by Chain I; required to reach fineAt. -/
def SpinGeOneWithinBudget_OPEN : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ a P : Q', (6 : Q') * P ≤ a → G.kpSpinHalf W a P →
    ∃ P' : Q', (6 : Q') * P' ≤ a ∧ G.kpAllSpin W a P'

/-- `KPToFineAt_BRIDGE` [BRIDGE — NOT IN SPEC; no audited proof cited].  All-spin
KP convergence with `6Ψ ≤ a` on the step-2 width ⇒ the Wilson vacuum two-step
factor `1/64` (`fineAt W 2`).  Carries the cluster-expansion → decay →
two-step-factor link; stated explicitly so it is not hidden.
This hypothesis carries the WHOLE analytic link to `fineAt`: the polymer
quantities of `SphereGasModel` are uninterpreted, so the main theorems prove
only bookkeeping and certificates, and reach `fineAt` solely through this
bridge.  Not chart closure; not non-abelian evidence. -/
def KPToFineAt_BRIDGE : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → ∀ a P : Q', (6 : Q') * P ≤ a →
    G.kpAllSpin (W (0 + 2 + 1)) a P → fineAt W 2 (Q'.mkPos 1 64 (by decide))

/-- `CEffLeTwo_CONJ` [CONJ; §26.4–26.5: "true by a wide margin on everything
computed, not provable by the tree/sup method"; indicative c_eff ≈ 1 + η/(4Ψ*)].
Attachment factor ≤ 2: `σ_K ≤ 2·σ₁` at the same weight.  Not used below. -/
def CEffLeTwo_CONJ : Prop :=
  ∀ W : Nat, 8 ≤ W → ∀ lam B : Q', G.sig1 W lam B → G.sigK W lam (2 * B)

/-- B19 two-sphere law [PROVED-SELF modulo scan audit, §27.2]; scope exactly:
subcubic Γ with ≤ 2 spin-1 sheets per vertex, `|w| = (4/3)^{n₃/2}`.  The
degree-4 form is FALSE locally (49/9 occurs).  Evidence for (H2); not used. -/
def TwoSphereLawSubcubic : Prop := G.twoSphereLawSubcubic

/-! ## 4. Certificate (exact rationals) at 14/25, row τ = 0.20, G-split -/

def psiG : Q' := 4 * s020
def aG : Q' := 6 * psiG
def lamG : Q' := Q'.mkPos 105943 100000 (by decide)
def EG : Q' := Q'.mkPos 1060593 1000000 (by decide)
def tG : Q' := Q'.mkPos 197328 1000000 (by decide)

theorem certG_tree : (2 + aG) * (betaB psiG * betaB psiG) ≤ lamG * (2 - aG) := by decide
theorem certG_exp :
    (2 + (etaCubeCert + etaRestClosing)) ≤ EG * (2 - (etaCubeCert + etaRestClosing)) := by
  decide
theorem certG_act : uStep2 * (lamG * EG) ≤ tG := by decide
theorem certG_radius : tG ≤ r020 := by decide
theorem certG_cube : (4 : Q') * cubeCap * tG ^ 6 ≤ etaCubeCert := by decide
theorem certG_sheet : uStep2 * (lamG * EG) ≤ r020 := by decide

/-- Records `etaRestClosing = 0.008 < etaRestSpec = 0.0186`.  The spec's 0.0186
room ignored the feedback from the cube bound: raising the total η raises the
attached activity `t`, and with it `4t⁶·215.13…`, so with the B6 rows the
certifiable η_rest is only ≈ 0.0083.  `H2_rest_OPEN etaRestClosing` (0.008) is
therefore the honest, STRONGER open hypothesis.  The math side is rechecking
the room, so this constant may change in a follow-up. -/
theorem etaRestClosing_lt_spec : etaRestClosing < etaRestSpec := by decide

/-! ## 5. Main theorem (G-split) -/

/-- **PROVED.**  Chain I (I.2–I.7) + G-split (`HostCharging`, `H2_cube_tree`,
`H2_rest_OPEN 0.008`) + `NonSphereWithinBudget_OPEN` +
`SpinGeOneWithinBudget_OPEN` + `KPToFineAt_BRIDGE` ⇒ `hfine_step2_ge8_OPEN`.
Supersolution witness: τ = 0.20 row, Ψ̂ = 4·s, a = 6Ψ̂, δ = 0,
η_cube = 0.05081 (self-consistent with feedback), η_rest = 0.008.
NOTE: with η_rest = 0.0186 (spec) the B6 rows do not close (see report). -/
theorem hfine_step2_ge8_of_chainI_Gsplit
    (hZ2 : Z2CertTable G) (hCH : ChannelCut G) (hV : DegreeOneVanish G)
    (hCR : ClusterReform G) (hTree : TreeKP_B G) (hAct : SheetActivity G)
    (hHost : HostCharging G) (hCube : H2_cube_tree G)
    (hRest : H2_rest_OPEN G etaRestClosing)
    (hNS : NonSphereWithinBudget_OPEN G) (hS1 : SpinGeOneWithinBudget_OPEN G)
    (hBr : KPToFineAt_BRIDGE G) :
    hfine_step2_ge8_OPEN := by
  intro W hW
  have hrow : G.z2Sum (W (0 + 2 + 1)) r020 s020 := (hZ2 (W (0 + 2 + 1)) hW).2.2.1
  have hs1 : G.sig1 (W (0 + 2 + 1)) (lamG * EG) (4 * s020) :=
    hAct (W (0 + 2 + 1)) hW (lamG * EG) r020 s020 certG_sheet hrow
  have hc : G.etaCube (W (0 + 2 + 1)) tG etaCubeCert :=
    hCube (W (0 + 2 + 1)) hW tG etaCubeCert (by decide) certG_cube
  have hr : G.etaRest (W (0 + 2 + 1)) tG etaRestClosing :=
    hRest (W (0 + 2 + 1)) hW tG (by decide) certG_radius
  have hK : G.sigK (W (0 + 2 + 1)) lamG psiG :=
    hHost (W (0 + 2 + 1)) hW lamG tG etaCubeCert etaRestClosing EG (4 * s020)
      certG_exp certG_act hc hr hs1
  have hT : G.treeSum (W (0 + 2 + 1)) aG psiG :=
    hTree (W (0 + 2 + 1)) hW psiG aG lamG (by decide) (by decide) (by decide)
      certG_tree hK
  have hSph : G.kpSphere (W (0 + 2 + 1)) aG psiG :=
    hCR hCH hV (W (0 + 2 + 1)) hW aG psiG hT
  have h6 : (6 : Q') * psiG ≤ aG := by decide
  cases hNS (W (0 + 2 + 1)) hW aG psiG h6 hSph with
  | intro P1 hP1 =>
    cases hS1 (W (0 + 2 + 1)) hW aG P1 hP1.1 hP1.2 with
    | intro P2 hP2 => exact hBr W hW aG P2 hP2.1 hP2.2

/-! ## 6. Alternative: spec Chain I with I.8 (η ≤ 0.003, δ ≤ 1e−4), row τ = 0.1825 -/

def psiI : Q' := 4 * s01825 + deltaH2
def aI : Q' := 6 * psiI
def lamI : Q' := Q'.mkPos 10226 10000 (by decide)
def EI : Q' := Q'.mkPos 10031 10000 (by decide)

theorem certI_tree : (2 + aI) * (betaB psiI * betaB psiI) ≤ lamI * (2 - aI) := by decide
theorem certI_exp : (2 + etaH2) ≤ EI * (2 - etaH2) := by decide
theorem certI_sheet : uStep2 * (lamI * EI) ≤ r01825 := by decide

/-- **PROVED.**  Spec Chain I verbatim (I.2–I.8 with η = 0.003, δ = 1e−4) +
non-sphere + spin ≥ 1 + bridge ⇒ `hfine_step2_ge8_OPEN`.  Witness of
conditional_chain_hyps.md §D Chain I (τ = 0.1825). -/
theorem hfine_step2_ge8_of_chainI_H2cluster
    (hZ2 : Z2CertTable G) (hCH : ChannelCut G) (hV : DegreeOneVanish G)
    (hCR : ClusterReform G) (hTree : TreeKP_B G) (hAct : SheetActivity G)
    (hH2 : H2_cluster_OPEN G etaH2 deltaH2)
    (hNS : NonSphereWithinBudget_OPEN G) (hS1 : SpinGeOneWithinBudget_OPEN G)
    (hBr : KPToFineAt_BRIDGE G) :
    hfine_step2_ge8_OPEN := by
  intro W hW
  have hrow : G.z2Sum (W (0 + 2 + 1)) r01825 s01825 := (hZ2 (W (0 + 2 + 1)) hW).2.1
  have hs1 : G.sig1 (W (0 + 2 + 1)) (lamI * EI) (4 * s01825) :=
    hAct (W (0 + 2 + 1)) hW (lamI * EI) r01825 s01825 certI_sheet hrow
  have hK : G.sigK (W (0 + 2 + 1)) lamI psiI :=
    hH2 (W (0 + 2 + 1)) hW lamI EI (4 * s01825) certI_exp hs1
  have hT : G.treeSum (W (0 + 2 + 1)) aI psiI :=
    hTree (W (0 + 2 + 1)) hW psiI aI lamI (by decide) (by decide) (by decide)
      certI_tree hK
  have hSph : G.kpSphere (W (0 + 2 + 1)) aI psiI :=
    hCR hCH hV (W (0 + 2 + 1)) hW aI psiI hT
  have h6 : (6 : Q') * psiI ≤ aI := by decide
  cases hNS (W (0 + 2 + 1)) hW aI psiI h6 hSph with
  | intro P1 hP1 =>
    cases hS1 (W (0 + 2 + 1)) hW aI P1 hP1.1 hP1.2 with
    | intro P2 hP2 => exact hBr W hW aI P2 hP2.1 hP2.2

/-! ## 7. Chains II and III: hypothesis bundles (no implications proved) -/

/-- Uninterpreted statements for Chain II (C ≡ 1 comparison gas, bracket A). -/
structure ChainIIData where
  resolutionTheoremC : Prop
  treeKP_A : Prop
  sheetAsZ2Cycle : Prop
  /-- `junctionExcess a E`: 4·Σ_Y (u e^{b_a})^{|Y|}(Π_ℓ C_{m_ℓ} − 1) ≤ E at KP parameter a. -/
  junctionExcess : Q' → Q' → Prop
  spinGeOneFits : Prop
  /-- `surchargeRoom κ`: uniform surcharge κ fits the certified C ≡ 1 gas (B16). -/
  surchargeRoom : Q' → Prop

/-- E_max(a) rows, W ≥ 8: 1.21e−3 (a = 0.02), 4.56e−3 (a = 0.05), best 7.87e−3 (a = 0.1075). -/
def EmaxA002 : Q' := Q'.mkPos 121 100000 (by decide)
def EmaxA005 : Q' := Q'.mkPos 456 100000 (by decide)
def EmaxBest : Q' := Q'.mkPos 787 100000 (by decide)
def aEmaxBest : Q' := Q'.mkPos 1075 10000 (by decide)

/-- Chain II bundle (W ≥ 8, bracket A, threshold `thrChainII = 0.5730`,
witnessed 0.5729).  Statuses: II.1 = `Z2CertTable` [CERT-NUM]; II.2 [PROVED-AUD];
II.3 [PROVED-AUD]; II.4 [PROVED-AUD]; II.5 [CONJ]; II.6 [CONJ]; B16 [PROVED-AUD]. -/
structure ChainIIHyps (D : ChainIIData) : Prop where
  z2 : Z2CertTable G
  resolution : D.resolutionTheoremC
  treeKP_A : D.treeKP_A
  sheetAsZ2Cycle : D.sheetAsZ2Cycle
  junctionExcess_OPEN : D.junctionExcess aEmaxBest EmaxBest
  spinGeOneFits_OPEN : D.spinGeOneFits
  surchargeA : D.surchargeRoom kappaMaxA
  surchargeB : D.surchargeRoom kappaMaxB

/-- Uninterpreted statements for Chain III (parity route). -/
structure ChainIIIData where
  closedSetCounts : Prop
  /-- `parityTail μ`: parity encoding rate μ_par ≤ μ. -/
  parityTail : Q' → Prop
  kpFactor6 : Prop
  p1pp : Prop

def muPar : Q' := Q'.mkPos 7012 1000 (by decide)
def aChainIII : Q' := Q'.mkPos 665 10000 (by decide)

/-- Chain III bundle (scope W ≥ 8 per ledger reading; threshold
`thrChainIII = 0.4380`, a = 0.0665).  III.1 [PROVED-AUD to n = 12; n = 14 count
1316 not independently verified]; III.2 [PROVED-SELF]; III.3 [PROVED-AUD];
III.4 P1″ [CONJ].  Note `step2_above_U1`: 14/25 > 0.4380, so Chain III does not
reach step 2 even if P1″ holds. -/
structure ChainIIIHyps (D : ChainIIIData) : Prop where
  closedSetCounts : D.closedSetCounts
  parityTail : D.parityTail muPar
  kpFactor6 : D.kpFactor6
  p1pp_OPEN : D.p1pp

end YMGap.RG.Step2Conditional

#print axioms YMGap.RG.Step2Conditional.hfine_step2_of_small_and_ge8
#print axioms YMGap.RG.Step2Conditional.wStep2_eqv
#print axioms YMGap.RG.Step2Conditional.uStep2_eqv
#print axioms YMGap.RG.Step2Conditional.cubeCap_eqv
#print axioms YMGap.RG.Step2Conditional.RB7_sixth_ge_five
#print axioms YMGap.RG.Step2Conditional.step2_above_U1
#print axioms YMGap.RG.Step2Conditional.step2_below_conditional
#print axioms YMGap.RG.Step2Conditional.certG_tree
#print axioms YMGap.RG.Step2Conditional.certG_exp
#print axioms YMGap.RG.Step2Conditional.certG_act
#print axioms YMGap.RG.Step2Conditional.certG_radius
#print axioms YMGap.RG.Step2Conditional.certG_cube
#print axioms YMGap.RG.Step2Conditional.certG_sheet
#print axioms YMGap.RG.Step2Conditional.etaRestClosing_lt_spec
#print axioms YMGap.RG.Step2Conditional.hfine_step2_ge8_of_chainI_Gsplit
#print axioms YMGap.RG.Step2Conditional.certI_tree
#print axioms YMGap.RG.Step2Conditional.certI_exp
#print axioms YMGap.RG.Step2Conditional.certI_sheet
#print axioms YMGap.RG.Step2Conditional.hfine_step2_ge8_of_chainI_H2cluster
