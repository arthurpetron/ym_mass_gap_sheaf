/-
`FusedChannelAll` — Milestone 14.1, second deliverable: EVERY fused channel
DERIVED — `FusedDominatedByHK N s` inhabited for ALL `s` and ALL truncations
`N`, with exact rational amplitudes and the valid exponent `s`.

# The exponent choice (honest sharpness ledger)

The certificate pipeline needs a VALID exponent, not the sharp one: any
`n` with `n ≤ C₄(a) + C₄(b)` for every fusing pair licenses the domination
`boxSum w N s ≤ fusedAmp(N,s)·wⁿ`.  Here we use `n := s`, valid for EVERY
channel because the fusion ladder forces `a + b ≥ s` and the Casimir
dominates the spin (`C₄(x) = x(x+2) ≥ x`), so
`C₄(a) + C₄(b) ≥ a + b ≥ s`.  The SHARP exponent is the balanced-pair
minimum `C₄(⌈s/2⌉) + C₄(⌊s/2⌋)` (for `s = 1` it is `3`, proved in
`FusedChannelOne`); upgrading the remaining channels to their sharp
exponents is the named sharpness item — it improves DECAY QUALITY, not
validity, and the 14.2 budget arithmetic will dictate where sharpness is
actually needed.

# What is delivered (all PROVED, axiom-clean)

  * `c4_ge_self` / `fusionOK_exp_ge` — the valid-exponent lemma: every
    pair fusing to `s` carries `C₄(a) + C₄(b) ≥ s`;
  * `fusedAmp` — the derived amplitude for EVERY channel: the exact double
    character sum `Σ_{a,b≤N} 1[s ∈ a⊗b]·dimQ a·dimQ b` (computable
    rational; no measured number);
  * `pair_term_le_s` / **`boxSum_le_fused`** — the channel bound
    `boxSum w N s ≤ fusedAmp N s · wˢ` on `w ∈ [0,1]`, every `N`, every `s`;
  * **`fusedDominated_all`** — `FusedDominatedByHK N s` INHABITED with
    derived data for EVERY channel — Milestone 14.1's checkable predicate
    discharged at the valid-exponent level.

# What remains open (AGENTS.md Rule 6)

Sharp exponents per channel (balanced-pair convexity — a Nat inequality
upgrade); then 14.2: the defect identity connecting these derived channel
bounds (minus the free counterterms) to `TMDefectCertificateOS.dominate`,
where the `Σ ≤ 6` budget is checked against DERIVED amplitudes — the first
place the construction can close or produce a bankable refutation.  No
frontier type is touched; the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedChannelOne

namespace YMGap.Continuum.FusedChannelAll

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedChannelOne

/-! ## 1. The valid-exponent lemma -/

/-- The Casimir dominates the spin: `x ≤ C₄(x)`. -/
theorem c4_ge_self (x : Nat) : x ≤ c4 x := by
  show x ≤ x * (x + 2)
  calc x = x * 1 := (Nat.mul_one x).symm
    _ ≤ x * (x + 2) := Nat.mul_le_mul_left x (by omega)

/-- **Every pair fusing to `s` carries exponent `≥ s`:** the ladder forces
`a + b ≥ s`, and `C₄(a) + C₄(b) ≥ a + b`. -/
theorem fusionOK_exp_ge {a b s : Nat} (h : fusionOK a b s = true) :
    s ≤ c4 a + c4 b := by
  obtain ⟨k, _, _, he⟩ := (fusionOK_iff_ladder a b s).mp h
  have hab : s ≤ a + b := by omega
  have ha := c4_ge_self a
  have hb := c4_ge_self b
  omega

/-! ## 2. The derived amplitude for every channel -/

/-- **The DERIVED amplitude** for channel `s`: the exact double character
sum `Σ_{a,b≤N} 1[s ∈ a⊗b]·dimQ a·dimQ b`. -/
def fusedAmp (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    fusionInd a b s * (dimQ a * dimQ b)) (N + 1)) (N + 1)

theorem fusedAmp_nonneg (N s : Nat) : (0 : Q') ≤ fusedAmp N s :=
  fsum_nonneg
    (fun a => fsum_nonneg
      (fun b => Q'.mul_nonneg _ _ (fusionInd_nonneg a b s)
        (Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b)))
      (N + 1))
    (N + 1)

/-! ## 3. The per-pair bound and the channel theorem -/

/-- The per-pair bound at the valid exponent `s`. -/
theorem pair_term_le_s {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (a b s : Nat) :
    fusionInd a b s * (coeffW w a * coeffW w b)
      ≤ (fusionInd a b s * (dimQ a * dimQ b)) * qpow w s := by
  by_cases h : fusionOK a b s = true
  · have hind : fusionInd a b s = (1 : Q') := by
      unfold fusionInd
      rw [h]
      rfl
    rw [hind]
    have hexp := fusionOK_exp_ge h
    have hcw : (coeffW w a * coeffW w b).eqv
        ((dimQ a * dimQ b) * qpow w (c4 a + c4 b)) := by
      show ((dimQ a * qpow w (c4 a)) * (dimQ b * qpow w (c4 b))).eqv
        ((dimQ a * dimQ b) * qpow w (c4 a + c4 b))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (dimQ a) (qpow w (c4 a))
          (dimQ b * qpow w (c4 b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (YMGap.Continuum.TaylorModel.mul_swap' (qpow w (c4 a)) (dimQ b)
            (qpow w (c4 b)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ a) (dimQ b)
          (qpow w (c4 a) * qpow w (c4 b)))) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (qpow_add' w (c4 a) (c4 b)))
    have hdims : (0 : Q') ≤ dimQ a * dimQ b :=
      Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b)
    have hbound : (dimQ a * dimQ b) * qpow w (c4 a + c4 b)
        ≤ (dimQ a * dimQ b) * qpow w s :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (qpow_exp_antitone hw0 hw1 hexp) hdims
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w a * coeffW w b))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcw) ?_
    refine Q'.le_trans' _ _ _ hbound ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv (dimQ a * dimQ b)))
      (qpow_nonneg _ hw0 s)
  · have hind : fusionInd a b s = (0 : Q') := by
      unfold fusionInd
      rw [if_neg (fun hh => h hh)]
    rw [hind]
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv (coeffW w a * coeffW w b))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_refl' 0) ?_
    exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.zero_mul_eqv (dimQ a * dimQ b)))
      (Q'.zero_mul_eqv (qpow w s)))

/-- **`boxSum_le_fused` (PROVED — every channel derived).**
`boxSum w N s ≤ fusedAmp N s · wˢ` for every `w ∈ [0, 1]`, every truncation
`N`, every channel `s`. -/
theorem boxSum_le_fused {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N s : Nat) : boxSum w N s ≤ fusedAmp N s * qpow w s := by
  unfold boxSum
  have hterm : fsum (fun a => fsum (fun b =>
      fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)
      ≤ fsum (fun a => fsum (fun b =>
        (fusionInd a b s * (dimQ a * dimQ b)) * qpow w s) (N + 1)) (N + 1) :=
    fsum_le_fsum'
      (fun a => fsum_le_fsum'
        (fun b => pair_term_le_s hw0 hw1 a b s) (N + 1)) (N + 1)
  refine Q'.le_trans' _ _ _ hterm ?_
  have hfac : (fsum (fun a => fsum (fun b =>
      (fusionInd a b s * (dimQ a * dimQ b)) * qpow w s) (N + 1)) (N + 1)).eqv
      (fusedAmp N s * qpow w s) := by
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr'
        (fun a => fsum_factor
          (fun b => fusionInd a b s * (dimQ a * dimQ b))
          (qpow w s) (N + 1))
        (N + 1)) ?_
    exact fsum_factor
      (fun a => fsum (fun b =>
        fusionInd a b s * (dimQ a * dimQ b)) (N + 1))
      (qpow w s) (N + 1)
  exact Q'.le_of_eqv hfac

/-! ## 4. THE MILESTONE PREDICATE: all channels inhabited -/

/-- **`fusedDominated_all` (PROVED — Milestone 14.1's predicate at the
valid-exponent level).**  `FusedDominatedByHK N s` inhabited with derived
data for EVERY truncation `N` and EVERY channel `s`. -/
def fusedDominated_all (N s : Nat) : FusedDominatedByHK N s where
  amp := fusedAmp N s
  expn := s
  amp_nonneg := fusedAmp_nonneg N s
  dominates := fun u hu0 hu1 =>
    boxSum_le_fused
      (YMGap.Continuum.HeatKernelChannelTM.one_sub_nonneg hu1)
      (YMGap.Continuum.HeatKernelChannelTM.one_sub_le_one hu0) N s

end YMGap.Continuum.FusedChannelAll

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedChannelAll.c4_ge_self
#print axioms YMGap.Continuum.FusedChannelAll.fusionOK_exp_ge
#print axioms YMGap.Continuum.FusedChannelAll.fusedAmp_nonneg
#print axioms YMGap.Continuum.FusedChannelAll.pair_term_le_s
#print axioms YMGap.Continuum.FusedChannelAll.boxSum_le_fused
#print axioms YMGap.Continuum.FusedChannelAll.fusedDominated_all
