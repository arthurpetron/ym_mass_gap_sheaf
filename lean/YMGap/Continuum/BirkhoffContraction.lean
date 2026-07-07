/-
Track B / R2 — THE BIRKHOFF / HILBERT-METRIC CONTRACTION OF THE POSITIVE
MULTI-REP TRANSFER, and its verdict on `SingleStepDefectBound.singleStep`.

# What this module does (read first)

A fresh tool on the sole open per-scale input of the continuum construction,
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`
(`realδ_k ≤ δ_model(w_k)`), viewed through the **Birkhoff / Hilbert projective
metric** of the positive character transfer operator.

## The setup (Birkhoff–Perron–Frobenius)

The SU(2) heat-kernel transfer operator (convolution by the class function
`K_w(θ) = Σ_s (s+1)·w^{s(s+2)}·χ_s(θ)`, `coeffW w s = dimQ s · qpow w (c4 s) > 0`)
is a POSITIVE operator on its natural cone.  Birkhoff's theorem: a positive linear
map contracts the Hilbert projective metric with ratio

    κ(T) = tanh(Δ(T)/4),   Δ(T) = sup log( T_{ik} T_{jl} / (T_{il} T_{jk}) )

(the projective diameter), and this κ is an **upper bound for the sub-leading /
leading eigenvalue ratio** `|λ_2|/λ_1`.  Here the Perron (vacuum) eigenvalue is
`λ_0 = coeffW w 0 = 1` and the sub-leading (first-excited) transfer eigenvalue over
it is the convolution ratio

    ρ_step(w) = λ_1 / λ_0 = w^{c4(1)} = w^3 = `heatKernelSep w`,

the exact spectral gap ratio the Birkhoff contraction bounds.  (The character-basis
excited/vacuum ratio is `coeffW w 1 / coeffW w 0 = 2·w^3`; the gap indicator used by
the rest of the codebase is `2 − 2w^3`, `= 2·(1 − ρ_step)·(1+w+w^2)/… ≈ 6(1−w)`.)

## The DECISIVE computation (off-line, mpmath dps≥40 + sympy exact — see birkhoff.md)

At the continuum end `w → 1` the transfer kernel `K_w → δ_e` (the modes decouple),
so the projective **diameter DIVERGES**:

    Δ(T) ~ C/(1 − w),   C ≈ 4.77 → π²/2 ≈ 4.93   (antipodal short-time asymptotic),

hence `κ = tanh(Δ/4) → 1` super-exponentially, `1 − κ ~ 2·exp(−C/(2(1−w)))`.  The
naive/geometric Birkhoff contraction FAILS (κ → 1) at `w → 1`.  Worse: the EXACT
spectral ratio `ρ_step = w^3` — which κ upper-bounds and which is INVARIANT under any
positive-diagonal (weighted / physical-metric) conjugation `T ↦ D⁻¹TD` (eigenvalues
are similarity-invariant) — ALSO tends to `1`:

    (1 − w) ≤ 1 − ρ_step(w) = 1 − w^3 ≤ 3·(1 − w)     (PROVED below, the sandwich).

So the per-step Birkhoff gap indicator `1 − ρ_step` is `Θ(1 − w) → 0`.  Because the
spectral ratio itself → 1, **NO weighted/physical Birkhoff can restore uniform
contraction**: the best contraction rate over ALL cone metrics is `≥ |λ_2|/λ_1 =
ρ_step → 1`.  This is not a defect of the tool — it is the correct statement that the
LATTICE gap per step vanishes (dimensional transmutation): `m_lat·a = −log(w^3) =
3(1−w)+O((1−w)²) → 0`.

## The VERDICT — κ → 1 at w → 1 is EXACTLY `singleStep`, not the mass gap

The Birkhoff per-step contraction is provably NON-UNIFORM (`birkhoff_floor_refuted`:
any purported uniform floor `κ₀ < 1` is refuted the moment the AF trajectory gets
close enough to `1`, which it always does).  The surviving content is the COMPOSED &
RESCALED rate over the whole RG recursion — `κ_step^{1/a} = (1 − a·m_phys)^{1/a} →
e^{−m_phys}` — whose positivity uniformly in `a` is the physical mass gap.  In
per-step form this composition-with-rescaling is verbatim
`SingleStepDefectBound.singleStep`.  The Birkhoff route therefore **reduces to** — it
does not close — `singleStep` (`fullFloor_of_birkhoffTransfer`).

This is a THIRD independent per-step tool (after the MK free-energy variational bound
and the uniform-in-m parallel-fusion bound) that confirms the same wall, now with a
sharp IMPOSSIBILITY: the eigenvalue ratio any Birkhoff/weighted contraction bounds
already tends to 1.  `BirkhoffGapDefectTransfer` (= `SingleStepDefectBound`) is
UNINHABITED.  NO 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` reusing the PROVED `oneSub_qpow_le` (geometric per-term bound),
`qpow_succ_le_self`, and `heatKernelSep_lt_one`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no `ring`.  The lone `noncomputable`
(`fullFloor_of_birkhoffTransfer`) is a re-export of the upstream constructive
Σ-projection extraction (`fullFloor_of_singleStep`).
-/

import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.BirkhoffContraction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport

/-! ## 1. The spectral gap ratio the Birkhoff contraction bounds -/

/-- **`birkhoffSpectralRatio w = w^3` — the sub-leading/leading transfer eigenvalue
ratio `ρ_step = λ_1/λ_0` that the Birkhoff contraction `κ = tanh(Δ/4)` upper-bounds
and that every positive-diagonal (weighted / physical-metric) conjugation leaves
invariant.**  It is exactly `heatKernelSep w` (`= qpow w (c4 1) = w^3`). -/
def birkhoffSpectralRatio (w : Q') : Q' := heatKernelSep w

theorem birkhoffSpectralRatio_eq (w : Q') :
    birkhoffSpectralRatio w = qpow w 3 := rfl

/-! ## 2. THE SANDWICH — the per-step Birkhoff gap indicator is `Θ(1 − w) → 0` -/

/-- **Upper half of the sandwich:** `1 − ρ_step(w) ≤ 3·(1 − w)` on `[0,1]`.  The
per-step Birkhoff gap indicator vanishes AT MOST linearly in the margin — so at the
continuum end `w → 1` it → 0 and the contraction ratio `κ ≥ ρ_step → 1`.  Reuses the
PROVED geometric per-term bound `oneSub_qpow_le` at exponent `c4(1) = 3`. -/
theorem birkhoffGap_upper {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - birkhoffSpectralRatio w ≤ Q'.ofNat 3 * ((1 : Q') - w) := by
  show (1 : Q') - qpow w 3 ≤ Q'.ofNat 3 * ((1 : Q') - w)
  exact HeatKernelRGStep.oneSub_qpow_le hw0 hw1 3

/-- **Lower half of the sandwich:** `(1 − w) ≤ 1 − ρ_step(w)` on `[0,1]`.  The gap
indicator is AT LEAST linear in the margin — so it is genuinely positive for `w < 1`
and → 0 exactly as `(1 − w) → 0`: the contraction defect `1 − κ ≤ 1 − ρ_step` is
squeezed to 0 by the deep-UV trajectory, hence NOT bounded away from 0.  Reuses the
PROVED `qpow_succ_le_self` (`w^3 = w^{2+1} ≤ w`). -/
theorem birkhoffGap_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - w ≤ (1 : Q') - birkhoffSpectralRatio w := by
  have h : birkhoffSpectralRatio w ≤ w := qpow_succ_le_self hw0 hw1 2
  have hneg : -w ≤ -birkhoffSpectralRatio w := Q'.neg_le_neg h
  exact Q'.add_le_add_left 1 _ _ hneg

/-- **The ratio is `< 1` at fixed `w < 1` (a per-step gap DOES exist at strong
coupling), but only strictly — no uniform floor.**  `ρ_step(w) = w^3 < 1` for
`w < 1` (`heatKernelSep_lt_one`). -/
theorem birkhoffSpectralRatio_lt_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    birkhoffSpectralRatio w < (1 : Q') :=
  heatKernelSep_lt_one hw0 hw1

/-! ## 3. THE IMPOSSIBILITY — no uniform Birkhoff contraction floor -/

/-- `¬ (a < a)` on `Q'` (defeq to `Int.lt_irrefl`). -/
private theorem q_lt_irrefl (a : Q') : ¬ a < a := fun h => Int.lt_irrefl _ h

/-- **`birkhoff_floor_refuted` — NO uniform per-step Birkhoff contraction floor
`κ₀ < 1` survives.**  Given an AF trajectory `w : Nat → Q'` on `[0,1]` and a purported
uniform floor `κ₀` with `ρ_step(w k) ≤ κ₀` at every scale, ANY witness that the
trajectory eventually satisfies `3·(1 − w k) < 1 − κ₀` (which every genuine AF
trajectory `w k → 1` provides, since `1 − κ₀ > 0`) yields a CONTRADICTION.  So the
per-step Birkhoff / Hilbert-metric contraction is provably non-uniform: `κ → 1` at
`w → 1`.  This is the decisive statement — it holds for the EXACT spectral ratio, so
no weighted/physical cone metric can evade it (eigenvalue ratios are conjugation
invariant). -/
theorem birkhoff_floor_refuted (w : Nat → Q')
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q'))
    (κ₀ : Q')
    (conv : Σ' k : Nat, Q'.ofNat 3 * ((1 : Q') - w k) < (1 : Q') - κ₀)
    (floor : ∀ k, birkhoffSpectralRatio (w k) ≤ κ₀) : False := by
  obtain ⟨k, hk⟩ := conv
  -- upper sandwich at scale k
  have hup : (1 : Q') - birkhoffSpectralRatio (w k)
      ≤ Q'.ofNat 3 * ((1 : Q') - w k) := birkhoffGap_upper (hw0 k) (hw1 k)
  have hlt : (1 : Q') - birkhoffSpectralRatio (w k) < (1 : Q') - κ₀ :=
    Q'.lt_of_le_of_lt hup hk
  -- floor ⟹ 1 − κ₀ ≤ 1 − ρ_step(w k)
  have hfl : (1 : Q') - κ₀ ≤ (1 : Q') - birkhoffSpectralRatio (w k) := by
    have hneg : -κ₀ ≤ -birkhoffSpectralRatio (w k) := Q'.neg_le_neg (floor k)
    exact Q'.add_le_add_left 1 _ _ hneg
  exact q_lt_irrefl _ (Q'.lt_of_le_of_lt hfl hlt)

/-! ## 4. THE REDUCTION — the Birkhoff route reduces to (does not close) `singleStep` -/

/-- **`BirkhoffGapDefectTransfer := SingleStepDefectBound` (Rule 9.8 def-alias;
UNINHABITED).**  The surviving content of the Birkhoff route — the COMPOSED &
RESCALED contraction over the full RG recursion, whose per-step form is exactly the
true-margin degradation `(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`.  The
per-step Birkhoff contraction `κ → 1` (`birkhoff_floor_refuted`) is precisely this
wall; it is NOT inhabited here. -/
def BirkhoffGapDefectTransfer : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- **`fullFloor_of_birkhoffTransfer` — the whole Clay continuum floor FROM the
composed/rescaled Birkhoff transfer (conditional).**  GIVEN a
`BirkhoffGapDefectTransfer` (= `SingleStepDefectBound`), the positive uniform
continuum floor holds for the true margin.  This certifies the Birkhoff route
reduces INTO `singleStep` — it consumes exactly that one open input, nothing more. -/
noncomputable def fullFloor_of_birkhoffTransfer (S : BirkhoffGapDefectTransfer) :
    (0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat,
          (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
            ≤ S.trueMargin k :=
  SingleStepDefectReduction.fullFloor_of_singleStep S

/-- **`birkhoffVerdict` — the honest bundled verdict (Prop, no witness).**  For every
`w ∈ [0,1]`: (i) the per-step Birkhoff gap indicator is sandwiched
`(1 − w) ≤ 1 − ρ_step(w) ≤ 3(1 − w)` (so `κ → 1` as `w → 1`); (ii) `ρ_step(w) < 1`
strictly for `w < 1` (a gap exists at fixed coupling, but with NO uniform floor —
`birkhoff_floor_refuted`).  The Birkhoff contraction is therefore NON-uniform; the
mass gap is the composed/rescaled rate = `singleStep`, which remains OPEN. -/
theorem birkhoffVerdict :
    (∀ w : Q', (0 : Q') ≤ w → w ≤ (1 : Q') →
      ((1 : Q') - w ≤ (1 : Q') - birkhoffSpectralRatio w
        ∧ (1 : Q') - birkhoffSpectralRatio w ≤ Q'.ofNat 3 * ((1 : Q') - w)))
    ∧ (∀ w : Q', (0 : Q') ≤ w → w < (1 : Q') → birkhoffSpectralRatio w < (1 : Q')) :=
  ⟨fun _w hw0 hw1 => ⟨birkhoffGap_lower hw0 hw1, birkhoffGap_upper hw0 hw1⟩,
   fun _w hw0 hw1 => birkhoffSpectralRatio_lt_one hw0 hw1⟩

end YMGap.Continuum.BirkhoffContraction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BirkhoffContraction.birkhoffSpectralRatio_eq
#print axioms YMGap.Continuum.BirkhoffContraction.birkhoffGap_upper
#print axioms YMGap.Continuum.BirkhoffContraction.birkhoffGap_lower
#print axioms YMGap.Continuum.BirkhoffContraction.birkhoffSpectralRatio_lt_one
#print axioms YMGap.Continuum.BirkhoffContraction.birkhoff_floor_refuted
#print axioms YMGap.Continuum.BirkhoffContraction.fullFloor_of_birkhoffTransfer
#print axioms YMGap.Continuum.BirkhoffContraction.birkhoffVerdict
