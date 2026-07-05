/-
Track B / local-CLT — the TWO-REGION SCAFFOLD for the upper-tail corner of R1
(`R1RegimeGE.RegimeGETailBound`), the sole remaining residual of `SaddleVarianceFloor`.

# Why this file exists (read first — load-bearing honesty)

`RegimeGETailBound w` asks for `FullRangeFloor w s` for every window `s ≥ 7` on the physical upper
half `w ∈ [1/2, 1]`.  The complete (numerically end-to-end verified, gap-free) argument
(`computations/r1_corner_closure_argument.md`, `…corner_result.md`) splits this region at the
certificate point `w = 4K/(4K+35)`, `K = s²+6s+7`, i.e. the rational condition `(1−w)/w ≤ 35/(4K)`:

  * **PARABOLIC branch** `4K ≤ (35+4K)·w`  (`w` near `1`).  The exact parabolic variance is
    `P(t) = V(t,1) = t(t+4)/5` and `Var_par(t) = 8t(t−1)(t+4)(t+5)/175`, so `Δ²Var_par(s) =
    96·K/175`.  The tilt-integral identity `Δ²e(s) = ∫₀^λ ½ Δ²Var_μ(s) dμ` (`e = P − V`,
    `λ = −ln w`) together with the finite ensemble inequality `Δ²Var_μ ≤ Δ²Var_par` (**lemma C**)
    gives `Δ²e ≤ (λ/2)·Δ²Var_par ≤ ((1−w)/2w)·96K/175`, whence `Δ²V+2 = 12/5 − Δ²e ≥ 0` exactly on
    this branch.  Zero infinite-theta content; margin `35/4`.
  * **THETA branch** `(35+4K)·w ≤ 4K`  (`w` away from `1`): the truncation is negligible and the
    exact-defect theta lower bound `LBθ ≥ 1.78 > 0` holds (plateau `2∓2ϑ₄(w²)⁴ ≥ 93/50` via the
    proved anchor `ϑ₄(1/4)⁴ ≤ 7/100`, plus a bounded, monotone-in-`m` defect and `Δ²tail ≥ 0`).

Every `(s, w)` lands in one branch (the `Q'` order is decidable), so the two branches inhabit
`RegimeGETailBound`.  This file lays that decomposition down as Type-level branch structures and
PROVES the assembly.  The two branch certificates (finite lemma C + rational algebra for parabolic;
theta-truncation for theta) are the remaining certificate-level work — named-open here, never
`sorry`.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
The two branch residuals are `Type`-level structures (Rule 6a).
-/

import YMGap.Continuum.R1RegimeGE

namespace YMGap.Continuum.R1CornerScaffold

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.R1CaseSplit

/-! ## 0. The certificate constant `K = s²+6s+7` and the rational split. -/

/-- `certK s = s²+6s+7` — the exact numerator of `Δ²Var_par(s) = 96·K/175`, and the constant in the
parabolic-certificate threshold `w = 4K/(4K+35)`. -/
def certK (s : Nat) : Nat := s * s + 6 * s + 7

/-! ## 1. The two branch obligations (split at `4K ≤ (35+4K)·w ⟺ (1−w)/w ≤ 35/4K`). -/

/-- **`ParabolicTailBranch w`** (NAMED OPEN — the `w`-near-`1` half of the corner).  For `w ∈ [1/2,1]`,
`s ≥ 7`, and `4K ≤ (35+4K)·w` (i.e. `(1−w)/w ≤ 35/4K`), the full-range floor holds.  Discharged by
the exact backbone `P(t)=t(t+4)/5`, `Δ²Var_par = 96K/175`, the tilt-integral identity, and the finite
ensemble inequality **lemma C** (`Δ²Var_μ ≤ Δ²Var_par`), giving `Δ²V+2 ≥ 12/5 − ((1−w)/2w)·96K/175 ≥ 0`. -/
structure ParabolicTailBranch (w : Q') : Type where
  parab : half ≤ w → w ≤ 1 → ∀ s, 7 ≤ s →
    Q'.ofNat (4 * certK s) ≤ Q'.ofNat (35 + 4 * certK s) * w → FullRangeFloor w s

/-- **`ThetaTailBranch w`** (NAMED OPEN — the `w`-away-from-`1` half of the corner).  For `w ∈ [1/2,1]`,
`s ≥ 7`, and `(35+4K)·w ≤ 4K` (i.e. `(1−w)/w ≥ 35/4K`), the full-range floor holds.  Discharged by the
exact-defect theta lower bound `LBθ ≥ 1.78 > 0`. -/
structure ThetaTailBranch (w : Q') : Type where
  theta : half ≤ w → w ≤ 1 → ∀ s, 7 ≤ s →
    Q'.ofNat (35 + 4 * certK s) * w ≤ Q'.ofNat (4 * certK s) → FullRangeFloor w s

/-- **`regimeGETailBound_of_branches` — THE CORNER SCAFFOLD.**  The two branches inhabit the standing
residual `R1RegimeGE.RegimeGETailBound w`.  For each `(s, w)` the DECIDABLE `Q'` dichotomy
`q_le_total` on `(35+4K)·w` vs `4K` selects the theta or parabolic branch.  Pure modus ponens —
axiom-clean. -/
def regimeGETailBound_of_branches {w : Q'}
    (P : ParabolicTailBranch w) (T : ThetaTailBranch w) : R1RegimeGE.RegimeGETailBound w where
  tail := fun hhalf hw1 s hs => by
    rcases q_le_total (Q'.ofNat (35 + 4 * certK s) * w) (Q'.ofNat (4 * certK s)) with h | h
    · exact T.theta hhalf hw1 s hs h
    · exact P.parab hhalf hw1 s hs h

/-! ## 2. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `regimeGETailBound_of_branches` — the two-region scaffold: `ParabolicTailBranch` +
    `ThetaTailBranch` inhabit `RegimeGETailBound` by the decidable rational split at `w = 4K/(4K+35)`.

NAMED OPEN (Type-level structures, never `sorry`):
  * `ParabolicTailBranch w` — `w` near `1` (`4K ≤ (35+4K)w`), via the exact parabolic backbone
    `P(t)=t(t+4)/5`, the tilt-integral identity, and the finite ensemble inequality lemma C
    (`Δ²Var_μ ≤ Δ²Var_par`).  Certificate margin `35/4`.
  * `ThetaTailBranch w` — `w` away from `1` (`(35+4K)w ≤ 4K`), via the exact-defect theta lower bound
    `LBθ ≥ 1.78` (plateau `≥ 93/50` on the proved `ϑ₄(1/4)⁴ ≤ 7/100`).

The complete gap-free argument (both branches verified end-to-end, floor `1.8226`) is in
`computations/r1_corner_closure_argument.md` and `…corner_result.md`.
-/

end YMGap.Continuum.R1CornerScaffold

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1CornerScaffold.regimeGETailBound_of_branches
