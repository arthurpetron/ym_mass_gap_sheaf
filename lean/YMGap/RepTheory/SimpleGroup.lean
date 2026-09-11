/-
Legacy scalar admissibility certificates for the uniform σ̂-budget reduction.

# Why this module exists

`RepTheory/RepData.lean` already parametrizes the σ̂-budget closure by a
handful of scalar invariants (`C₂_fund`, `C₂_adj = h^∨`, `g²`, …) and
proves the *conditional* closure `RepData.budget_closes`.  This file adds two
numeric lower-bound hypotheses on those stored scalars.  It does **not**
construct a compact simple group, identify `R.C2_fund` with the least nonzero
Casimir of that group, derive descent through a global form, or prove that a
chosen faithful action is irreducible.  In particular, the historical name
`AdmissibleSimpleGroup` denotes only a scalar certificate, not provenance from
an actual group.

The rational floor `3/4` is the desired universal lower bound for the eventual
global-form spectral minimum, and `2` is the dual-Coxeter floor.  Their general
representation-theoretic justification is still owed by the constructive
root/weight, central-character, and highest-weight development.  A defining
representation need not minimize the Casimir (already for simply connected
`B₂` and `B₃`), and quotient global forms can reject cover representations.

# What this module proves

  * `AdmissibleSimpleGroup` — the structure carrying the two lower bounds
    `gap_lb : (3/4 : Q') ≤ R.C2_fund` and `hvee_lb : (2 : Q') ≤ R.C2_adj`,
    plus the certificate the group already owns (`RepData.ClosureCertificate`).
  * `Casimir.gapFloor = 3/4`, `Casimir.hveeFloor = 2` — exact target floors.
  * `su2_admissible` — SU(2) **saturates** both bounds (`3/4 ≤ 3/4`,
    `2 ≤ 2`, by `decide`); it is the scalar boundary instance.
  * `su3_admissible` — the SU(3) scalar record has strict slack
    (`3/4 ≤ 4/3`, `2 ≤ 3`) for the stored SU(3) scalars.
  * `suN_gap_lb` / `suN_hvee_lb` — the `SU(N)` family (`N ≥ 2`) satisfies
    both numerical bounds.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing fact is a `Q'`-rational `decide` or an explicit `Q'`
order proof, reporting empty or `[propext]`.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.RepTheory.RepData

namespace YMGap.RepTheory

open YMGap.Constructive

/-! ## Exact target floors -/

namespace Casimir

/-- Exact rational floor used by the legacy scalar budget interface.  The
future global-form highest-weight development must prove that the actual least
nonzero descended Casimir is at least this value. -/
def gapFloor : Q' := Q'.mkPos 3 4 (by decide)

/-- Exact rational dual-Coxeter floor used by the scalar budget interface. -/
def hveeFloor : Q' := Q'.ofNat 2

/-- `0 < gapFloor`. -/
theorem gapFloor_pos : (0 : Q') < gapFloor := by decide

/-- `0 < hveeFloor`. -/
theorem hveeFloor_pos : (0 : Q') < hveeFloor := by decide

end Casimir

/-! ## The admissibility interface

Despite its historical name, `AdmissibleSimpleGroup R` does not assert that
`R` comes from a compact simple gauge group.  It carries two scalar lower
bounds together with the closure certificate `R` already owes.  The reduction
(`MassGap/SimpleGroup.lean`) uses `gap_lb` in one character-tail input adapter,
exposes `cert` through a separate accessor, and does not currently use
`hvee_lb` in its main budget theorem.  The base budget route is driven by the
separate `UniformBudgetWitness`; this structure records scalar obligations for
later representation-theoretic closure rather than claiming they are all
load-bearing today. -/
structure AdmissibleSimpleGroup (R : RepData) : Prop where
  /-- Lower bound `3/4 ≤ R.C2_fund` on the stored legacy scalar. -/
  gap_lb  : Casimir.gapFloor ≤ R.C2_fund
  /-- Lower bound `2 ≤ R.C2_adj` on the stored adjoint scalar. -/
  hvee_lb : Casimir.hveeFloor ≤ R.C2_adj
  /-- The group's own σ̂-budget closure certificate (Bałaban tie + the
  per-step budget); see `RepData.ClosureCertificate`. -/
  cert    : R.ClosureCertificate

/-! ## SU(2): the scalar boundary instance

The stored SU(2) invariants sit exactly on the two floors,
`C₂_fund = 3/4 = gapFloor` and
`C₂_adj = 2 = hveeFloor`.  Both bounds hold with equality (`decide`),
which is the complete formal content of this section. -/

/-- SU(2) saturates the gap floor: `3/4 ≤ 3/4`. -/
theorem su2_gap_lb : Casimir.gapFloor ≤ su2.C2_fund := by decide

/-- SU(2) saturates the dual-Coxeter floor: `2 ≤ 2`. -/
theorem su2_hvee_lb : Casimir.hveeFloor ≤ su2.C2_adj := by decide

/-- The stored SU(2) scalar record satisfies both bounds with equality, and
`su2_cert` supplies its conditional closure certificate. -/
theorem su2_admissible : AdmissibleSimpleGroup su2 where
  gap_lb  := su2_gap_lb
  hvee_lb := su2_hvee_lb
  cert    := su2_cert

/-! ## SU(3): an interior instance (strict slack) -/

/-- SU(3) clears the gap floor with slack: `3/4 ≤ 4/3`. -/
theorem su3_gap_lb : Casimir.gapFloor ≤ su3.C2_fund := by decide

/-- SU(3) clears the dual-Coxeter floor with slack: `2 ≤ 3`. -/
theorem su3_hvee_lb : Casimir.hveeFloor ≤ su3.C2_adj := by decide

/-- The stored SU(3) scalar record satisfies the legacy admissibility structure,
with strict slack in both recorded invariants. -/
theorem su3_admissible : AdmissibleSimpleGroup su3 where
  gap_lb  := su3_gap_lb
  hvee_lb := su3_hvee_lb
  cert    := su3_cert

/-! ## The `A_{N-1} = SU(N)` family clears both floors for `N ≥ 2`

The chosen `SU(N)` scalar formulas (`C₂_fund = (N²−1)/(2N)`, `C₂_adj = N`)
satisfy both lower bounds for every `N ≥ 2`, so every group in the
`A` family clears these numerical tests (modulo its own closure certificate).
We prove
the two bounds at the level of the `suN_C2_fund`/`suN_C2_adj` formulas,
without claiming the global-form spectral minimum. -/

/-- `C₂_adj = N ≥ 2` for `SU(N)` with `N ≥ 2`: the dual-Coxeter floor.
`hveeFloor = 2 = ofNat 2 ≤ ofNat N`, monotone in `N`. -/
theorem suN_hvee_lb (N : Nat) (hN : 2 ≤ N) :
    Casimir.hveeFloor ≤ suN_C2_adj N := by
  show (Q'.ofNat 2).le (Q'.ofNat N)
  show (Q'.ofNat 2).num * ((Q'.ofNat N).den : Int)
     ≤ (Q'.ofNat N).num * ((Q'.ofNat 2).den : Int)
  -- (ofNat n).num = Int.ofNat n, (ofNat n).den = 1, so goal: Int.ofNat 2 * 1 ≤ Int.ofNat N * 1.
  have h2 : (Q'.ofNat 2).num = (2 : Int) := rfl
  have hN' : (Q'.ofNat N).num = (N : Int) := rfl
  have hd2 : ((Q'.ofNat 2).den : Int) = 1 := rfl
  have hdN : ((Q'.ofNat N).den : Int) = 1 := rfl
  rw [h2, hN', hd2, hdN]
  -- Goal: 2 * 1 ≤ (N:Int) * 1
  have : (2 : Int) ≤ (N : Int) := by omega
  omega

/-- `C₂_fund = (N²−1)/(2N) ≥ 3/4` for `SU(N)` with `N ≥ 2`: the gap
floor.  Cross-multiplied: `4·(N²−1) ≥ 3·(2N)` i.e. `4N²−4 ≥ 6N`, i.e.
`4N²−6N−4 ≥ 0`, true for `N ≥ 2`. -/
theorem suN_gap_lb (N : Nat) (hN : 2 ≤ N) :
    Casimir.gapFloor ≤ suN_C2_fund N (by omega) := by
  -- Unfold to the cross-product Int inequality `p.num·q.den ≤ q.num·p.den`.
  show (Casimir.gapFloor).num * ((suN_C2_fund N (by omega)).den : Int)
     ≤ (suN_C2_fund N (by omega)).num * ((Casimir.gapFloor).den : Int)
  -- Reduce each `.num`/`.den` via the `mkPos` projections.
  have hgn : (Casimir.gapFloor).num = (3 : Int) := rfl
  have hgd : ((Casimir.gapFloor).den : Int) = (4 : Int) := rfl
  have hfn : (suN_C2_fund N (by omega)).num = (N : Int) * (N : Int) - 1 := rfl
  have hfd : ((suN_C2_fund N (by omega)).den : Int) = ((2 * N : Nat) : Int) :=
    by rw [suN_C2_fund, Q'.mkPos_den (h := by omega)]
  rw [hgn, hgd, hfn, hfd]
  -- Goal: 3 * ↑(2*N) ≤ (↑N·↑N − 1) * 4.  Cast ↑(2*N) = 2·↑N.
  have hcast : (((2 * N : Nat)) : Int) = 2 * (N : Int) := by
    rw [Int.natCast_mul]; rfl
  rw [hcast]
  -- Abbreviate k := (N : Int), 2 ≤ k.
  have hk2 : (2 : Int) ≤ (N : Int) := by omega
  -- Key nonlinear step: 4 * (2*k) ≤ 4 * (k*k)  (from 2*k ≤ k*k, k ≥ 0).
  have hkk : (2 : Int) * (N : Int) ≤ (N : Int) * (N : Int) :=
    Int.mul_le_mul_of_nonneg_right hk2 (by omega)
  have h8 : (4 : Int) * (2 * (N : Int)) ≤ 4 * ((N : Int) * (N : Int)) :=
    Int.mul_le_mul_of_nonneg_left hkk (by omega)
  -- Goal `3*(2*k) ≤ (k*k - 1)*4`: with A := k*k an atom, h8 gives 8k ≤ 4A; omega closes.
  omega

end YMGap.RepTheory

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.Casimir.gapFloor_pos
#print axioms YMGap.RepTheory.Casimir.hveeFloor_pos
#print axioms YMGap.RepTheory.su2_admissible
#print axioms YMGap.RepTheory.su3_admissible
#print axioms YMGap.RepTheory.suN_hvee_lb
#print axioms YMGap.RepTheory.suN_gap_lb
