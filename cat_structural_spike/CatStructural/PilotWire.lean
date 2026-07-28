/-
CatStructural/PilotWire.lean

**Item (1), second certificate stack**: the chain wired to the
σ̂-budget-closure certificates of `YMGap.RG.SigmaHatPilot` — the
Phase-3 pilot wire-ins — complementing `StepBridge.lean`, which wires
the per-step Θ-certificates of `YMGap/RG/BlockSpin.lean`.  Between
them the two files cover both shapes the main tree's singleStep data
takes:

  · `StepBridge` : per-scale ADDITIVE S4 certificates
    (`σ̂_k − η_k ≤ σ̂_{k+1}`), each translated to a ratio morphism;
  · this file    : the GLOBAL budget certificate
    (`∀ N, Σ_{k<N} η_k ≤ η_total ≤ σ̂₀`), consumed whole as the
    uniform-gap CONE over the induced ledger `σ̂_N = σ̂₀ − Σ_{k<N} η_k`.

The pilot constants are the ACTUAL certificate numbers
(`SigmaHatPilot`, data provenance
`computations.q_lift.pilot_eta_rational_bound`, post-2026-05-26 c_λ
Casimir-gap derivation):

  * canonical (g₀ = 0.30, K = 3): η_max = 3/10000, η_total = 9/10000,
    σ̂₀ = 1;
  * Wilson (g₀ = 0.50, K = 3): η_max = 1/10000, η_total = 3/10000,
    σ̂₀ = 1;
  * η-sequence `truncated_const_3 η_max`; `finSum` with
    `finSum f (N+1) = finSum f N + f N`; stabilization past K = 3 at
    the `Eq` level via the structural `add_zero`.

All of the above is mirrored verbatim from
`YMGap.Constructive.RationalTail` / `SigmaHatPilot` (as `QSpike.lean`
mirrors `Q'`); on promotion the mirrors are deleted and the wire
consumes the originals unchanged.

What the wire produces:

  * the σ̂-ledgers as `MassG` families (`sigmaCM`, `sigmaWM`), positive
    at every scale because the pilot closure is STRICT
    (η_total < σ̂₀ by four orders of magnitude) — four kernel decides
    plus stabilization;
  * the wired chain (`pilotChainC` = `chainG` over `selfRatioStep`),
    its hom-setoid collapse to the direct `σ̂_n/σ̂₀` comparison
    (`pilotChainC_collapse`, instantiating the generic telescoping
    collapse), and its telescoped bound by projection;
  * the uniform-gap cone (`pilotGapC`) assembled by
    `UniformGapG.ofPointwise` DIRECTLY from the closure certificate —
    apex `σ̂₀ − η_total = 9991/10000`, kernel-decided positive, tight
    against the stabilized ledger (`apexC_tight`);
  * uniform positivity `∀ n, 0 < σ̂_n` through BOTH generic spines
    (cone `pos_all` and chain `gap_persistsG`), confirming they agree
    on wired data;
  * **items (1) + (2) tied together on real data**: the standing
    guard (`SquareGuard.squaresUpTo`) run on the canonical-vs-Wilson
    comparison of the two ACTUAL pilot ledgers — passing generically
    (`pilot_guard_all`, via the generic positive control) and
    kernel-decided on the audit window (`pilot_guard_window`).

Mathlib-free, Classical-free, sorry-free, kernel `decide` only.
-/

import CatStructural.QSpike
import CatStructural.LedgerWire
import CatStructural.SquareGuard

namespace CatStructural

namespace QS

/-- Mirror of `Q'.add_zero'`: `p + 0 = p` STRUCTURALLY (an `Eq`, not
    just an `eqv`) — the fact that makes `finSum` stabilization an
    `Eq`-level statement.  (The `add`/`neg`/`sub` mirrors themselves
    live in `QSpike.lean`.) -/
theorem add_zero (p : QS) : add p zero = p := by
  cases p with | mk num denPred =>
  show (⟨num * ((1 : Nat) : Int) + (0 : Int) * ((denPred + 1 : Nat) : Int),
         (denPred + 1) * 1 - 1⟩ : QS) = ⟨num, denPred⟩
  congr 1
  · simp
  · simp

end QS

/-! ## The certificate stack, mirrored: sequences, sums, stabilization -/

/-- Mirror of `RationalTail.QSeq`. -/
def QSSeq : Type := Nat → QS

/-- Mirror of `RationalTail.finSum`:
    `finSum f 0 = 0`; `finSum f (N+1) = finSum f N + f N`. -/
def finSumQS (f : QSSeq) : Nat → QS
  | 0 => QS.zero
  | n + 1 => QS.add (finSumQS f n) (f n)

/-- Mirror of `RationalTail.finSum_stabilizes_after_K`: past a zero
    tail, partial sums are constant — at the `Eq` level, via the
    structural `QS.add_zero`. -/
theorem finSumQS_stabilizes (f : QSSeq) (K : Nat)
    (h : ∀ k, K ≤ k → f k = QS.zero) :
    ∀ M, finSumQS f (K + M) = finSumQS f K
  | 0 => rfl
  | M + 1 => by
    show QS.add (finSumQS f (K + M)) (f (K + M)) = finSumQS f K
    rw [h (K + M) (Nat.le_add_right K M), QS.add_zero]
    exact finSumQS_stabilizes f K h M

/-- Mirror of `RationalTail.truncated_const_3`: the pilot η-shape —
    `η_max` for `k < 3`, zero after. -/
def truncatedConst3 (q : QS) : QSSeq
  | 0 => q
  | 1 => q
  | 2 => q
  | _ + 3 => QS.zero

theorem truncatedConst3_zero_of_ge_3 (q : QS) :
    ∀ k, 3 ≤ k → truncatedConst3 q k = QS.zero
  | _ + 3, _ => rfl

/-! ## The pilot constants — the ACTUAL certificate numbers -/

/-- η_max = 3/10000 (canonical, `SigmaHatPilot.eta_max_pilot` /
    `BudgetConstants.bcEtaMaxCanonical`). -/
def etaMaxC : QS := ⟨3, 9999⟩
/-- η_total = 9/10000 (canonical, `SigmaHatPilot.eta_total_pilot`). -/
def etaTotalC : QS := ⟨9, 9999⟩
/-- σ̂₀ = 1 (`SigmaHatPilot.sigma_hat_0_pilot`). -/
def sigmaHat0 : QS := QS.one
/-- The canonical pilot η-sequence (`SigmaHatPilot.eta_pilot`). -/
def etaC : QSSeq := truncatedConst3 etaMaxC

/-- η_max = 1/10000 (Wilson, `SigmaHatPilot.eta_max_pilot_wilson`). -/
def etaMaxW : QS := ⟨1, 9999⟩
/-- η_total = 3/10000 (Wilson, `SigmaHatPilot.eta_total_pilot_wilson`). -/
def etaTotalW : QS := ⟨3, 9999⟩
/-- The Wilson pilot η-sequence (`SigmaHatPilot.eta_pilot_wilson`). -/
def etaW : QSSeq := truncatedConst3 etaMaxW

/-! ## The σ̂-ledgers -/

/-- The canonical σ̂-ledger: `σ̂_N = σ̂₀ − Σ_{k<N} η_k`. -/
def sigmaC (n : Nat) : QS := QS.sub sigmaHat0 (finSumQS etaC n)

/-- The Wilson σ̂-ledger. -/
def sigmaW (n : Nat) : QS := QS.sub sigmaHat0 (finSumQS etaW n)

/-- Ledger stabilization: `σ̂_{3+M} = σ̂_3` (an `Eq`), inherited from
    `finSum` stabilization past the zero tail. -/
theorem sigmaC_stab (M : Nat) : sigmaC (3 + M) = sigmaC 3 := by
  show QS.sub sigmaHat0 (finSumQS etaC (3 + M)) = _
  rw [finSumQS_stabilizes etaC 3 (truncatedConst3_zero_of_ge_3 etaMaxC) M]
  rfl

theorem sigmaW_stab (M : Nat) : sigmaW (3 + M) = sigmaW 3 := by
  show QS.sub sigmaHat0 (finSumQS etaW (3 + M)) = _
  rw [finSumQS_stabilizes etaW 3 (truncatedConst3_zero_of_ge_3 etaMaxW) M]
  rfl

/-! ## Strict closure ⟹ ledger positivity (the wire's analytic input) -/

theorem sigmaC_pos : ∀ n, qSubstrate.lt qSubstrate.zero (sigmaC n)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    rw [show n + 3 = 3 + n from Nat.add_comm n 3, sigmaC_stab]
    decide

theorem sigmaW_pos : ∀ n, qSubstrate.lt qSubstrate.zero (sigmaW n)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    rw [show n + 3 = 3 + n from Nat.add_comm n 3, sigmaW_stab]
    decide

/-- The canonical σ̂-ledger as a `MassG` family — the object family of
    the wired chain. -/
def sigmaCM (n : Nat) : MassG qSubstrate :=
  ⟨sigmaC n, qSubstrate.le_of_lt (sigmaC_pos n)⟩

def sigmaWM (n : Nat) : MassG qSubstrate :=
  ⟨sigmaW n, qSubstrate.le_of_lt (sigmaW_pos n)⟩

/-! ## The wired chain -/

/-- The wired per-scale morphism family: the certificate's σ̂-ledger as
    self-ratio domination steps. -/
def pilotStepC : ∀ k, DomG (sigmaCM k) (sigmaCM (k + 1)) :=
  selfRatioStep sigmaCM sigmaC_pos

/-- The wired chain composite `σ̂₀ ⟶ σ̂_n`. -/
def pilotChainC (n : Nat) : DomG (sigmaCM 0) (sigmaCM n) :=
  chainG sigmaCM pilotStepC n

/-- **Telescoping collapse at the pilot**: the composite of the wired
    per-scale steps is hom-setoid equal to the direct `σ̂_n/σ̂₀`
    comparison — instantiation of the generic collapse, no re-proof. -/
theorem pilotChainC_collapse (n : Nat) :
    DomG.eqv (pilotChainC n) (directHom sigmaCM sigmaC_pos n) :=
  selfRatio_chain_collapse sigmaCM sigmaC_pos n

/-- The chain's telescoped bound, extracted by projection. -/
theorem pilotChainC_bound (n : Nat) :
    qSubstrate.le (QS.mul (pilotChainC n).num (sigmaC 0))
                  (QS.mul (pilotChainC n).den (sigmaC n)) :=
  chainG_bound sigmaCM pilotStepC n

/-- Composite numerators are positive: base `0 < 1`, step = ledger
    positivity times the induction hypothesis. -/
theorem pilotChainC_num_pos :
    ∀ n, qSubstrate.lt qSubstrate.zero (pilotChainC n).num
  | 0 => qSubstrate.zero_lt_one
  | n + 1 => qSubstrate.mul_pos (sigmaC_pos (n + 1)) (pilotChainC_num_pos n)

/-! ## The cone: the closure certificate IS the uniform gap -/

/-- The canonical apex: `σ̂₀ − η_total = 9991/10000`. -/
def apexC : QS := QS.sub sigmaHat0 etaTotalC

theorem apexC_le : ∀ n, qSubstrate.le apexC (sigmaC n)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    rw [show n + 3 = 3 + n from Nat.add_comm n 3, sigmaC_stab]
    decide

/-- **The wired uniform-gap cone (canonical pilot)**: assembled by
    `UniformGapG.ofPointwise` directly from the closure certificate.
    One apex object, `9991/10000`, kernel-decided positive — pinning
    is structural. -/
def pilotGapC : UniformGapG sigmaCM :=
  UniformGapG.ofPointwise ⟨apexC, by decide⟩ (by decide) apexC_le

/-- **The payoff, cone route**: uniform strict positivity of the pilot
    σ̂-ledger at every scale via `pos_all` — the categorical statement
    of "the σ̂-budget closes ⟹ the gap survives every scale", at the
    actual certificate numbers. -/
theorem pilot_gap_uniform : ∀ n, qSubstrate.lt qSubstrate.zero (sigmaC n) :=
  fun n => UniformGapG.pos_all pilotGapC n

/-- The same payoff through the chain route (`gap_persistsG`),
    confirming the two generic spines agree on the wired data. -/
theorem pilot_gap_via_chain : ∀ n, qSubstrate.lt qSubstrate.zero (sigmaC n) :=
  gap_persistsG sigmaCM pilotStepC (sigmaC_pos 0) pilotChainC_num_pos

/-! ## Items (1) + (2) tied together: the standing guard on real data

The canonical and Wilson pilots are two certificate stacks for the
same physics.  Their comparison is the guard's first REAL audit item:
ledgers from the actual certificates, canonical comparison components,
`SquareGuard.squaresUpTo` as the device. -/

/-- The canonical pilot as a guard ledger. -/
def pilotLedgerC : LedgerG qSubstrate := ⟨sigmaCM, pilotStepC⟩

/-- The Wilson pilot as a guard ledger. -/
def pilotLedgerW : LedgerG qSubstrate :=
  ⟨sigmaWM, selfRatioStep sigmaWM sigmaW_pos⟩

/-- The canonical-vs-Wilson comparison components (ratio `σ̂ᵂ_k/σ̂ᶜ_k`). -/
def pilotCmp : ∀ k, DomG (pilotLedgerC.M k) (pilotLedgerW.M k) :=
  ratioHom sigmaCM sigmaWM sigmaC_pos

/-- **The guard passes at every scale, generically**: the naturality
    squares of the canonical-vs-Wilson comparison commute for ALL `k`,
    by the generic positive control — real certificate ledgers are
    honest self-ratio presentations, so the guard's precondition is a
    theorem, not a check. -/
theorem pilot_guard_all (k : Nat) :
    SquareGuard.square pilotLedgerC pilotLedgerW pilotCmp k :=
  selfRatio_squares_commute sigmaCM sigmaWM sigmaC_pos sigmaW_pos k

/-- **The guard's kernel run on the audit window**: `squaresUpTo 4`
    covers every scale with nonzero η (the pilots stabilize past
    K = 3), decided by the kernel on the actual pilot numbers — the
    standing-audit device exercised end-to-end on real data. -/
theorem pilot_guard_window :
    SquareGuard.squaresUpTo pilotLedgerC pilotLedgerW pilotCmp 4 := by
  decide

/-! ## Concrete kernel anchors at the pilot numbers -/

/-- σ̂_3 — the canonical ledger's stabilized value — is semantically
    `9991/10000`, kernel-checked on the unnormalized representation
    (`999100000000/10¹²`). -/
theorem sigmaC_three_value : QS.eqv (sigmaC 3) ⟨9991, 9999⟩ := by decide

/-- The apex is semantically EQUAL to the stabilized ledger value:
    the cone is TIGHT at the pilot — no slack was introduced anywhere
    between the certificate and the categorical statement. -/
theorem apexC_tight : QS.eqv apexC (sigmaC 3) := by decide

#print axioms QS.add_zero
#print axioms finSumQS_stabilizes
#print axioms sigmaC_pos
#print axioms pilotChainC_collapse
#print axioms pilotChainC_bound
#print axioms pilotGapC
#print axioms pilot_gap_uniform
#print axioms pilot_gap_via_chain
#print axioms pilot_guard_all
#print axioms pilot_guard_window
#print axioms sigmaC_three_value
#print axioms apexC_tight

end CatStructural
