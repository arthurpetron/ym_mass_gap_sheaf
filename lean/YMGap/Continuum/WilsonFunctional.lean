/-
Track B / E1 — the real single-edge SU(2) heat-kernel Wilson functional,
via character orthogonality.

The heat-kernel measure on one edge, `dμ_t(g) = K_t(g) dg` with
`K_t(g) = Σ_λ dim(λ)·χ_λ(g)·e^{−t·C₂(λ)}`, is a genuine probability
measure on `SU(2)` (the only rep contributing to `∫K_t` is the trivial one,
so `∫K_t = 1`).  By Peter–Weyl / character orthogonality
(`∫ χ_μ χ_λ dg = δ_{μλ}` for the self-conjugate SU(2) reps) the
gauge-invariant character expectations are

    ⟨χ_{s/2}⟩_t = ∫ χ_{s/2}(g) K_t(g) dg = dim(s)·e^{−t·C₂(s)},

with `dim(s) = s+1` and `C₂(s) = s(s+2)/4` (`RepTheory.SU2`).  This is the
*actual* Wilson measure's character moments — a genuine first piece of the
continuum-existence construction (`docs/track-b-continuum-plan.md` E1),
reusing the A1 exponential (`expNeg`) and the SU(2) Casimir.  It replaces
the trivial functional `ObservableMeasure.trivFunc` with real
finite-volume (single-edge) heat-kernel expectations.

# What is genuine here

  * `wilsonCharExp t s = dim(s)·e^{−t·C₂(s)}` — the heat-kernel expectation
    of the spin-`s/2` character (`CReal`), the moment `⟨χ⟩_t`.
  * `wilsonCharExp_nonneg` — each character moment is `≥ 0`.
  * `wilsonCharExp_unit` — `⟨χ_{triv}⟩_t = ⟨1⟩ = 1`: the measure is
    NORMALIZED (the genuine probability condition).

# What remains (the analytic completion of E1)

  * Full positivity `0 ≤ E(a*·a)` for a general observable `a = Σ c_μ χ_μ`
    — the positive-definiteness of the heat-kernel measure (a Gram-matrix
    condition in the character basis).  This upgrades `wilsonCharExp` to a
    full `ProbFunctional` and is the next E1 sub-step; the heat kernel IS a
    positive measure, so it holds, but proving it from the character data is
    genuine work.
  * The plaquette-coupled finite lattice (E1 → E2) and the
    infinite-volume / RG-consistent family (E2, E3) — see the roadmap.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.RepTheory.SU2
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.WilsonFunctional

open YMGap.Constructive
open YMGap.RepTheory

/-- `C₂(s) = s(s+2)/4` for SU(2) spin-`s/2`, as a `Q'`. -/
def casimirQ (s : Nat) : Q' := Q'.mkPos (SU2.fourTimesCasimir s : Int) 4 (by decide)

theorem casimirQ_nonneg (s : Nat) : (0 : Q') ≤ casimirQ s := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

theorem tcasimirQ_nonneg (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    (0 : Q') ≤ t * casimirQ s :=
  Q'.mul_nonneg t (casimirQ s) ht (casimirQ_nonneg s)

/-- **The single-edge heat-kernel Wilson character expectation**
`⟨χ_{s/2}⟩_t = dim(s)·e^{−t·C₂(s)}` — the genuine moment of the SU(2)
heat-kernel measure (`CReal`). -/
def wilsonCharExp (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.ofNat (SU2.dimension s)))
    (ExpNeg.expNeg (t * casimirQ s) (tcasimirQ_nonneg t ht s))

/-- Each character moment is `≥ 0` (`dim ≥ 0`, `e^{−·} ≥ 0`). -/
theorem wilsonCharExp_nonneg (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    ExpPos.geRat (wilsonCharExp t ht s) 0 := by
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := Q'.ofNat (SU2.dimension s))
      (SU3CharFactor.ofNat_nonneg _) (expNeg_geRat_zero _ _)) ?_
  -- 0 ≤ dim · 0
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-! ## Normalization: `⟨1⟩ = 1` (the probability condition)

At the trivial rep `s = 0`: `dim 0 = 1`, `C₂(0) = 0`, `e^{0} = 1`, so the
unit observable has expectation `1`.  We prove `e^{−t·C₂(0)} ≃ e^{0}` via
`expNeg_eqv_congr` (since `t·C₂(0) ≃ 0`), then `1·e^{0} ≃ 1` by the
scalar-mul bounds. -/

theorem tcasimir_zero_eqv (t : Q') : (t * casimirQ 0).eqv 0 := by
  show t.num * 0 * ((0 : Q').den : Int) = 0 * ((t * casimirQ 0).den : Int)
  omega

/-- `⟨1⟩_t ≤ 1`. -/
theorem wilsonCharExp_unit_le (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonCharExp t ht 0) 1 := by
  refine CReal.leRat_mono
    (CReal.leRat_smul_nonneg (c := Q'.ofNat (SU2.dimension 0)) (by decide)
      (SU3CharFactor.expNeg_le_one (t * casimirQ 0) (tcasimirQ_nonneg t ht 0))) ?_
  decide

/-- `⟨1⟩_t ≥ 1`. -/
theorem wilsonCharExp_unit_ge (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (wilsonCharExp t ht 0) 1 := by
  have hge0 : ExpPos.geRat (ExpNeg.expNeg (t * casimirQ 0) (tcasimirQ_nonneg t ht 0)) 1 :=
    SU3CharFactor.geRat_of_equiv
      (expNeg_eqv_congr (tcasimirQ_nonneg t ht 0) (by decide) (tcasimir_zero_eqv t))
      SU3CharFactor.geRat_expNeg_zero
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := Q'.ofNat (SU2.dimension 0)) (by decide) hge0) ?_
  decide

/-- **Normalization** `⟨1⟩_t = 1`: the single-edge heat-kernel measure is a
probability measure (`⟨χ_{triv}⟩ = 1`, both bounds). -/
theorem wilsonCharExp_unit (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonCharExp t ht 0) 1 ∧ ExpPos.geRat (wilsonCharExp t ht 0) 1 :=
  ⟨wilsonCharExp_unit_le t ht, wilsonCharExp_unit_ge t ht⟩

end YMGap.Continuum.WilsonFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonFunctional.wilsonCharExp_nonneg
#print axioms YMGap.Continuum.WilsonFunctional.wilsonCharExp_unit
