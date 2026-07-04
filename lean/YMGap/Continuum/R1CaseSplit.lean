/-
Track B / local-CLT — the STAGE-1 case-split scaffold for R1
(`CircleFourierPowerModel.SaddleVarianceFloor w`, i.e. `∀ s, FullRangeFloor w s`).

# Why this file exists (read first — load-bearing honesty)

R1 is the `−2` position-variance curvature floor on the FULL-range Fourier-square moments:
`∀ s, FullRangeFloor w s`, equivalently `Δ²V(s) ≥ −2` where `V(t) = dmomNfull w t / acNfull w t
= ⟨D²⟩_t` is the theta-tilted variance of `D = t − 2p` under `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`.
The paper proof (memos `computations/r1_audit_report.md`, `even_centre_certificate.md`,
`phi_certificate.md`, `r1_remaining_pieces.md`) is a CASE SPLIT over (centre-parity × w-regime),
each cell carrying an explicit rational certificate.  This file lays down the decomposition as
Type-level cell structures and PROVES the comfortable (even-centre) cell in full, reducing it to a
single named centre-variance bound; the two hard cells and the centre bound are left as honest
named-open Type-level hypotheses for later stages.

## The index correspondence (established here, load-bearing)

`FullRangeFloor w s` is the cleared `Δ²V ≥ −2` with the DOUBLED (centre) term at argument `s+1`:

    2·V(s+1)·⟨…⟩  ≤  V(s)·⟨…⟩ + V(s+2)·⟨…⟩ + 2·⟨…⟩       (`V` = dmomNfull/acNfull; centre = `s+1`).

So `Δ²V = V(s) − 2·V(s+1) + V(s+2)` is centred at `s+1`, and the parity that matters is the parity of
the CENTRE `s+1`:

  * centre `s+1` ODD  (i.e. `s` EVEN)  — the BINDING (tight) cell.  Here neighbours `s`, `s+2` are
    EVEN, so `V(even) → 0` as `w → 0` while `V(s+1) = V(odd) → 1`, giving `Δ²V → 0 + 0 − 2·1 = −2`
    (corner-tight).  This is the φ-chain / Task-A cell (`OddCentreCellLE`).
  * centre `s+1` EVEN (i.e. `s` ODD)  — the COMFORTABLE cell.  Here neighbours `s`, `s+2` are ODD, so
    `V(s) ≥ 1` and `V(s+2) ≥ 1` (the PROVED two-point tie `dmomNfull_ge_acNfull_odd`), while the centre
    `V(s+1) = V(even)` is small, giving `Δ²V + 2 ≥ 4 − 2·V(s+1) ≥ 59/50 > 0`.  This is the cell PROVED
    here (`EvenCentreCell`, from `CentreVarBound`).

The w-regime split is at `w = 1/2` (`half`): the even-centre certificate constant `141/100` rests on
`G_e(1/4) ≤ 141/100`, valid on the lower half `w ≤ 1/2`; the upper half `1/2 ≤ w` is the
parity-agnostic Task-B cell (`RegimeGECell`).  Since `w : Q'` is an EXACT rational with a DECIDABLE
total order, the regime dichotomy `w ≤ 1/2 ∨ 1/2 ≤ w` is constructive (`q_le_total`, from
`Int.le_total`) — no LEM.

# What this file provides

  * `saddleVarianceFloor_of_cells` — the SCAFFOLD: the three cells inhabit R1
    (`SaddleVarianceFloor w`) by the decidable parity × regime split.  PROVED (axiom-clean modus
    ponens over the cells).
  * `evenCentreCell_of_centreVarBound` — the EVEN-CENTRE cell PROVED, reduced to the single named
    centre bound `CentreVarBound w` via the proved odd-neighbour two-point tie
    `EnvelopeClosure.dmomNfull_ge_acNfull_odd` and the subtraction-free `Q'` algebra `evenCellAlg`.
  * `evenCellAlg` — the cleared, subtraction-free `Q'` inequality of the even cell (the `4 − 2·(141/100)
    = 59/50 ≥ 0` margin), genuinely PROVED (no `sorry`).

NAMED OPEN (Type-level structures, never `sorry`) — for Stages 2–4:
  * `OddCentreCellLE w` — the BINDING cell (`s` even / centre `s+1` odd, `w ≤ 1/2`): the φ-chain
    (`phi_certificate.md`) plus `Δ²(tail) ≥ 0` (Task A, `r1_remaining_pieces.md`).  The near-cancellation
    parity, needing the theta `V_inf` decomposition.
  * `RegimeGECell w` — the upper-half cell (`1/2 ≤ w`, both parities): Task B
    (`r1_remaining_pieces.md`), margin `Δ²V+2 ≥ 12/11` (corner) / `12/7` off-corner.
  * `CentreVarBound w` — the residual of the even cell: `V(even s+1) ≤ 141/100` in cleared form
    `dmomNfull w (s+1) ≤ (141/100)·acNfull w (s+1)` for odd `s` on `w ≤ 1/2`.  This is the theta-layer
    residual `G_e(1/4) ≤ 141/100` (`even_centre_certificate.md`, block E-const/E-cheb/E-mono).

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration below is axiom-checked at the file end.  The scaffold combinator and the
even-cell reduction are pure modus ponens / subtraction-free `Q'` algebra over the reused `≤`/`Q'.eqv`
machinery and the PROVED `dmomNfull_ge_acNfull_odd`; only `propext`/`Quot.sound` (via the `Q'` setoid)
may appear.  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.  The three
named-open cells and `CentreVarBound` are `Type`-level structures (Rule 6a), never `Prop := True` or a
`Unit` witness.
-/

import YMGap.Continuum.EnvelopeClosure
import YMGap.Continuum.CondMomentReduction

namespace YMGap.Continuum.R1CaseSplit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.EnvelopeClosure
open YMGap.Continuum.AcNReserveAnalytic

/-! ## 0. Constructive regime dichotomy and the certificate constants. -/

/-- The regime threshold `1/2` as an exact `Q'`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The even-centre certificate constant `141/100` as an exact `Q'` (`= G_e(1/4)` upper bound). -/
def q141 : Q' := Q'.mkPos 141 100 (by decide)

/-- **`q_le_total`** — the DECIDABLE total order on the exact rationals `Q'` gives the regime
dichotomy constructively (via `Int.le_total` on the cross-products; no LEM). -/
theorem q_le_total (p q : Q') : p ≤ q ∨ q ≤ p := by
  rcases Int.le_total (p.num * (q.den : Int)) (q.num * (p.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## 1. The subtraction-free `Q'` algebra of the even (comfortable) cell.

The cell arithmetic is: with `a_i = acNfull ≥ 0`, `d_i = dmomNfull`, the two odd neighbours give
`a0 ≤ d0`, `a2 ≤ d2`, and the centre bound gives `d1 ≤ (141/100)·a1`.  Then the cleared floor

    2·(d1·(a0·a2))  ≤  d0·(a1·a2) + d2·(a0·a1) + 2·(a0·(a1·a2))

holds because LHS `≤ (2·141/100)·P = (282/100)·P` and RHS `≥ 4·P` with `P = a0·(a1·a2) ≥ 0`, and
`282/100 ≤ 4` (margin `59/50`).  Everything is a MANIFEST nonnegative combination — no cancellation. -/

/-- `(a+b)·c ≃ a·c + b·c` (right distribution, from `mul_add` + `mul_comm`). -/
theorem add_mul_local (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a + b) c)
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c a b)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (c * a) (a * c) (c * b) (Q'.mul_comm_eqv c a))
        (Q'.add_eqv_congr_left (a * c) (c * b) (b * c) (Q'.mul_comm_eqv c b))))

/-- `2·P ≃ P + P` (scalar `Q'.ofNat 2`; decidable coefficient identity + distribution). -/
theorem two_smul (P : Q') : (Q'.ofNat 2 * P).eqv (P + P) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + (1 : Q')) P (by decide))
    (Q'.eqv_trans _ _ _ (add_mul_local (1 : Q') (1 : Q') P)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((1 : Q') * P) P ((1 : Q') * P) (Q'.one_mul_eqv P))
        (Q'.add_eqv_congr_left P ((1 : Q') * P) P (Q'.one_mul_eqv P))))

/-- `(P + P) + 2·P ≃ 4·P` (the RHS-coefficient collapse of the even cell). -/
theorem four_smul (P : Q') : ((P + P) + Q'.ofNat 2 * P).eqv (Q'.ofNat 4 * P) := by
  have e1 : (Q'.ofNat 4 * P).eqv (Q'.ofNat 2 * P + Q'.ofNat 2 * P) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 4) (Q'.ofNat 2 + Q'.ofNat 2) P (by decide))
      (add_mul_local (Q'.ofNat 2) (Q'.ofNat 2) P)
  have e2 : (Q'.ofNat 2 * P + Q'.ofNat 2 * P).eqv ((P + P) + Q'.ofNat 2 * P) :=
    Q'.add_eqv_congr_right (Q'.ofNat 2 * P) (P + P) (Q'.ofNat 2 * P) (two_smul P)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2)

/-- **`evenCellAlg`** — the cleared, subtraction-free even-cell inequality.  From the two odd-neighbour
ties (`a0 ≤ d0`, `a2 ≤ d2`), the centre bound (`d1 ≤ (141/100)·a1`), and nonnegativity of the masses,
the full-range floor's cleared form holds (margin `59/50`).  PROVED — no `sorry`. -/
theorem evenCellAlg {a0 a1 a2 d0 d1 d2 : Q'}
    (h0 : (0 : Q') ≤ a0) (h1 : (0 : Q') ≤ a1) (h2 : (0 : Q') ≤ a2)
    (hN0 : a0 ≤ d0) (hN2 : a2 ≤ d2) (hC : d1 ≤ q141 * a1) :
    Q'.ofNat 2 * (d1 * (a0 * a2))
      ≤ d0 * (a1 * a2) + d2 * (a0 * a1) + Q'.ofNat 2 * (a0 * (a1 * a2)) := by
  -- nonnegativity atoms
  have hP : (0 : Q') ≤ a0 * (a1 * a2) :=
    Q'.mul_nonneg _ _ h0 (Q'.mul_nonneg _ _ h1 h2)
  have ha0a2 : (0 : Q') ≤ a0 * a2 := Q'.mul_nonneg _ _ h0 h2
  have ha1a2 : (0 : Q') ≤ a1 * a2 := Q'.mul_nonneg _ _ h1 h2
  have ha0a1 : (0 : Q') ≤ a0 * a1 := Q'.mul_nonneg _ _ h0 h1
  -- (L1)  LHS ≤ (2·q141)·P                         [centre bound, then rearrange]
  have hstep1 : d1 * (a0 * a2) ≤ (q141 * a1) * (a0 * a2) :=
    Q'.mul_le_mul_of_nonneg_right d1 (q141 * a1) (a0 * a2) hC ha0a2
  have hstep2 : Q'.ofNat 2 * (d1 * (a0 * a2)) ≤ Q'.ofNat 2 * ((q141 * a1) * (a0 * a2)) :=
    Q'.mul_le_mul_of_nonneg_left (d1 * (a0 * a2)) ((q141 * a1) * (a0 * a2)) (Q'.ofNat 2)
      hstep1 (by decide)
  have hrearr : (Q'.ofNat 2 * ((q141 * a1) * (a0 * a2))).eqv
      ((Q'.ofNat 2 * q141) * (a0 * (a1 * a2))) := by ring_qeqv
  have hL1 : Q'.ofNat 2 * (d1 * (a0 * a2)) ≤ (Q'.ofNat 2 * q141) * (a0 * (a1 * a2)) :=
    Q'.le_trans' _ _ _ hstep2 (Q'.le_of_eqv hrearr)
  -- (L2)  (2·q141)·P ≤ 4·P                         [282/100 ≤ 4, P ≥ 0]
  have hL2 : (Q'.ofNat 2 * q141) * (a0 * (a1 * a2)) ≤ Q'.ofNat 4 * (a0 * (a1 * a2)) :=
    Q'.mul_le_mul_of_nonneg_right (Q'.ofNat 2 * q141) (Q'.ofNat 4) (a0 * (a1 * a2))
      (by decide) hP
  -- (L3)  4·P ≤ (P + P) + 2·P                      [coefficient collapse]
  have hL3 : Q'.ofNat 4 * (a0 * (a1 * a2))
      ≤ (a0 * (a1 * a2) + a0 * (a1 * a2)) + Q'.ofNat 2 * (a0 * (a1 * a2)) :=
    Q'.ge_of_eqv (four_smul (a0 * (a1 * a2)))
  -- (L4)  the two odd neighbours push each `P` up to `d0·(a1·a2)`, `d2·(a0·a1)`
  have hT1 : a0 * (a1 * a2) ≤ d0 * (a1 * a2) :=
    Q'.mul_le_mul_of_nonneg_right a0 d0 (a1 * a2) hN0 ha1a2
  have hPa2 : (a0 * (a1 * a2)).eqv (a2 * (a0 * a1)) := by ring_qeqv
  have hT2 : a0 * (a1 * a2) ≤ d2 * (a0 * a1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hPa2)
      (Q'.mul_le_mul_of_nonneg_right a2 d2 (a0 * a1) hN2 ha0a1)
  have hPP : (a0 * (a1 * a2) + a0 * (a1 * a2)) ≤ d0 * (a1 * a2) + d2 * (a0 * a1) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right (a0 * (a1 * a2)) (d0 * (a1 * a2)) (a0 * (a1 * a2)) hT1)
      (Q'.add_le_add_left (d0 * (a1 * a2)) (a0 * (a1 * a2)) (d2 * (a0 * a1)) hT2)
  have hL4 : (a0 * (a1 * a2) + a0 * (a1 * a2)) + Q'.ofNat 2 * (a0 * (a1 * a2))
      ≤ (d0 * (a1 * a2) + d2 * (a0 * a1)) + Q'.ofNat 2 * (a0 * (a1 * a2)) :=
    Q'.add_le_add_right _ _ (Q'.ofNat 2 * (a0 * (a1 * a2))) hPP
  -- chain L1 ≤ L2 ≤ L3 ≤ L4
  exact Q'.le_trans' _ _ _ hL1
    (Q'.le_trans' _ _ _ hL2 (Q'.le_trans' _ _ _ hL3 hL4))

/-! ## 2. The three cells and the residual centre bound (Type-level). -/

/-- **`OddCentreCellLE w`** (BINDING cell — NAMED OPEN).  Centre `s+1` ODD (`s` even), lower-half
regime `w ≤ 1/2`.  The near-cancelling parity; discharged in the paper proof by the φ-chain
(`phi_certificate.md`) + `Δ²(tail) ≥ 0` (Task A, `r1_remaining_pieces.md`).  Stage 2+. -/
structure OddCentreCellLE (w : Q') : Type where
  cell : w ≤ half → ∀ s, s % 2 = 0 → FullRangeFloor w s

/-- **`EvenCentreCell w`** (COMFORTABLE cell).  Centre `s+1` EVEN (`s` odd), lower-half regime
`w ≤ 1/2`.  PROVED here from `CentreVarBound` via `evenCentreCell_of_centreVarBound`. -/
structure EvenCentreCell (w : Q') : Type where
  cell : w ≤ half → ∀ s, s % 2 = 1 → FullRangeFloor w s

/-- **`RegimeGECell w`** (upper-half cell — NAMED OPEN).  Regime `1/2 ≤ w`, both parities.
Discharged in the paper proof by Task B (`r1_remaining_pieces.md`), margin `≥ 12/11`.  Stage 2+. -/
structure RegimeGECell (w : Q') : Type where
  cell : half ≤ w → ∀ s, FullRangeFloor w s

/-- **`CentreVarBound w`** (residual of the even cell — NAMED OPEN).  The centre variance bound
`V(even s+1) ≤ 141/100`, cleared/subtraction-free at the `acNfull` level: for odd `s` (centre `s+1`
even) on the lower half `w ≤ 1/2`, `dmomNfull w (s+1) ≤ (141/100)·acNfull w (s+1)`.  This is the
theta-layer residual `G_e(1/4) ≤ 141/100` (`even_centre_certificate.md`).  Stage 3 (theta layer). -/
structure CentreVarBound (w : Q') : Type where
  bound : w ≤ half → ∀ s, s % 2 = 1 → dmomNfull w (s + 1) ≤ q141 * acNfull w (s + 1)

/-! ## 3. The even cell, PROVED from the residual centre bound. -/

/-- **`evenCentreCell_of_centreVarBound`** — the COMFORTABLE cell PROVED.  Given `0 ≤ w` and the
named centre bound `CentreVarBound w`, the even-centre cell holds: for odd `s`, the two ODD neighbours
`s`, `s+2` give `acNfull ≤ dmomNfull` (the PROVED two-point tie `dmomNfull_ge_acNfull_odd`), the centre
bound gives `dmomNfull w (s+1) ≤ (141/100)·acNfull w (s+1)`, and `evenCellAlg` closes the cleared floor
with margin `59/50`.  No `sorry`. -/
def evenCentreCell_of_centreVarBound {w : Q'} (hw : (0 : Q') ≤ w)
    (C : CentreVarBound w) : EvenCentreCell w where
  cell := fun hle s hs => by
    have hs2 : (s + 2) % 2 = 1 := by omega
    have h0 : (0 : Q') ≤ acNfull w s := acN_nonneg hw (s + 1) s
    have h1 : (0 : Q') ≤ acNfull w (s + 1) := acN_nonneg hw (s + 2) (s + 1)
    have h2 : (0 : Q') ≤ acNfull w (s + 2) := acN_nonneg hw (s + 3) (s + 2)
    have hN0 : acNfull w s ≤ dmomNfull w s := dmomNfull_ge_acNfull_odd hw hs
    have hN2 : acNfull w (s + 2) ≤ dmomNfull w (s + 2) := dmomNfull_ge_acNfull_odd hw hs2
    have hC : dmomNfull w (s + 1) ≤ q141 * acNfull w (s + 1) := C.bound hle s hs
    exact evenCellAlg h0 h1 h2 hN0 hN2 hC

/-! ## 4. THE SCAFFOLD — R1 from the three cells. -/

/-- **`saddleVarianceFloor_of_cells` — THE STAGE-1 SCAFFOLD.**  The three paper cells inhabit R1
(`SaddleVarianceFloor w`).  For each window `s`, the DECIDABLE regime dichotomy `q_le_total` splits on
`w ≤ 1/2` vs `1/2 ≤ w`, and in the lower half the DECIDABLE parity of `s`
(`Nat.mod_two_eq_zero_or_one`) selects the odd-centre (`s` even) or even-centre (`s` odd) cell; the
upper half is the parity-agnostic regime cell.  Pure modus ponens — axiom-clean. -/
def saddleVarianceFloor_of_cells {w : Q'}
    (E : EvenCentreCell w) (O : OddCentreCellLE w) (R : RegimeGECell w) :
    SaddleVarianceFloor w where
  floor := fun s => by
    rcases q_le_total w half with hle | hge
    · rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
      · exact O.cell hle s h0
      · exact E.cell hle s h1
    · exact R.cell hge s

/-- **`saddleVarianceFloor_of_reduced`** — the fully-assembled Stage-1 statement: R1 from the ONE
proved even-cell residual `CentreVarBound` plus the two named-open hard cells.  Makes explicit that
the even cell is discharged (down to `CentreVarBound`) while `OddCentreCellLE`/`RegimeGECell` remain
the Stage-2+ frontier. -/
def saddleVarianceFloor_of_reduced {w : Q'} (hw : (0 : Q') ≤ w)
    (C : CentreVarBound w) (O : OddCentreCellLE w) (R : RegimeGECell w) :
    SaddleVarianceFloor w :=
  saddleVarianceFloor_of_cells (evenCentreCell_of_centreVarBound hw C) O R

/-! ## 5. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `q_le_total` — the constructive regime dichotomy on the exact rationals `Q'`.
  * `add_mul_local`, `two_smul`, `four_smul`, `evenCellAlg` — the subtraction-free `Q'` algebra of the
    even (comfortable) cell (`4 − 2·(141/100) = 59/50 ≥ 0`).
  * `evenCentreCell_of_centreVarBound` — the EVEN-CENTRE cell, reduced to `CentreVarBound` via the
    PROVED odd-neighbour two-point tie `dmomNfull_ge_acNfull_odd`.
  * `saddleVarianceFloor_of_cells` — the SCAFFOLD: the three cells inhabit R1 by the decidable
    parity × regime split.
  * `saddleVarianceFloor_of_reduced` — R1 from `CentreVarBound` + the two hard cells.

NAMED OPEN (Type-level structures, never `sorry`) — Stage 2+:
  * `OddCentreCellLE w` — the BINDING cell (`s` even / centre `s+1` odd, `w ≤ 1/2`): φ-chain
    (`phi_certificate.md`) + Task A (`r1_remaining_pieces.md`).
  * `RegimeGECell w` — the upper-half cell (`1/2 ≤ w`): Task B (`r1_remaining_pieces.md`).
  * `CentreVarBound w` — the residual of the even cell: `V(even s+1) ≤ 141/100` cleared
    (`dmomNfull w (s+1) ≤ (141/100)·acNfull w (s+1)`, odd `s`, `w ≤ 1/2`); the theta-layer bound
    `G_e(1/4) ≤ 141/100` (`even_centre_certificate.md`).
-/

end YMGap.Continuum.R1CaseSplit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1CaseSplit.q_le_total
#print axioms YMGap.Continuum.R1CaseSplit.add_mul_local
#print axioms YMGap.Continuum.R1CaseSplit.two_smul
#print axioms YMGap.Continuum.R1CaseSplit.four_smul
#print axioms YMGap.Continuum.R1CaseSplit.evenCellAlg
#print axioms YMGap.Continuum.R1CaseSplit.evenCentreCell_of_centreVarBound
#print axioms YMGap.Continuum.R1CaseSplit.saddleVarianceFloor_of_cells
#print axioms YMGap.Continuum.R1CaseSplit.saddleVarianceFloor_of_reduced
