/-
Track B / R2 — THE EIGENVALUE-SHIFT BRIDGE: the `weight-defect ⟹ eigenvalue-shift`
step that `SpectralLocalizationCrux.SpectralLocalization` left as its sole named
input.  VERDICT: the bridge is DIAGONAL (multiplicity-blind), and it CLOSES the
bulk localization to a clean conditional — `bondMoved_below_gapEdge` — reducing
`hlocalize` to a single per-mode EIGENVALUE-shift bound `eigShift ≤ 1/12`, with NO
`(s+1)` density factor.

# Diagonality — why the eigenvalue route is multiplicity-blind

The heat-kernel transfer operator and the Migdal–Kadanoff bond-moved operator are
BOTH class functions on SU(2): both are DIAGONAL in the character basis `{χ_s}`.
A class-function convolution operator has, on the mode `χ_s`, the vacuum-normalized
EIGENVALUE

    (mode-s eigenvalue)  =  (its character coefficient) / dimQ s,

because the coefficient `coeffW w s = dimQ s · w^{C₄(s)}` is the eigenvalue
`w^{C₄(s)}` times the degeneracy `dimQ s = s + 1`.  Consequently the bond-moving
perturbation, being diagonal in the SAME basis, shifts the mode-`s` eigenvalue by
EXACTLY its own per-mode coefficient defect divided by `dimQ s` — with NO coupling
to other modes and NO `(s+1)²` spectral-density weight.  This is the precise sense
in which the gap (a second-eigenvalue separation) is multiplicity-blind: the
`(s+1)` that makes the SCALED-NORM bulk sum (`BulkModeCrux`) diverge sits in the
DENSITY, not in the eigenvalue shift.

# The two objects (do NOT conflate)

  * `coeffShift` := `|bondMovedCoeff − KtauFix|` — the COEFFICIENT defect, which
    carries the `dimQ s = (s+1)` multiplicity (it is `Kτ`-weighted).
  * `eigShift`   := `|bmEig − retEig|` — the genuine vacuum-normalized EIGENVALUE
    shift, where `bmEig = bondMovedCoeff / dimQ s` and `retEig = renormWFix^{C₄(s)}`
    is the retuned per-mode eigenvalue.  This is the multiplicity-STRIPPED object.

The headline diagonality identity `coeffDefect_eq_mult`

    bondMovedCoeff − KtauFix  ≃  dimQ s · (bmEig − retEig),

ISOLATES the `(s+1)` factor explicitly: the eigenvalue defect `bmEig − retEig` is
the coefficient defect with the multiplicity divided out.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `bmEig` / `retEig` — the bond-moved and retuned per-mode EIGENVALUES (the
    vacuum-normalized, multiplicity-stripped transfer-operator diagonal entries);
    `retEig_nonneg`, `retEig_le_one`.
  * **`coeffDefect_eq_mult`** (DIAGONALITY / MULTIPLICITY-BLINDNESS).  The signed
    coefficient defect equals `dimQ s` times the eigenvalue defect — the `(s+1)`
    factor is the explicit prefactor; the eigenvalue shift carries none of it.
  * **`bondMoved_below_gapEdge`** (THE BRIDGE, CLOSED conditionally).  On the
    near-continuum regime `1 − w ≤ 1/12` and the bulk window (at the retuned base),
    IF the per-mode eigenvalue shift `eigShift ≤ 1/12`, THEN the bond-moved bulk
    eigenvalue stays at or below the gap edge: `bmEig ≤ eigA w 1 = w³`.  PROOF:
    `retEig ≤ 2/3` (`bulk_eigA_le` at the retuned base), `bmEig ≤ retEig + eigShift
    ≤ 2/3 + 1/12 = 3/4 ≤ w³`.  The genuine bond-moved spectrum analogue of
    `localization_holds`, at the eigenvalue level.
  * `gapMode_low` — the gap mode `s = 1` is ALWAYS a low mode: on `1 − w ≤ 1/12`,
    `C₄(1)·(1 − w) ≤ 1/4 < 1/2`, BELOW the bulk window.  So the gap edge is never in
    the bulk; its cumulative shift is the `s = 1` quadratic budget
    (`BondMovingQuadratic`, summable).
  * **`bulkBand_convex`** (THE MOVING WINDOW).  For an antitone margin sequence
    `e_k = 1 − w_k`, bulk-window membership is CONVEX in the step index `k`: a fixed
    mode `s` enters the bulk band once and exits once (a single contiguous block of
    steps).  This is the structural moving-window fact.

# Honest verdict on the bridge and the moving window

The bridge `weight-defect ⟹ eigenvalue-shift` is now a CLEAN diagonal reduction:
`hlocalize` is replaced by the single per-mode bound `eigShift ≤ 1/12`, which —
unlike the scaled-norm summability that `BulkModeCrux` showed FAILS — carries NO
`(s+1)` density.  `bondMoved_below_gapEdge` discharges everything ELSE.

The remaining residual is the per-mode `eigShift ≤ 1/12` on the bulk.  Since
`eigShift = retEig · |rrelFix|` (the retuned eigenvalue times the relative
residual, `retEig ≤ 1`), the single-step bulk bound is `eigShift ≤ |rrelFix|`,
i.e. it reduces to the SAME relative-residual obligation `FusionRelResidualBound`
(`|rrelFix| ≤ (1−w)²·P`) that the `s = 1`-dominated route already names — NOT a new
analytic input.  So the eigenvalue bridge CLOSES the localization conditionally and
REDUCES to the `s = 1`-dominant relative-residual bound.

HONEST CORRECTION to the naive moving-window count.  Along the harmonic AF
trajectory `1 − w_k ∼ A/k`, a fixed mode's bulk band `C₄(s)·(1 − w_k) ∈ [1/2, 3/4]`
pins `k ∈ [(4A/3)·C₄(s), 2A·C₄(s)]`, a contiguous block of width `∼ C₄(s) ∼ s²` —
NOT a constant.  The cumulative eigenvalue shift on a fixed mode is finite NOT
because the window is `O(1)` steps, but because the per-step shift on that band is
quadratic `∼ (1 − w_k)² ∼ 1/C₄(s)² ∼ 1/s⁴`, and `(width s²)·(per-step 1/s⁴) ∼
1/s²` — summable.  `bulkBand_convex` supplies the contiguity (single entry/exit);
the quadratic-times-width balance is the proven graded budget (`GradedBondMovingBudget`).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over already-proved engines (`bulk_eigA_le`,
`gapEdge_ge`, `divPos_mul_eqv`, `le_absQ`).  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.GradedBondMovingBudget

namespace YMGap.Continuum.EigenvalueShiftBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.FusionQuotientCollapse

/-! ## 0. Small `Q'` helpers (axiom-clean) -/

/-- Two-sided additive monotonicity `a ≤ b → c ≤ d → a + c ≤ b + d` (local copy). -/
theorem qadd_le_add {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- From `a + -b ≤ c` conclude `a ≤ c + b` (move `b` across).  PROOF:
`a ≃ (a + -b) + b ≤ c + b`. -/
theorem le_add_of_sub_le {a b c : Q'} (h : a + -b ≤ c) : a ≤ c + b := by
  have hstep : (a + -b) + b ≤ c + b := Q'.add_le_add_right (a + -b) c b h
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hstep
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-! ## 1. The per-mode transfer EIGENVALUES (vacuum-normalized, multiplicity-stripped) -/

/-- **The retuned per-mode transfer eigenvalue** `retEig p hp w s =
renormWFix^{C₄(s)}` — the diagonal entry of the RETUNED heat-kernel transfer
operator on the character `χ_s`, with NO degeneracy factor.  By construction
`KtauFix p hp w s = dimQ s · retEig p hp w s` (the coefficient is eigenvalue ×
multiplicity). -/
def retEig (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) : Q' :=
  qpow (renormWFix p hp w) (c4 s)

/-- `KtauFix = dimQ s · retEig` definitionally — the coefficient is the eigenvalue
times the degeneracy `dimQ s = s + 1`. -/
theorem KtauFix_eq_dimQ_retEig (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) :
    KtauFix p hp w s = dimQ s * retEig p hp w s := rfl

theorem retEig_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (p : Nat) (hp : 0 < p) (s : Nat) :
    (0 : Q') ≤ retEig p hp w s :=
  qpow_nonneg _ (renormWFix_nonneg hw0 p hp) (c4 s)

theorem retEig_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) (hp : 0 < p) (s : Nat) :
    retEig p hp w s ≤ (1 : Q') :=
  qpow_le_one (renormWFix_nonneg hw0 p hp) (renormWFix_le_one hw1 p hp) (c4 s)

/-- **The bond-moved per-mode transfer eigenvalue** `bmEig N p w s =
bondMovedCoeff N w p s / dimQ s` — the diagonal entry of the BOND-MOVED transfer
operator on `χ_s`, the bond-moved coefficient with the degeneracy `dimQ s` divided
out (the multiplicity-stripped eigenvalue). -/
def bmEig (N p : Nat) (w : Q') (s : Nat) : Q' :=
  Q'.divPos (bondMovedCoeff N w p s) (dimQ s) (Q'.ofNat_succ_pos s)

theorem bmEig_nonneg (N p : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat) :
    (0 : Q') ≤ bmEig N p w s := by
  show (0 : Q') ≤ Q'.divPos (bondMovedCoeff N w p s) (dimQ s) (Q'.ofNat_succ_pos s)
  unfold Q'.divPos
  exact Q'.mul_nonneg _ _ (bondMovedCoeff_nonneg N hw0 p s)
    (Q'.le_of_lt (Q'.recipPos_pos (dimQ s) (Q'.ofNat_succ_pos s)))

/-- `bondMovedCoeff = dimQ s · bmEig` — the coefficient is the bond-moved eigenvalue
times the degeneracy. -/
theorem bmc_eq_dimQ_bmEig (N p : Nat) (w : Q') (s : Nat) :
    (bondMovedCoeff N w p s).eqv (dimQ s * bmEig N p w s) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (dimQ s) (bmEig N p w s)) ?_
  exact Q'.divPos_mul_eqv (bondMovedCoeff N w p s) (dimQ s) (Q'.ofNat_succ_pos s)

/-! ## 2. THE DIAGONALITY / MULTIPLICITY-BLINDNESS IDENTITY -/

/-- **THE DIAGONALITY IDENTITY (multiplicity-blindness).**  The signed COEFFICIENT
defect equals `dimQ s` times the signed EIGENVALUE defect:

    bondMovedCoeff − KtauFix  ≃  dimQ s · (bmEig − retEig).

The `(s+1) = dimQ s` multiplicity is the EXPLICIT prefactor; the eigenvalue defect
`bmEig − retEig` carries NONE of it.  This is the precise sense in which the
bond-moving perturbation — diagonal in the character basis shared by both class-
function operators — shifts the mode-`s` eigenvalue by its own per-mode defect with
no density weight.  PROOF: `bondMovedCoeff ≃ dimQ s · bmEig` (`divPos`),
`KtauFix = dimQ s · retEig` (def), then distribute `dimQ s` over the difference. -/
theorem coeffDefect_eq_mult (N p : Nat) (hp : 0 < p) (w : Q') (s : Nat) :
    (bondMovedCoeff N w p s + -(KtauFix p hp w s)).eqv
      (dimQ s * (bmEig N p w s + -(retEig p hp w s))) := by
  -- KtauFix = dimQ s · retEig definitionally, so the LHS is bmc + -(dimQ s · retEig)
  have hbmc : (bondMovedCoeff N w p s).eqv (dimQ s * bmEig N p w s) :=
    bmc_eq_dimQ_bmEig N p w s
  show (bondMovedCoeff N w p s + -(dimQ s * retEig p hp w s)).eqv
      (dimQ s * (bmEig N p w s + -(retEig p hp w s)))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(dimQ s * retEig p hp w s)) hbmc) ?_
  -- (dimQ·bmEig) + -(dimQ·retEig) ≃ dimQ·(bmEig + -retEig)
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (dimQ s) (bmEig N p w s) (-(retEig p hp w s))) ?_
  exact Q'.add_eqv_congr_left (dimQ s * bmEig N p w s) _ _
    (Q'.mul_neg_eqv (dimQ s) (retEig p hp w s))

/-- **The coefficient defect** (the `Kτ`-weighted, multiplicity-CARRYING one). -/
def coeffShift (N p : Nat) (hp : 0 < p) (w : Q') (s : Nat) : Q' :=
  absQ (bondMovedCoeff N w p s + -(KtauFix p hp w s))

/-- **The per-mode EIGENVALUE shift** (the multiplicity-STRIPPED one): the absolute
diagonal perturbation of the bond-moved transfer eigenvalue on mode `s`,

    eigShift N p hp w s  =  |bmEig − retEig|,

carrying NO `(s+1)` factor.  This is the genuine spectral object the gap (a
second-eigenvalue separation) sees. -/
def eigShift (N p : Nat) (hp : 0 < p) (w : Q') (s : Nat) : Q' :=
  absQ (bmEig N p w s + -(retEig p hp w s))

theorem eigShift_nonneg (N p : Nat) (hp : 0 < p) (w : Q') (s : Nat) :
    (0 : Q') ≤ eigShift N p hp w s :=
  absQ_nonneg _

/-! ## 3. THE BRIDGE — the bond-moved bulk eigenvalue stays below the gap edge -/

/-- **THE EIGENVALUE-SHIFT BRIDGE (CLOSED, conditional on a per-mode `eigShift` bound).**
On the near-continuum regime `1 − w ≤ 1/12` and a bulk mode at the retuned base
(`1/2 ≤ C₄(s)·(1 − renormWFix)`), IF the per-mode eigenvalue shift is below the
localization margin (`eigShift ≤ 1/12`), THEN the bond-moved bulk eigenvalue stays
at or below the gap edge:

    bmEig N p w s  ≤  eigA w 1  ( = w³ ).

So the bond-moved bulk does NOT rise to the `s = 1` gap edge: the gap survives.  This
is the genuine bond-moved-spectrum analogue of
`SpectralLocalizationCrux.localization_holds`, at the EIGENVALUE level — and it is
multiplicity-BLIND (the `eigShift` hypothesis has no `(s+1)` density).  PROOF:
`retEig ≤ 2/3` (`bulk_eigA_le` at base `renormWFix`), `bmEig ≤ retEig + eigShift`
(`le_absQ`), `2/3 + 1/12 = 3/4 ≤ w³` (`gapEdge_ge`). -/
theorem bondMoved_below_gapEdge (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat)
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (hbulk : BulkModeCrux.q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - renormWFix p hp w))
    (hshift : eigShift N p hp w s ≤ SpectralLocalizationCrux.q112) :
    bmEig N p w s ≤ SpectralLocalizationCrux.eigA w 1 := by
  -- retEig = eigA (renormWFix) s ≤ 2/3 on the bulk window at the retuned base
  have hret : retEig p hp w s ≤ SpectralLocalizationCrux.q23 :=
    SpectralLocalizationCrux.bulk_eigA_le (renormWFix_nonneg hw0 p hp)
      (renormWFix_le_one hw1 p hp) s hbulk
  -- bmEig − retEig ≤ |bmEig − retEig| = eigShift
  have hdef : bmEig N p w s + -(retEig p hp w s) ≤ eigShift N p hp w s :=
    le_absQ _
  -- bmEig ≤ eigShift + retEig
  have hb : bmEig N p w s ≤ eigShift N p hp w s + retEig p hp w s :=
    le_add_of_sub_le hdef
  -- eigShift + retEig ≤ 1/12 + 2/3 = 3/4 ≤ eigA w 1
  have hsum : eigShift N p hp w s + retEig p hp w s
      ≤ SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23 :=
    qadd_le_add hshift hret
  have hedge : SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23
      ≤ SpectralLocalizationCrux.eigA w 1 :=
    Q'.le_trans' _ _ _
      (by decide : SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23
            ≤ BulkModeCrux.q34)
      (SpectralLocalizationCrux.gapEdge_ge hw0 hw1 hnc)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ hsum hedge)

/-! ## 4. The gap mode `s = 1` is always a low mode (never in the bulk) -/

/-- **The gap mode `s = 1` is a LOW mode.**  On `1 − w ≤ 1/12`,

    C₄(1)·(1 − w)  =  3·(1 − w)  ≤  1/4  <  1/2,

so `s = 1` is BELOW the bulk window `[1/2, 3/4]` — the gap edge is never in the bulk.
Hence its cumulative bond-moving shift is the `s = 1` quadratic budget
(`BondMovingQuadratic`, summable), not a bulk `Θ(1)` defect. -/
theorem gapMode_low {w : Q'}
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112) :
    Q'.ofNat (c4 1) * ((1 : Q') - w) ≤ BulkModeCrux.q14 := by
  have h1 : Q'.ofNat (c4 1) * ((1 : Q') - w)
      ≤ Q'.ofNat (c4 1) * SpectralLocalizationCrux.q112 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnc (zero_le_ofNat (c4 1))
  exact Q'.le_trans' _ _ _ h1
    (by decide : Q'.ofNat (c4 1) * SpectralLocalizationCrux.q112 ≤ BulkModeCrux.q14)

/-- `1/4 < 1/2`: the gap mode's Casimir-margin product is STRICTLY below the bulk
window's lower edge.  Together with `gapMode_low`: the gap edge `s = 1` is never on
the bulk window. -/
theorem gapMode_below_bulk : BulkModeCrux.q14 < BulkModeCrux.q12 := by decide

/-! ## 5. THE MOVING WINDOW — bulk-band membership is convex in the step index -/

/-- **THE MOVING-WINDOW CONTIGUITY.**  For an ANTITONE margin sequence `e`
(`e_k = 1 − w_k`, decreasing along asymptotic freedom), bulk-band membership
`α ≤ e_k ≤ β` is CONVEX in the step index `k`: if `j ≤ k ≤ l` and the band holds at
the endpoints `j` (upper) and `l` (lower), it holds at `k`.  So a FIXED mode enters
the bulk band once and exits once — a single contiguous block of trajectory steps
(`e l ≤ e k ≤ e j`, sandwiched between the two endpoint bounds).

This is the structural moving-window fact: the per-mode bulk residence is a single
entry/exit interval.  (Its WIDTH is `∼ C₄(s) ∼ s²` along the harmonic AF rate, NOT
`O(1)` — see the module header; the cumulative-shift finiteness comes from the
quadratic per-step budget, not from a constant window count.) -/
theorem bulkBand_convex {e : Nat → Q'} (hanti : ∀ i j, i ≤ j → e j ≤ e i)
    {α β : Q'} {j k l : Nat} (hjk : j ≤ k) (hkl : k ≤ l)
    (hj : e j ≤ β) (hl : α ≤ e l) :
    α ≤ e k ∧ e k ≤ β :=
  ⟨Q'.le_trans' _ _ _ hl (hanti k l hkl),
   Q'.le_trans' _ _ _ (hanti j k hjk) hj⟩

/-! ## 6. Demo — the bridge fires conditionally at a concrete near-continuum weight

Reusing `SpectralLocalizationCrux.demoW = 95/96` (`1 − w = 1/96 ≤ 1/12`).  We
exhibit the bridge as a clean conditional: GIVEN a per-mode eigenvalue-shift bound
`eigShift ≤ 1/12` (the named residual), the bond-moved bulk eigenvalue stays below
the gap edge. -/

/-- The demo weight `w = 95/96`. -/
def demoW : Q' := SpectralLocalizationCrux.demoW

theorem demoW_nc : (1 : Q') - demoW ≤ SpectralLocalizationCrux.q112 :=
  SpectralLocalizationCrux.demoW_nc

/-- **The bridge fires at `w = 95/96`** (conditional on the per-mode `eigShift`
bound): for any `N`, `p ≥ 1`, and bulk mode `s` at the retuned base with
`eigShift ≤ 1/12`, the bond-moved bulk eigenvalue `bmEig ≤ eigA (95/96) 1`. -/
theorem demo_bridge (N p : Nat) (hp : 0 < p) (s : Nat)
    (hbulk : BulkModeCrux.q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - renormWFix p hp demoW))
    (hshift : eigShift N p hp demoW s ≤ SpectralLocalizationCrux.q112) :
    bmEig N p demoW s ≤ SpectralLocalizationCrux.eigA demoW 1 :=
  bondMoved_below_gapEdge N p hp SpectralLocalizationCrux.demoW_pos
    SpectralLocalizationCrux.demoW_le_one s demoW_nc hbulk hshift

end YMGap.Continuum.EigenvalueShiftBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EigenvalueShiftBridge.le_add_of_sub_le
#print axioms YMGap.Continuum.EigenvalueShiftBridge.KtauFix_eq_dimQ_retEig
#print axioms YMGap.Continuum.EigenvalueShiftBridge.retEig_nonneg
#print axioms YMGap.Continuum.EigenvalueShiftBridge.retEig_le_one
#print axioms YMGap.Continuum.EigenvalueShiftBridge.bmEig_nonneg
#print axioms YMGap.Continuum.EigenvalueShiftBridge.bmc_eq_dimQ_bmEig
#print axioms YMGap.Continuum.EigenvalueShiftBridge.coeffDefect_eq_mult
#print axioms YMGap.Continuum.EigenvalueShiftBridge.eigShift_nonneg
#print axioms YMGap.Continuum.EigenvalueShiftBridge.bondMoved_below_gapEdge
#print axioms YMGap.Continuum.EigenvalueShiftBridge.gapMode_low
#print axioms YMGap.Continuum.EigenvalueShiftBridge.gapMode_below_bulk
#print axioms YMGap.Continuum.EigenvalueShiftBridge.bulkBand_convex
#print axioms YMGap.Continuum.EigenvalueShiftBridge.demo_bridge
