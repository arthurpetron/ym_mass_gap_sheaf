/-
Closing the Option-2 target `WilsonParsevalExt.SymbolTypedParseval` down to ONE
named, satisfiable, choice-free constructive-completion residual.

# What this module delivers

`Continuum/WilsonParsevalExt.lean` named `SymbolTypedParseval w N` — the
`DiagonalTransferSymbol`-typed `WilsonLinearFC.WilsonTowerParseval` that
`wilsonLinearTransfer` actually consumes — as an OPEN `Type`-level residual: it
requires a `SmulGNSData D`, a symbol `S`, and a fully realized `S`-typed Parseval
datum over the CANONICAL completion `D.toGNSData.gnsComplete.hilbert.cinner`.
The concrete character carrier of `Continuum/WilsonSchurIdentities.lean` cannot
populate it: its inner product is the DIRECTLY-defined irrational-weighted
`charHilbert.cinner`, its base scaffold `charGNS` is degenerate (`B ≡ 0`, canonical
completion = one point), and `charTransfer.T ≠ S.TqSymb`.  So Option 2 is a genuine
rebuild with a NON-degenerate rational base form (which forces dropping the
irrational weights `μ_s`; see the honesty note below).

Here we carry out that rebuild and reduce the target to exactly one residual:

  * **`charSmulGNS N`** (GENUINE, discharged) — the rational Euclidean base module
    on `V = Nat → Q'` with `B a b = Σ_{s<N} a_s·b_s` (`RationalTail.finSum`).  Every
    `GNSData`/`SmulGNSData` field is the `finSum` lift of the single-coordinate
    `qWeightGNS`/`qSmulGNS` algebra (`finSum_eqv_congr`, `finSum_add`,
    `const_mul_finSum`, `finSum_le_termwise`).
  * **`charDiagonalSymbol w hw0 hw1 N`** (GENUINE, discharged) — the diagonal
    λ-symbol `Dv a = (λ_s·a_s)`, `λ_s = qpow w (c4 (s+1))`.  All five fields are
    per-coordinate rationals; the contraction `d²(Dv a, Dv b) ≤ d²(a,b)` is the
    `finSum` lift of `q_sq_scale_le` (`0 ≤ λ_s ≤ 1`).
  * **`FinEuclCompletionCoords w hw0 hw1 N`** (the SOLE residual) — the
    RC-diagonal resolution of the finite-dimensional canonical completion: an
    `RC`-coordinate projection `proj`, the standard-Euclidean resolution
    `⟨z,z'⟩ = Σ_i (proj z i)·(proj z' i)`, and the intertwiner
    `proj (T z) i = λ_i·(proj z i)`.  Named as `Type`-level data (Rule 8), never
    faked.  Both clauses are choice-free finite-dimensional completion facts.
  * **`symbolTypedParsevalWilson`** (GENUINE assembly) — from a
    `FinEuclCompletionCoords` inhabits `SymbolTypedParseval w N`, with the four
    Parseval fields discharged as one-line `RCmul`/`RCscale` rearrangements
    (`RCmul_scale_left/right/both`, `RCmul_self_nonneg`).

Net: the open Option-2 target reduces to exactly `FinEuclCompletionCoords`.

# Honesty (AGENTS.md Rule 6)

The rational base form carries weight-1 coordinates; the physical reflection form
carries `μ_s = e^{−t·C₂}` (a `CReal`).  The SPECTRUM (`λ_s = qpow w (c4 (s+1))`,
gap from `λ_1 < 1`) is preserved, but this `SymbolTypedParseval` is for the
WEIGHT-1 tower — an existence witness over its own `D, S`, not a `√μ`-fidelity
match to the interacting `E_Λ` moment functional.  That, and the base
Peter–Weyl/OS "parseval" for `E_Λ`, remain separate inputs (as the target already
scopes).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonParsevalExt
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.RCScaleClose
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.CRealAlg

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.CharacterDiagResolutionProof
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.WilsonParsevalExt
open YMGap.Continuum.WilsonLinearFC

namespace YMGap.Continuum.SymbolTypedParsevalClose

/-! ## 0. The `Q'` rearrangements the constructions need -/

/-- `l·a + -(l·b) ≃ l·(a + -b)` — the per-coordinate distributivity used both in
`charSmulGNS.smul_sub` and in the contraction `distSqQ_Dv`. -/
theorem q_mul_sub_distrib (l a b : Q') : ((l * a) + -(l * b)).eqv (l * (a + -b)) := by
  have h1 : (l * (a + -b)).eqv (l * a + l * (-b)) := Q'.mul_add_eqv l a (-b)
  have h2 : (l * a + l * (-b)).eqv (l * a + -(l * b)) :=
    Q'.add_eqv_congr_left (l * a) (l * (-b)) (-(l * b)) (Q'.mul_neg_eqv l b)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h1 h2)

/-- `a·(s·b) ≃ s·(a·b)` — the scalar-commute used for `Dv_smul` and the `RC`
scale/mul lemmas. -/
theorem q_mul_swap_left (a s b : Q') : (a * (s * b)).eqv (s * (a * b)) := by
  have h1 : (a * (s * b)).eqv ((a * s) * b) := Q'.eqv_symm (Q'.mul_assoc_eqv a s b)
  have h2 : ((a * s) * b).eqv ((s * a) * b) :=
    Q'.mul_eqv_congr_right (a * s) (s * a) b (Q'.mul_comm_eqv a s)
  have h3 : ((s * a) * b).eqv (s * (a * b)) := Q'.mul_assoc_eqv s a b
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- `(s·a)·(s·b) ≃ (s·s)·(a·b)` — the squared-scalar regroup for `parseval_Tsq`. -/
theorem q_scale_both (s a b : Q') : ((s * a) * (s * b)).eqv ((s * s) * (a * b)) := by
  have h1 : ((s * a) * (s * b)).eqv (s * (a * (s * b))) := Q'.mul_assoc_eqv s a (s * b)
  have h2 : (s * (a * (s * b))).eqv (s * (s * (a * b))) :=
    Q'.mul_eqv_congr_left s (a * (s * b)) (s * (a * b)) (q_mul_swap_left a s b)
  have h3 : (s * (s * (a * b))).eqv ((s * s) * (a * b)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv s s (a * b))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-! ## 1. The rational Euclidean base module `charSmulGNS` (GENUINE) -/

/-- **The rational Euclidean base module.**  `V = Nat → Q'`, `⟨a,b⟩ = Σ_{s<N} a_s·b_s`
(a CReal-free rational finite sum).  Every field is the `finSum` lift of the
single-coordinate `qWeightGNS`/`qSmulGNS` algebra. -/
def charSmulGNS (N : Nat) : SmulGNSData where
  V := Nat → Q'
  veq := fun a b => ∀ s, (a s).eqv (b s)
  veq_refl := fun _ s => Q'.eqv_refl _
  veq_symm := fun h s => Q'.eqv_symm (h s)
  veq_trans := fun h1 h2 s => Q'.eqv_trans _ _ _ (h1 s) (h2 s)
  zero := fun _ => 0
  add := fun a b s => a s + b s
  neg := fun a s => -(a s)
  smul := fun c a s => c * a s
  add_congr := fun ha hb s => QPoly.q_add_congr (ha s) (hb s)
  neg_congr := fun {a a'} h s => Q'.neg_eqv_congr (a s) (a' s) (h s)
  smul_congr := fun c {a a'} h s => Q'.mul_eqv_congr_left c (a s) (a' s) (h s)
  add_assoc := fun a b c s => Q'.add_assoc_eqv (a s) (b s) (c s)
  add_comm := fun a b s => Q'.add_comm_eqv (a s) (b s)
  zero_add := fun a s => QPoly.q_zero_add_eqv (a s)
  neg_add := fun a s => Q'.neg_add_self_eqv (a s)
  B := fun a b => RationalTail.finSum (fun s => a s * b s) N
  B_congr_left := fun {a a'} b h =>
    RationalTail.finSum_eqv_congr (fun s => a s * b s) (fun s => a' s * b s)
      (fun s => Q'.mul_eqv_congr_right (a s) (a' s) (b s) (h s)) N
  B_add_left := fun a b c =>
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr (fun s => (a s + b s) * c s)
        (fun s => a s * c s + b s * c s)
        (fun s => QPoly.q_add_mul (a s) (b s) (c s)) N)
      (RationalTail.finSum_add (fun s => a s * c s) (fun s => b s * c s) N)
  B_smul_left := fun c a b =>
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr (fun s => (c * a s) * b s)
        (fun s => c * (a s * b s))
        (fun s => Q'.mul_assoc_eqv c (a s) (b s)) N)
      (Q'.eqv_symm (RationalTail.const_mul_finSum (fun s => a s * b s) c N))
  B_symm := fun a b =>
    RationalTail.finSum_eqv_congr (fun s => a s * b s) (fun s => b s * a s)
      (fun s => Q'.mul_comm_eqv (a s) (b s)) N
  self_nonneg := fun a => by
    have h := CharacterTail.finSum_le_termwise (fun _ => (0 : Q'))
      (fun s => a s * a s) (fun s => SumOfSquares.q_mul_self_nonneg (a s)) N
    rw [RationalTail.finSum_zero_seq N] at h
    exact h
  smul_sub := fun c a b s =>
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (a s) (-(b s)))
      (Q'.add_eqv_congr_left (c * a s) (c * (-(b s))) (-(c * b s)) (Q'.mul_neg_eqv c (b s)))

/-! ## 2. The diagonal λ-symbol `charDiagonalSymbol` (GENUINE) -/

/-- The diagonal carrier map `Dv a = (λ_s·a_s)`, `λ_s = qpow w (c4 (s+1))`. -/
def charDv (w : Q') : (Nat → Q') → (Nat → Q') :=
  fun a s => qpow w (c4 (s + 1)) * a s

/-- **The diagonal transfer symbol.**  The five `DiagonalTransferSymbol` fields are
per-coordinate rationals; the contraction `distSqQ_Dv` is the `finSum` lift of
`q_sq_scale_le` (`0 ≤ λ_s ≤ 1` from `qpow_nonneg`/`qpow_le_one`). -/
def charDiagonalSymbol (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    DiagonalTransferSymbol (charSmulGNS N) where
  Dv := charDv w
  Dv_congr := fun {a b} h s =>
    Q'.mul_eqv_congr_left (qpow w (c4 (s + 1))) (a s) (b s) (h s)
  distSqQ_Dv := fun a b => by
    refine CharacterTail.finSum_le_termwise _ _ (fun k => ?_) N
    refine OSReconstructionProgress.le_of_eqv_le
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          ((qpow w (c4 (k + 1)) * a k) + -(qpow w (c4 (k + 1)) * b k))
          (qpow w (c4 (k + 1)) * (a k + -(b k)))
          ((qpow w (c4 (k + 1)) * a k) + -(qpow w (c4 (k + 1)) * b k))
          (q_mul_sub_distrib (qpow w (c4 (k + 1))) (a k) (b k)))
        (Q'.mul_eqv_congr_left
          (qpow w (c4 (k + 1)) * (a k + -(b k)))
          ((qpow w (c4 (k + 1)) * a k) + -(qpow w (c4 (k + 1)) * b k))
          (qpow w (c4 (k + 1)) * (a k + -(b k)))
          (q_mul_sub_distrib (qpow w (c4 (k + 1))) (a k) (b k))))
      (WilsonSchurIdentities.q_sq_scale_le (qpow w (c4 (k + 1))) (a k + -(b k))
        (qpow_nonneg w hw0 (c4 (k + 1)))
        (HeatKernelGap.qpow_le_one hw0 hw1 (c4 (k + 1))))
  Dv_add := fun a b s => Q'.mul_add_eqv (qpow w (c4 (s + 1))) (a s) (b s)
  Dv_smul := fun c a s => q_mul_swap_left (qpow w (c4 (s + 1))) c (a s)

/-! ## 3. The `RC` scale/mul rearrangements (GENUINE) -/

/-- `RCnonneg (a·a)` — the `RC` square is nonnegative. -/
theorem RCmul_self_nonneg (a : CReal.RC) : CReal.RCnonneg (CReal.RCmul a a) := by
  refine Quotient.inductionOn a ?_
  intro A
  rw [CReal.RCmul_mk]
  exact rcnonneg_mk_of_geRat
    (ExpPos.geRat_of_eventually ⟨0, fun n _ => SumOfSquares.q_mul_self_nonneg (A.approx n)⟩)

/-- `(s·a)·b = s·(a·b)` in `RC` (pull the scalar left through the product). -/
theorem RCmul_scale_left (s : Q') (a b : CReal.RC) :
    CReal.RCmul (CReal.RCscale s a) b = CReal.RCscale s (CReal.RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  show Quotient.mk CReal.crealSetoid (CReal.mul (CReal.mul (CReal.ofQ' s) A) B)
      = Quotient.mk CReal.crealSetoid (CReal.mul (CReal.ofQ' s) (CReal.mul A B))
  exact Quotient.sound (CRealAlg.cmul_assoc (CReal.ofQ' s) A B)

/-- `a·(s·b) = s·(a·b)` in `RC` (pull the scalar out of the right factor). -/
theorem RCmul_scale_right (s : Q') (a b : CReal.RC) :
    CReal.RCmul a (CReal.RCscale s b) = CReal.RCscale s (CReal.RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  show Quotient.mk CReal.crealSetoid (CReal.mul A (CReal.mul (CReal.ofQ' s) B))
      = Quotient.mk CReal.crealSetoid (CReal.mul (CReal.ofQ' s) (CReal.mul A B))
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_mul_swap_left (A.approx n) s (B.approx n)))

/-- `(s·a)·(s·b) = (s·s)·(a·b)` in `RC` (the squared-scalar regroup). -/
theorem RCmul_scale_both (s : Q') (a b : CReal.RC) :
    CReal.RCmul (CReal.RCscale s a) (CReal.RCscale s b)
      = CReal.RCscale (s * s) (CReal.RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  show Quotient.mk CReal.crealSetoid
      (CReal.mul (CReal.mul (CReal.ofQ' s) A) (CReal.mul (CReal.ofQ' s) B))
      = Quotient.mk CReal.crealSetoid (CReal.mul (CReal.ofQ' (s * s)) (CReal.mul A B))
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_scale_both s (A.approx n) (B.approx n)))

/-! ## 4. The sole residual: `FinEuclCompletionCoords` (named, not faked) -/

/-- **The RC-diagonal resolution of the finite-dimensional canonical completion.**
The completion of `Q^N` under `d² = Σ (a−b)²` is `RC^N` (it contains genuine
irrational CReal-limit points), so the completion points are NOT all embedded
coordinate vectors — the correct, sharpest single identification is this
finite-dimensional `RC`-coordinatization:

  * `proj` — the `RC`-coordinate projection (`z ↦ (⟦coordinate i of a Cauchy rep⟧)`,
    total and 1-Lipschitz since `|a_i−b_i|² ≤ d²(a,b)`);
  * `resolve` — the completion inner product IS the standard `RC`-Euclidean form
    `⟨z,z'⟩ = Σ_i (proj z i)·(proj z' i)`;
  * `proj_T` — `T = diag(λ_i)`: `proj (T z) i = λ_i·(proj z i)`.

Both clauses are choice-free finite-dimensional constructive-completion facts,
provable on the dense image via `cinnerCompl_embed` + `TqSymb_embed` and extended
by coordinate continuity.  Named as `Type`-level data (Rule 8), never faked. -/
structure FinEuclCompletionCoords (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) : Type where
  /-- The `RC`-coordinate projection of a completion point. -/
  proj : GNSCompletionSpace (charSmulGNS N).toGNSData → Fin N → CReal.RC
  /-- The completion inner product is the standard `RC`-Euclidean form. -/
  resolve : ∀ z z',
    (charSmulGNS N).toGNSData.gnsComplete.hilbert.cinner z z'
      = CReal.RCfinSum N (fun i => CReal.RCmul (proj z i) (proj z' i))
  /-- `T` acts diagonally: `proj (T z) i = λ_i·(proj z i)`. -/
  proj_T : ∀ z i,
    proj ((charDiagonalSymbol w hw0 hw1 N).TqSymb z) i
      = CReal.RCscale (qpow w (c4 (i.val + 1))) (proj z i)

/-! ## 5. Assembly: `SymbolTypedParseval` from `FinEuclCompletionCoords` -/

/-- **The Option-2 target, discharged modulo `FinEuclCompletionCoords`.**  From an
`FinEuclCompletionCoords` datum, inhabit `SymbolTypedParseval w N`.  The four
`WilsonTowerParseval` fields are one-line `RCmul`/`RCscale` rearrangements:

  * `coeffSq z i := (proj z i)·(proj z i)`, nonneg by `RCmul_self_nonneg`;
  * `parseval_self := resolve z z`;
  * `parseval_T := resolve (T z) z` + `proj_T` + `RCmul_scale_left`;
  * `parseval_offdiag := resolve` twice + `proj_T` + `RCmul_scale_left/right`;
  * `parseval_Tsq := resolve (T z)(T z)` + `proj_T` + `RCmul_scale_both`. -/
def symbolTypedParsevalWilson (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (C : FinEuclCompletionCoords w hw0 hw1 N) :
    SymbolTypedParseval w N where
  D := charSmulGNS N
  S := charDiagonalSymbol w hw0 hw1 N
  R := rcScaleResidualPlus
  parseval :=
    { coeffSq := fun z i => CReal.RCmul (C.proj z i) (C.proj z i)
      coeffSq_nonneg := fun z i => RCmul_self_nonneg (C.proj z i)
      parseval_self := fun z => C.resolve z z
      parseval_T := fun z => by
        rw [C.resolve ((charDiagonalSymbol w hw0 hw1 N).TqSymb z) z]
        refine congrArg (CReal.RCfinSum N) (funext (fun i => ?_))
        rw [C.proj_T z i]
        exact RCmul_scale_left _ (C.proj z i) (C.proj z i)
      parseval_offdiag := fun z z' => by
        rw [C.resolve ((charDiagonalSymbol w hw0 hw1 N).TqSymb z) z',
            C.resolve z ((charDiagonalSymbol w hw0 hw1 N).TqSymb z')]
        refine congrArg (CReal.RCfinSum N) (funext (fun i => ?_))
        rw [C.proj_T z i, C.proj_T z' i, RCmul_scale_left, RCmul_scale_right]
      parseval_Tsq := fun z => by
        rw [C.resolve ((charDiagonalSymbol w hw0 hw1 N).TqSymb z)
              ((charDiagonalSymbol w hw0 hw1 N).TqSymb z)]
        refine congrArg (CReal.RCfinSum N) (funext (fun i => ?_))
        rw [C.proj_T z i]
        exact RCmul_scale_both _ (C.proj z i) (C.proj z i) }

end YMGap.Continuum.SymbolTypedParsevalClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SymbolTypedParsevalClose.charSmulGNS
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.charDiagonalSymbol
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.RCmul_self_nonneg
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.RCmul_scale_left
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.RCmul_scale_right
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.RCmul_scale_both
#print axioms YMGap.Continuum.SymbolTypedParsevalClose.symbolTypedParsevalWilson
