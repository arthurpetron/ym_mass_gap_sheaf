/-
Inhabiting `SymbolTypedParsevalClose.FinEuclCompletionCoords` — the sole residual
that closes `SymbolTypedParseval` and makes `wilsonLinearTransfer` unconditional
over its own weight-1 witness.

# What this module delivers (all GENUINE, axiom-clean)

The completion of the rational Euclidean base module `charSmulGNS N` under
`d² = Σ_{s<N} (a_s − b_s)²` is the finite-dimensional `RC^N`.  The three data of
`FinEuclCompletionCoords` are constructed here from a SINGLE new inequality:

  * **`finSum_ge_term` / `coordSq_le_distSqQ`** (the one genuinely new lemma) —
    single-coordinate domination of the `finSum`: `(a_i − b_i)² ≤ d²(a,b)`.  This
    is the 1-Lipschitz continuity of each coordinate functional.

  * **`coordCauchy` / `projCR` / `proj`** — the `RC`-coordinate projection, total
    and well-defined on the completion (`Equiv_of_ofQ'_limit_close`), reindexing
    the `distSqQ` modulus at `ε²` through the square-reflection.

  * **`proj_T`** — `T = diag(λ_i)` acts diagonally:
    `proj (T z) i = λ_i · (proj z i)`, `λ_i = qpow w (c4 (i+1))`.  The
    `cinnerCompl_cSmul_left` proof shape (a scalar limit `convergesTo_constMul`).

  * **`resolve`** — the completion inner product IS the standard `RC`-Euclidean
    form `⟨z,z'⟩ = Σ_i (proj z i)·(proj z' i)`.  Finite-dimensional continuity of
    the inner product, summed over the `N` coordinates: `RCfinSum` collapses to a
    single class (`RCfinSum_mk`), whose CReal `csumFin` is the coordinate-summed
    product limit (`convergesTo_csumFin` folding `convergesTo_mul`), termwise equal
    to `ofQ'` of the rational inner-product sequence (`csumFin_approx_finSum`).

`finEuclCompletionCoords` bundles these into `FinEuclCompletionCoords`, and
`symbolTypedParseval` feeds it to the already-proved `symbolTypedParsevalWilson`
to inhabit `SymbolTypedParseval w N`.

# Honesty (AGENTS.md Rule 6)

This is the WEIGHT-1 tower — an existence witness over its own `charSmulGNS N`,
`charDiagonalSymbol`, not a `√μ`-fidelity match to the interacting `E_Λ` moment
functional (the module header of `SymbolTypedParsevalClose` scopes this caveat).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.SymbolTypedParsevalClose
import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Constructive.CRealSum

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SymbolTypedParsevalClose

namespace YMGap.Continuum.FinEuclCompletionCoordsClose

/-! ## L0 — single-term domination of `finSum` (the ONE new inequality) -/

/-- A finite sum of nonnegatives is nonnegative. -/
theorem finSum_nonneg (f : Nat → Q') (h : ∀ k, (0 : Q') ≤ f k) :
    ∀ m, (0 : Q') ≤ RationalTail.finSum f m
  | 0 => by show (0 : Q') ≤ RationalTail.finSum f 0; exact Q'.le_refl' 0
  | m + 1 => by
      show (0 : Q') ≤ RationalTail.finSum f m + f m
      exact Q'.zero_le_add _ _ (finSum_nonneg f h m) (h m)

/-- **The one new lemma.**  A single term is dominated by the whole (nonnegative)
finite sum: `f i ≤ Σ_{s<m} f s` for `i < m`. -/
theorem finSum_ge_term (f : Nat → Q') (h : ∀ k, (0 : Q') ≤ f k) :
    ∀ (m i : Nat), i < m → f i ≤ RationalTail.finSum f m
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, i, hi => by
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
      · rw [heq]
        show f m ≤ RationalTail.finSum f m + f m
        exact le_of_le_eqv
          (Q'.add_le_self_of_nonneg (f m) (RationalTail.finSum f m) (finSum_nonneg f h m))
          (Q'.add_comm_eqv (f m) (RationalTail.finSum f m))
      · show f i ≤ RationalTail.finSum f m + f m
        exact Q'.le_trans' _ _ _ (finSum_ge_term f h m i hlt)
          (Q'.add_le_self_of_nonneg (RationalTail.finSum f m) (f m) (h m))

/-- **Coordinate domination.**  `(a_i − b_i)² ≤ d²(a,b)` on the rational
Euclidean base module. -/
theorem coordSq_le_distSqQ (N : Nat) (a b : Nat → Q') (i : Fin N) :
    ((a i.val + -(b i.val)) * (a i.val + -(b i.val)))
      ≤ (charSmulGNS N).toGNSData.distSqQ a b :=
  finSum_ge_term (fun s => (a s + -(b s)) * (a s + -(b s)))
    (fun _ => SumOfSquares.q_mul_self_nonneg _) N i.val i.isLt

/-! ## L1 / L2 — the coordinate Cauchy datum and the RC-projection -/

/-- The `i`-th coordinate rational sequence of a completion representative. -/
def coordSeq {N : Nat} (x : CauchyGNS (charSmulGNS N).toGNSData) (i : Fin N) : Nat → Q' :=
  fun n => (x.seq n) i.val

/-- The coordinate sequence is `Q'`-Cauchy — its modulus reindexes `x`'s at `ε²`,
and the square-reflection turns `(Δ_i)² ≤ ε²` into `|Δ_i| ≤ ε`. -/
def coordCauchy {N : Nat} (x : CauchyGNS (charSmulGNS N).toGNSData) (i : Fin N) :
    CReal.QCauchy (coordSeq x i) where
  M := fun ε => x.modulus (ε * ε)
  bound := fun ε hε p q hp hq =>
    Q'.two_sided_of_abs_sub_le
      (Q'.abs_le_of_sq_le_sq hε
        (Q'.le_trans' _ _ _ (coordSq_le_distSqQ N (x.seq p) (x.seq q) i)
          (x.isCauchy (ε * ε) (Q'.mul_pos hε hε) p q hp hq)))

/-- The `i`-th coordinate `CReal` of a completion representative. -/
def projCR {N : Nat} (x : CauchyGNS (charSmulGNS N).toGNSData) (i : Fin N) : CReal :=
  CReal.ofQ'CauchySeq (coordSeq x i) (coordCauchy x i)

/-- The `i`-th coordinate as an `RC`-class. -/
def projRep {N : Nat} (x : CauchyGNS (charSmulGNS N).toGNSData) (i : Fin N) : CReal.RC :=
  Quotient.mk crealSetoid (projCR x i)

/-- The coordinate class respects `CauchyNull` (1-Lipschitz coordinate continuity,
the `cinnerRep_welldef` shape). -/
theorem projRep_welldef {N : Nat} (i : Fin N)
    {x x' : CauchyGNS (charSmulGNS N).toGNSData}
    (h : CauchyNull (charSmulGNS N).toGNSData x x') : projRep x i = projRep x' i :=
  Quotient.sound (CReal.Equiv_of_ofQ'_limit_close
    (CReal.convergesTo_ofQ'CauchySeq (coordSeq x i) (coordCauchy x i))
    (CReal.convergesTo_ofQ'CauchySeq (coordSeq x' i) (coordCauchy x' i))
    (fun ε hε => by
      obtain ⟨M, hM⟩ := h (ε * ε) (Q'.mul_pos hε hε)
      exact ⟨M, fun n hn => Q'.two_sided_of_abs_sub_le
        (Q'.abs_le_of_sq_le_sq hε
          (Q'.le_trans' _ _ _ (coordSq_le_distSqQ N (x.seq n) (x'.seq n) i) (hM n hn)))⟩))

/-- **The RC-coordinate projection of a completion point.** -/
def proj {N : Nat} :
    GNSCompletionSpace (charSmulGNS N).toGNSData → Fin N → CReal.RC :=
  fun z i => Quotient.liftOn z (fun x => projRep x i) (fun _ _ h => projRep_welldef i h)

/-! ## The `RC`/`CReal` finite-sum bridges -/

/-- Fin-indexed `CReal` finite sum, mirroring `RCfinSum`'s recursion. -/
def csumFin : (m : Nat) → (Fin m → CReal) → CReal
  | 0, _ => CReal.czero
  | m + 1, g => CReal.add (csumFin m (fun i => g i.castSucc)) (g (Fin.last m))

/-- `RCfinSum` of coordinate classes collapses to one class of `csumFin`. -/
theorem RCfinSum_mk : ∀ (m : Nat) (g : Fin m → CReal),
    CReal.RCfinSum m (fun i => Quotient.mk crealSetoid (g i))
      = Quotient.mk crealSetoid (csumFin m g)
  | 0, _ => rfl
  | m + 1, g => by
      show CReal.RCadd
            (CReal.RCfinSum m (fun i => Quotient.mk crealSetoid (g i.castSucc)))
            (Quotient.mk crealSetoid (g (Fin.last m)))
          = Quotient.mk crealSetoid
              (CReal.add (csumFin m (fun i => g i.castSucc)) (g (Fin.last m)))
      rw [RCfinSum_mk m (fun i => g i.castSucc), CReal.RCadd_mk]

/-- The approximations of a `csumFin` of coordinate products are the rational
`finSum` of the products. -/
theorem csumFin_approx_finSum (a b : Nat → Q') (k : Nat) :
    ∀ m, (csumFin m (fun i : Fin m =>
              CReal.mul (CReal.ofQ' (a i.val)) (CReal.ofQ' (b i.val)))).approx k
      = RationalTail.finSum (fun s => a s * b s) m
  | 0 => rfl
  | m + 1 => by
      show (csumFin m (fun i : Fin m =>
                CReal.mul (CReal.ofQ' (a i.val)) (CReal.ofQ' (b i.val)))).approx k
              + a m * b m
          = RationalTail.finSum (fun s => a s * b s) m + a m * b m
      rw [csumFin_approx_finSum a b k m]

/-- Fin-indexed additivity of `ConvergesTo` for `csumFin`. -/
theorem convergesTo_csumFin : ∀ (m : Nat) (S : Fin m → Nat → CReal) (lim : Fin m → CReal),
    (∀ i, CReal.ConvergesTo (S i) (lim i)) →
    CReal.ConvergesTo (fun M => csumFin m (fun i => S i M)) (csumFin m lim)
  | 0, _, _, _ => by
      intro ε hε
      refine ⟨0, fun _ _ => ⟨0, fun n _ => ?_⟩⟩
      show (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
        ∧ (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
      exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε),
             Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)⟩
  | m + 1, S, lim, h => by
      have ih := convergesTo_csumFin m (fun i => S i.castSucc) (fun i => lim i.castSucc)
        (fun i => h i.castSucc)
      exact CReal.convergesTo_add ih (h (Fin.last m))

/-! ## L3 helper — per-coordinate product limit -/

/-- The product of the constant coordinate liftings converges to the product of
the coordinate limits (`convergesTo_mul`, fed the uniform coordinate bounds). -/
theorem termConv (N : Nat) (x y : CauchyGNS (charSmulGNS N).toGNSData) (i : Fin N) :
    CReal.ConvergesTo
      (fun M => CReal.mul (CReal.ofQ' (coordSeq x i M)) (CReal.ofQ' (coordSeq y i M)))
      (CReal.mul (projCR x i) (projCR y i)) := by
  obtain ⟨Bx, _, hBx⟩ := (coordCauchy x i).globalBound
  obtain ⟨By, _, hBy⟩ := (coordCauchy y i).globalBound
  exact CReal.convergesTo_mul (B := Q'.max' Bx By)
    (Q'.le_trans' _ _ _ (Q'.abs_nonneg _)
      (Q'.le_trans' _ _ _ (hBx 0) (Q'.le_max'_left Bx By)))
    (fun k _ => Q'.le_trans' _ _ _ (hBx k) (Q'.le_max'_left Bx By))
    (fun n => Q'.le_trans' _ _ _
      (hBy (CReal.QMhat (coordSeq y i) (coordCauchy y i) n)) (Q'.le_max'_right Bx By))
    (CReal.convergesTo_ofQ'CauchySeq (coordSeq x i) (coordCauchy x i))
    (CReal.convergesTo_ofQ'CauchySeq (coordSeq y i) (coordCauchy y i))

/-! ## L3 — the diagonal intertwiner `proj (T z) = λ · proj z` -/

/-- **`T = diag(λ_i)`.**  `proj (T z) i = λ_i · (proj z i)`,
`λ_i = qpow w (c4 (i+1))` — the `cinnerCompl_cSmul_left` limit shape. -/
theorem proj_T (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat)
    (z : GNSCompletionSpace (charSmulGNS N).toGNSData) (i : Fin N) :
    proj ((charDiagonalSymbol w hw0 hw1 N).TqSymb z) i
      = CReal.RCscale (qpow w (c4 (i.val + 1))) (proj z i) := by
  refine Quotient.inductionOn z ?_
  intro x
  show Quotient.mk crealSetoid
        (CReal.ofQ'CauchySeq (coordSeq ((charDiagonalSymbol w hw0 hw1 N).cDiagCauchy x) i)
          (coordCauchy ((charDiagonalSymbol w hw0 hw1 N).cDiagCauchy x) i))
      = CReal.RCscale (qpow w (c4 (i.val + 1)))
          (Quotient.mk crealSetoid (CReal.ofQ'CauchySeq (coordSeq x i) (coordCauchy x i)))
  rw [CReal.RCscale_mk]
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ' (coordSeq ((charDiagonalSymbol w hw0 hw1 N).cDiagCauchy x) i n))
    (bSeq := fun n => CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
                        (CReal.ofQ' (coordSeq x i n)))
    (fun n => CReal.Equiv_of_approx_eq (fun _ => rfl))
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_constMul (qpow w (c4 (i.val + 1)))
      (CReal.convergesTo_ofQ'CauchySeq (coordSeq x i) (coordCauchy x i)))

/-! ## L4 — the completion inner product = standard RC-Euclidean form -/

/-- **The Parseval resolution.**  `⟨z,z'⟩ = Σ_{i<N} (proj z i)·(proj z' i)` on the
completion — finite-dimensional continuity of the inner product. -/
theorem resolve (N : Nat) (z z' : GNSCompletionSpace (charSmulGNS N).toGNSData) :
    (charSmulGNS N).toGNSData.gnsComplete.hilbert.cinner z z'
      = CReal.RCfinSum N (fun i => CReal.RCmul (proj z i) (proj z' i)) := by
  refine Quotient.inductionOn₂ z z' ?_
  intro x y
  show Quotient.mk crealSetoid ((charSmulGNS N).toGNSData.cinnerRep x y)
      = CReal.RCfinSum N (fun i => CReal.RCmul (projRep x i) (projRep y i))
  refine (Quotient.sound (?_ : CReal.Equiv ((charSmulGNS N).toGNSData.cinnerRep x y)
            (csumFin N (fun i => CReal.mul (projCR x i) (projCR y i))))).trans
    (RCfinSum_mk N (fun i => CReal.mul (projCR x i) (projCR y i))).symm
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun M => CReal.ofQ' ((charSmulGNS N).toGNSData.cInnerSeq x y M))
    (bSeq := fun M => csumFin N (fun i =>
              CReal.mul (CReal.ofQ' (coordSeq x i M)) (CReal.ofQ' (coordSeq y i M))))
    (fun M => CReal.Equiv_of_approx_eq
      (fun k => (csumFin_approx_finSum (x.seq M) (y.seq M) k N).symm))
    (CReal.convergesTo_ofQ'CauchySeq ((charSmulGNS N).toGNSData.cInnerSeq x y)
      ((charSmulGNS N).toGNSData.cInnerQCauchy x y))
    (convergesTo_csumFin N
      (fun i M => CReal.mul (CReal.ofQ' (coordSeq x i M)) (CReal.ofQ' (coordSeq y i M)))
      (fun i => CReal.mul (projCR x i) (projCR y i))
      (fun i => termConv N x y i))

/-! ## Assembly -/

/-- **The sole residual, discharged.**  `FinEuclCompletionCoords` is inhabited by
the constructed projection, its diagonal intertwiner, and the Parseval
resolution. -/
def finEuclCompletionCoords (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) : SymbolTypedParsevalClose.FinEuclCompletionCoords w hw0 hw1 N where
  proj := proj
  resolve := resolve N
  proj_T := proj_T w hw0 hw1 N

/-- **`SymbolTypedParseval w N`, unconditional over its weight-1 witness.**
Feeds the discharged residual to the already-proved assembly. -/
def symbolTypedParseval (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    WilsonParsevalExt.SymbolTypedParseval w N :=
  SymbolTypedParsevalClose.symbolTypedParsevalWilson w hw0 hw1 N
    (finEuclCompletionCoords w hw0 hw1 N)

end YMGap.Continuum.FinEuclCompletionCoordsClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.finSum_ge_term
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.coordSq_le_distSqQ
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.coordCauchy
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.projRep_welldef
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.proj
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.RCfinSum_mk
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.csumFin_approx_finSum
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.convergesTo_csumFin
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.termConv
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.proj_T
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.resolve
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.finEuclCompletionCoords
#print axioms YMGap.Continuum.FinEuclCompletionCoordsClose.symbolTypedParseval
