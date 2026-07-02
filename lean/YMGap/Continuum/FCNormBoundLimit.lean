/-
Retiring the last real data field of `ContinuousFCLimitData`: the operator-norm
bound `fcApply_normBound` (`‖f(T)x‖² ≤ M·‖x‖²`) is here PROVED as the diagonal
limit of the per-polynomial spectral bound, exactly mirroring how
`fcApply_selfAdjoint_limit` retired the self-adjointness field.

# What this module does (a sharp reduction of core ④-operator)

`ContinuousFCLimitData` carried BOTH `fcApply_selfAdjoint` and `fcApply_normBound`
as honest data.  The self-adjointness one is already a theorem
(`fcApply_selfAdjoint_limit`).  This module proves the norm-bound one:

  * `leEv_mul_nonneg_left` — a `CReal`-factor left-monotonicity of `leEv`
    (nonnegative `CReal` factor `F`), routed through the existing `mul_nonneg`
    and the distributivity `mul_sub`.
  * `leEv_of_convergesTo_le` — push a termwise `leEv` through two `CReal` limits
    (Helper 1; the `ε/4` chase of `leEv_of_ofQ'_limit_le`).
  * `convergesTo_of_sub_null` — assemble a limit from a null difference
    (Helper 2; `convergesTo_add` + `convergesTo_limit_congr`).
  * `diagInner_converges` — the load-bearing diagonal continuity
    `p ↦ ⟨zₚ,zₚ⟩ → ⟨z,z⟩` at a completion Cauchy limit, GIVEN a uniform bound
    `⟨zₚ,zₚ⟩ ≤ C` (Cauchy–Schwarz on the left leg + Atom C on the right).
  * `fcApply_normBound_limit` — the retirement theorem.

`CompleteFCLimitData` then carries ONLY the genuine per-polynomial spectral datum
`polyNormBound_termwise` (already discharged by `dischargeBTC`/`PolyNormData`),
and `dischargeBTC_complete` produces a `BoundedTransferCalculusResidual` off it.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.WilsonContinuousFC
import YMGap.Continuum.RCScaleClose
import YMGap.Constructive.CRealMulMono

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

/-! ## Part 1 — a `Q'` rearrangement bridge -/

namespace YMGap.Constructive.Q'

/-- `0 ≤ (X − Y) + ε ⟹ Y ≤ X + ε`. -/
theorem le_add_of_zero_le_sub_add {X Y ε : Q'} (h : (0 : Q') ≤ (X + -Y) + ε) :
    Y ≤ X + ε := by
  have h1 : -ε ≤ X + -Y := Q'.neg_le_of_zero_le_add h
  have h2 : -(X + -Y) ≤ -(-ε) := Q'.neg_le_neg h1
  have e1 : (-(X + -Y)).eqv (Y + -X) := by
    have a1 : (-(X + -Y)).eqv (-X + -(-Y)) := Q'.neg_add_eqv X (-Y)
    have a2 : (-X + -(-Y)).eqv (-X + Y) :=
      Q'.add_eqv_congr_left (-X) (-(-Y)) Y (Q'.neg_neg_eqv Y)
    have a3 : (-X + Y).eqv (Y + -X) := Q'.add_comm_eqv (-X) Y
    exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 a3)
  have e2 : (-(-ε)).eqv ε := Q'.neg_neg_eqv ε
  have h3 : Y + -X ≤ ε :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e2))
  exact Q'.le_add_of_sub_le h3

end YMGap.Constructive.Q'

/-! ## Part 2 — the three new `CReal` convergence/order lemmas -/

namespace YMGap.Constructive.CReal

/-- **Left-factor `leEv`-monotonicity for a nonnegative `CReal` factor.**
`0 ≤ F` (as `leEv czero F`) and `a ≤ b` give `F·a ≤ F·b`.  Routed through the
sign-free `mul_nonneg` and the distributivity `mul_sub` (no global bound needed). -/
theorem leEv_mul_nonneg_left {F a b : CReal}
    (hF : leEv czero F) (hab : leEv a b) :
    leEv (mul F a) (mul F b) := by
  -- (1) `b − a ≥ 0`.
  have hba : leEv czero (sub b a) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hab ε hε
    refine ⟨N, fun n hn => ?_⟩
    show (0 : Q') ≤ (b.approx n + -(a.approx n)) + ε
    have h0 : (0 : Q') ≤ (b.approx n + ε) + -(a.approx n) := Q'.sub_nonneg_of_le (hN n hn)
    have erearr : ((b.approx n + ε) + -(a.approx n)).eqv ((b.approx n + -(a.approx n)) + ε) := by
      have a1 := Q'.add_assoc_eqv (b.approx n) ε (-(a.approx n))
      have a2 : (b.approx n + (ε + -(a.approx n))).eqv (b.approx n + (-(a.approx n) + ε)) :=
        Q'.add_eqv_congr_left (b.approx n) (ε + -(a.approx n)) (-(a.approx n) + ε)
          (Q'.add_comm_eqv ε (-(a.approx n)))
      have a3 : (b.approx n + (-(a.approx n) + ε)).eqv ((b.approx n + -(a.approx n)) + ε) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (b.approx n) (-(a.approx n)) ε)
      exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 a3)
    exact Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv erearr)
  -- (2) `F·(b − a) ≥ 0`.
  have hFg : ExpPos.geRat F 0 := hF
  have hbag : ExpPos.geRat (sub b a) 0 := hba
  have hprod : leEv czero (mul F (sub b a)) := CReal.mul_nonneg hFg hbag
  -- (3) distribute: `F·b − F·a ≥ 0`.
  have hsub : leEv czero (sub (mul F b) (mul F a)) :=
    leEv_trans hprod (leEv_of_equiv (CReal.mul_sub F b a))
  -- (4) unpack to the goal.
  intro ε hε
  obtain ⟨N, hN⟩ := hsub ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (mul F a).approx n ≤ (mul F b).approx n + ε
  have hraw : (0 : Q') ≤ ((mul F b).approx n + -((mul F a).approx n)) + ε := hN n hn
  exact Q'.le_add_of_zero_le_sub_add hraw

/-- **Helper 1 — push a termwise `leEv` through two `CReal` limits.**
`a → A`, `b → B`, `∀ p, a p ≤ b p ⟹ A ≤ B`.  The `ε/4` chase of
`leEv_of_ofQ'_limit_le`, at the `CReal` (not `ofQ'`) level. -/
theorem leEv_of_convergesTo_le {a b : Nat → CReal} {A B : CReal}
    (hA : ConvergesTo a A) (hB : ConvergesTo b B)
    (hle : ∀ p, leEv (a p) (b p)) : leEv A B := by
  intro ε hε
  let q : Q' := HalfPow.half * (HalfPow.half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨NsA, hsA⟩ := hA q hqpos
  obtain ⟨NsB, hsB⟩ := hB q hqpos
  obtain ⟨NapxA, hclA⟩ := hsA (max NsA NsB) (Nat.le_max_left _ _)
  obtain ⟨NapxB, hclB⟩ := hsB (max NsA NsB) (Nat.le_max_right _ _)
  obtain ⟨Nc, hcl⟩ := hle (max NsA NsB) q hqpos
  refine ⟨max (max NapxA NapxB) Nc, fun n hn => ?_⟩
  have hnA : NapxA ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnB : NapxB ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnC : Nc ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨_, hAle⟩ := hclA n hnA     -- A_n ≤ (a P)_n + q
  obtain ⟨hBle, _⟩ := hclB n hnB     -- (b P)_n ≤ B_n + q
  have hMid : (a (max NsA NsB)).approx n ≤ (b (max NsA NsB)).approx n + q := hcl n hnC
  -- chain: A ≤ (aP)+q ≤ ((bP)+q)+q ≤ ((B+q)+q)+q  and  4q = ε (one pad)
  have chain3 : ∀ u v w z : Q', u ≤ v + q → v ≤ w + q → w ≤ z + q → u ≤ z + ε := by
    intro u v w z huv hvw hwz
    have s1 : u ≤ (w + q) + q := Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
    have s2 : u ≤ ((z + q) + q) + q :=
      Q'.le_trans' _ _ _ s1 (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hwz))
    refine Q'.le_trans' _ _ _ s2 ?_
    have hreassoc : (((z + q) + q) + q).eqv (z + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (z + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z q (q + q)) ?_
      exact Q'.add_eqv_congr_left z _ _ (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    have hpad : z + ((q + q) + q) ≤ z + (((q + q) + q) + q) :=
      Q'.add_le_add_left _ _ _ (Q'.add_le_self_of_nonneg ((q + q) + q) q (Q'.le_of_lt hqpos))
    refine Q'.le_trans' _ _ _ hpad ?_
    refine Q'.le_of_eqv (Q'.add_eqv_congr_left z _ _ ?_)
    have hqq : (q + q).eqv (HalfPow.half * ε) := ExpNeg.two_halves (HalfPow.half * ε)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (q + q) q q) ?_
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr hqq hqq) ?_
    exact ExpNeg.two_halves ε
  exact chain3 (A.approx n) ((a (max NsA NsB)).approx n) ((b (max NsA NsB)).approx n) (B.approx n)
    hAle hMid hBle

/-- `sub x czero ≈ x`. -/
theorem Equiv_sub_czero (x : CReal) : Equiv (sub x czero) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show (x.approx n + -(czero.approx n)).eqv (x.approx n)
    exact Q'.eqv_of_eq (Q'.sub_zero' (x.approx n)))

/-- **Helper 2 — assemble a limit from a null difference.**
`(a − b) → 0`, `b → L ⟹ a → L`. -/
theorem convergesTo_of_sub_null {a b : Nat → CReal} {L : CReal}
    (hnull : ConvergesTo (fun p => sub (a p) (b p)) czero)
    (hb : ConvergesTo b L) : ConvergesTo a L := by
  have hadd : ConvergesTo (fun p => add (sub (a p) (b p)) (b p)) (add czero L) :=
    CReal.convergesTo_add hnull hb
  have hcong : ConvergesTo a (add czero L) :=
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (fun p => SumOfSquares.Equiv_of_approx_eqv (fun n => by
        -- ((a p) − (b p)) + (b p) ≈ (a p)
        show (((a p).approx n + -((b p).approx n)) + (b p).approx n).eqv ((a p).approx n)
        have e1 := Q'.add_assoc_eqv ((a p).approx n) (-((b p).approx n)) ((b p).approx n)
        have e2 : ((a p).approx n + (-((b p).approx n) + (b p).approx n)).eqv
            ((a p).approx n + 0) :=
          Q'.add_eqv_congr_left ((a p).approx n) _ 0 (Q'.neg_add_self_eqv ((b p).approx n))
        have e3 : ((a p).approx n + (0 : Q')) = (a p).approx n := Q'.add_zero' ((a p).approx n)
        exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_of_eq e3)))) hadd
  refine convergesTo_limit_congr hcong ?_
  exact SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show ((czero.approx n) + L.approx n).eqv (L.approx n)
    exact Q'.eqv_of_eq (Q'.zero_add' (L.approx n)))

end YMGap.Constructive.CReal

/-! ## Part 3 — the diagonal inner-product continuity -/

namespace YMGap.Continuum.FCNormBoundLimit

open YMGap.Continuum.GNSQuotient.GNSData
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.HamiltonianScalar

/-- **Diagonal continuity of the inner product at a completion Cauchy limit.**
For `X : GeneralCompletionCauchy D`, GIVEN a uniform `RC`-order bound
`⟨X.pt p, X.pt p⟩ ≤ C` by a FIXED `CReal` `C` (globally `|C.approx| ≤ Bc`), the
diagonal `p ↦ ⟨X.pt p, X.pt p⟩` converges to `⟨X.lim, X.lim⟩`.

Right leg is Atom C (`cinnerRep_continuous_right`); the left leg's squared bound
is Cauchy–Schwarz `⟨Δp,zₚ⟩² ≤ ⟨Δp,Δp⟩·⟨zₚ,zₚ⟩ ≤ ⟨Δp,Δp⟩·C`, the last step being
`leEv_mul_nonneg_left` fed the uniform bound; then `⟨Δp,Δp⟩·C → 0` (Atom B). -/
theorem diagInner_converges (D : GNSData) (X : GeneralCompletionCauchy D) (C : CReal)
    (Bc : Q') (hBc0 : (0 : Q') ≤ Bc) (hBc : ∀ n, Q'.abs (C.approx n) ≤ Bc)
    (hbdd : ∀ p, CReal.leEv (D.cinnerRep (X.pt p) (X.pt p)) C) :
    CReal.ConvergesTo (fun p => D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim X.lim) := by
  -- Right leg (Atom C).
  have hR : CReal.ConvergesTo (fun p => D.cinnerRep X.lim (X.pt p)) (D.cinnerRep X.lim X.lim) :=
    D.cinnerRep_continuous_right X X.lim
  -- Left leg: sub (⟨zₚ,zₚ⟩) (⟨z,zₚ⟩) → czero.
  have hL : CReal.ConvergesTo
      (fun p => CReal.sub (D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim (X.pt p)))
      CReal.czero := by
    -- eₚ = ⟨Δp,Δp⟩·C is null (Atom B, after commuting to C·⟨Δp,Δp⟩).
    have hCnull : CReal.ConvergesTo
        (fun p => CReal.mul C
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))) CReal.czero :=
      CReal.convergesTo_null_mul_const C Bc hBc0 hBc (D.cinnerRep_diffSelf_null X)
    have henull : CReal.ConvergesTo
        (fun p => CReal.mul
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim)) C) CReal.czero :=
      YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
        (fun p => CRealAlg.cmul_comm C
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))) hCnull
    refine CReal.convergesTo_of_sqDiff_le_null
      (A := CReal.czero)
      (e := fun p => CReal.mul
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim)) C) ?_ henull
    intro p
    -- Step (a): sub (aSeq p) czero ≈ ⟨Δp,zₚ⟩.
    have hstepa : CReal.Equiv
        (CReal.sub (D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim (X.pt p)))
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p)) :=
      CReal.Equiv.symm (D.cinnerRep_sub_left_equiv (X.pt p) X.lim (X.pt p))
    have hL0 : CReal.Equiv
        (CReal.sub (CReal.sub (D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim (X.pt p)))
          CReal.czero)
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p)) :=
      CReal.Equiv.trans (CReal.Equiv_sub_czero _) hstepa
    have hLsq : CReal.Equiv
        (CReal.mul
          (CReal.sub (CReal.sub (D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim (X.pt p)))
            CReal.czero)
          (CReal.sub (CReal.sub (D.cinnerRep (X.pt p) (X.pt p)) (D.cinnerRep X.lim (X.pt p)))
            CReal.czero))
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p))
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p))) :=
      CReal.Equiv.trans (CReal.mul_congr_left hL0)
        (YMGap.Constructive.TrigSignedAdd.mul_congr_right hL0)
    -- Cauchy–Schwarz on ⟦Δp⟧, ⟦zₚ⟧ (descends by defeq).
    have hcs : CReal.leEv
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p))
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p)))
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))
          (D.cinnerRep (X.pt p) (X.pt p))) :=
      D.RC_cauchy_schwarz (Quotient.mk (cauchySetoid D) (D.subCauchy (X.pt p) X.lim))
        (Quotient.mk (cauchySetoid D) (X.pt p))
    -- ⟨Δp,Δp⟩ ≥ 0.
    have hΔnn : CReal.leEv CReal.czero
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim)) :=
      CReal.leEv_ofQ'_of_approx_ge (fun _ => D.self_nonneg _)
    -- micro-lemma + (†_p): ⟨Δp,Δp⟩·⟨zₚ,zₚ⟩ ≤ ⟨Δp,Δp⟩·C.
    have hmicro : CReal.leEv
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))
          (D.cinnerRep (X.pt p) (X.pt p)))
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim)) C) :=
      CReal.leEv_mul_nonneg_left hΔnn (hbdd p)
    have hchain : CReal.leEv
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p))
          (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (X.pt p)))
        (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim)) C) :=
      CReal.leEv_trans hcs hmicro
    exact CReal.leEv_trans (CReal.leEv_of_equiv hLsq) hchain
  -- Assemble the two legs (Helper 2).
  exact CReal.convergesTo_of_sub_null hL hR

end YMGap.Continuum.FCNormBoundLimit

/-! ## Part 4 — the retirement theorem and the discharge -/

namespace YMGap.Continuum.FCNormBoundLimit

open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient.GNSData
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.WilsonContinuousFC
open YMGap.Continuum.FCLimitContinuity

/-- **`fcApply` operator-norm bound — PROVED, unconditionally from the termwise
spectral bound.**  For a polynomial sequence `pseq`, a per-point supplier `img`,
and the per-polynomial bound `‖pₚ(T)x‖² ≤ M·‖x‖²`, the carrier limit
`fcApply (img ·) = lim_n pₙ(T)·` satisfies `‖f(T)x‖² ≤ M·‖x‖²`.  This is exactly
the `fcApply_normBound` field of `ContinuousFCLimitData`, now a theorem. -/
theorem fcApply_normBound_limit (SL : LinearSmulGNSData)
    (L : AdditiveTransferOperator SL.toGNSData) (pseq : Nat → QPoly.Poly)
    (img : ∀ x : GNSCompletionSpace SL.toGNSData, PolyImageCauchy SL L pseq x)
    (M : Q')
    (hbound : ∀ (p : Nat) (x : GNSCompletionSpace SL.toGNSData),
      RCle (SL.toGNSData.cinnerCompl (polyApply SL.toSmulGNSData L (pseq p) x)
              (polyApply SL.toSmulGNSData L (pseq p) x))
           (RCscale M (SL.toGNSData.cinnerCompl x x)))
    (x : GNSCompletionSpace SL.toGNSData) :
    RCle (SL.toGNSData.cinnerCompl (fcApply (img x)) (fcApply (img x)))
         (RCscale M (SL.toGNSData.cinnerCompl x x)) := by
  refine Quotient.inductionOn x ?_
  intro xrep
  -- abbreviations
  let D := SL.toGNSData
  let xc : GNSCompletionSpace D := Quotient.mk (cauchySetoid D) xrep
  let X : GeneralCompletionCauchy D := (img xc).toGeneralCompletionCauchy
  let C : CReal := CReal.mul (CReal.ofQ' M) (D.cinnerRep xrep xrep)
  -- the uniform per-`p` bound (†_p): ⟨X.pt p, X.pt p⟩ ≤ C.
  have hdagger : ∀ p, CReal.leEv (D.cinnerRep (X.pt p) (X.pt p)) C := by
    intro p
    have h := hbound p xc
    rw [← (img xc).represents p] at h
    exact h
  -- a global bound for C's approximations.
  obtain ⟨Bxx, hBxx0, hBxx⟩ := (D.cInnerQCauchy xrep xrep).globalBound
  have hBc : ∀ n, Q'.abs (C.approx n) ≤ Q'.abs M * Bxx := by
    intro n
    show Q'.abs (M * (D.cinnerRep xrep xrep).approx n) ≤ Q'.abs M * Bxx
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le M ((D.cinnerRep xrep xrep).approx n)) ?_
    refine Q'.mul_le_mul_of_nonneg_left (Q'.abs ((D.cinnerRep xrep xrep).approx n)) Bxx
      (Q'.abs M) ?_ (Q'.abs_nonneg M)
    exact hBxx (CReal.QMhat (D.cInnerSeq xrep xrep) (D.cInnerQCauchy xrep xrep) n)
  have hBc0 : (0 : Q') ≤ Q'.abs M * Bxx := Q'.mul_nonneg _ _ (Q'.abs_nonneg M) hBxx0
  -- Step 1 (diagonal continuity) and Step 2 (push ≤ through the limit).
  have hStep1 : CReal.ConvergesTo (fun p => D.cinnerRep (X.pt p) (X.pt p))
      (D.cinnerRep X.lim X.lim) :=
    diagInner_converges D X C (Q'.abs M * Bxx) hBc0 hBc hdagger
  have hstar : CReal.leEv (D.cinnerRep X.lim X.lim) C :=
    CReal.leEv_of_convergesTo_le hStep1 (CReal.convergesTo_const C) hdagger
  -- the goal is defeq to (★): leEv ⟨X.lim,X.lim⟩ C.
  exact hstar

/-- **The slim continuous-`f` calculus datum.**  Carries only the genuine
per-polynomial spectral bound `polyNormBound_termwise`; the self-adjointness and
operator-norm limit facts are now theorems. -/
structure CompleteFCLimitData (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model) : Type where
  /-- The polynomial sequence approximating `f`. -/
  pseq : Nat → QPoly.Poly
  /-- Per-point supplier: `n ↦ pₙ(T)x` as a distance-Cauchy sequence. -/
  img : ∀ x : GNSCompletionSpace SL.toGNSData,
    PolyImageCauchy SL LT.toAdditiveTransferOperator pseq x
  /-- The uniform squared operator-norm bound `M = (sup|f|)²`. -/
  normSqBound : Q'
  /-- **The per-polynomial spectral bound** `‖pₚ(T)x‖² ≤ M·‖x‖²` (already
  discharged by `dischargeBTC`/`PolyNormData`). -/
  polyNormBound_termwise : ∀ (p : Nat) (x : GNSCompletionSpace SL.toGNSData),
    RCle (SL.toGNSData.cinnerCompl
            (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (pseq p) x)
            (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (pseq p) x))
         (RCscale normSqBound (SL.toGNSData.cinnerCompl x x))

/-- **Upgrade to `ContinuousFCLimitData`** — both derivable fields become
theorems, leaving only `polyNormBound_termwise` as carried data. -/
def toContinuousFCLimitData (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model)
    (Cd : CompleteFCLimitData SL LT model gap) :
    ContinuousFCLimitData SL LT model gap where
  pseq := Cd.pseq
  img := Cd.img
  normSqBound := Cd.normSqBound
  fcApply_selfAdjoint := fcApply_selfAdjoint_limit SL LT.toAdditiveTransferOperator Cd.pseq Cd.img
  fcApply_normBound :=
    fcApply_normBound_limit SL LT.toAdditiveTransferOperator Cd.pseq Cd.img Cd.normSqBound
      Cd.polyNormBound_termwise

/-- **DISCHARGE of `BoundedTransferCalculusResidual` off the slim datum.** -/
def dischargeBTC_complete (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model)
    (Cd : CompleteFCLimitData SL LT model gap) :
    BoundedTransferCalculus.BoundedTransferCalculusResidual
      (spectralGapDataOfL SL.toSmulGNSData LT.toAdditiveTransferOperator model gap) :=
  dischargeBTC_limit SL LT model gap (toContinuousFCLimitData SL LT model gap Cd)

end YMGap.Continuum.FCNormBoundLimit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.le_add_of_zero_le_sub_add
#print axioms YMGap.Constructive.CReal.leEv_mul_nonneg_left
#print axioms YMGap.Constructive.CReal.leEv_of_convergesTo_le
#print axioms YMGap.Constructive.CReal.convergesTo_of_sub_null
#print axioms YMGap.Continuum.FCNormBoundLimit.diagInner_converges
#print axioms YMGap.Continuum.FCNormBoundLimit.fcApply_normBound_limit
#print axioms YMGap.Continuum.FCNormBoundLimit.dischargeBTC_complete
