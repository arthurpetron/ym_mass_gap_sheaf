/-
Inner-product LIMIT-CONTINUITY on the constructive GNS completion — the analytic
core that passes self-adjointness (and the norm bound) of a polynomial sequence
`pₙ(T)` through the carrier limit `fcApply = lim_n pₙ(T)x`.

# What this module adds (all axiom-clean)

`Continuum/RCCauchySchwarz.lean` proved the RC-valued Cauchy–Schwarz inequality,
`Continuum/RCDistBridge.lean` the difference-inner identity `cinnerRep (u−v)(u−v)
= ofQ'CauchySeq (distSqQ …)`, and `Continuum/ContinuousFCCarrierLimit.lean` the
carrier limit `fcApply` with its representative squared-distance convergence.
The remaining OPERATOR-side residual named in those modules ("RC inner product
deliberately undeveloped" / "inner-product continuity") is exactly the statement
that the completed inner product is CONTINUOUS in each slot at a carrier limit.
This module proves that continuity from the already-green pieces.

  * **Atom A — left-slot negation / subtraction of `cinnerCompl`.**  `RCneg` /
    `RCsub` on `RC = CReal/Equiv`, the rep-level `cinnerRep_sub_left_equiv`
    (`⟨u−v, w⟩ ≈ ⟨u,w⟩ − ⟨v,w⟩`, descended from `B_add_left`+`B_neg_left`), and its
    completion-level form `cinnerCompl_cNeg_left` / `cinnerCompl_cSub_left`.

  * **Atom B — a null·bounded product helper.**  `convergesTo_null_mul_const`:
    a fixed `CReal` factor `F` with a uniform approximation bound times a
    null sequence is null.  Specialises the green `convergesTo_mul`.

  * **Atom C — the squared→linear packaging (the one genuinely-new step).**
    `convergesTo_of_sqDiff_le_null`: from `(aₚ − A)² ≤ eₚ`, `eₚ → 0`, conclude
    `aₚ → A` sqrt-free (via `le_of_sq_le_sq` applied approximation-wise).  Combined
    with Cauchy–Schwarz, the difference identity, the null modulus of the
    representative squared distance (`carrierLimit_converges`), and Atom B, this
    yields the left- and right-slot continuity `cinnerRep_continuous_left` /
    `cinnerRep_continuous_right` at a general completion Cauchy limit.

  * **Retirement.**  `fcApply_selfAdjoint_limit`: the carrier limit
    `fcApply = lim_n pₙ(T)x` is self-adjoint, UNCONDITIONALLY, from the termwise
    `polyApply_selfAdjoint` and the two-slot continuity — retiring the
    `fcApply_selfAdjoint` field of `ContinuousFCLimitData` to a proved theorem.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.ContinuousFCCarrierLimit
import YMGap.Constructive.Sqrt
import YMGap.Constructive.TrigAddCReal
import YMGap.Constructive.TrigSignedAdd

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ContinuousFCCarrierLimit

/-! ## Part 0 — a small rational two-sided-bound helper

The rearrangements `Q'.le_add_of_sub_le`, `Q'.neg_sub_eqv`, `Q'.abs_mul_self_eqv`
and `Q'.abs_le_of_sq_le_sq` already live in `Continuum/GNSHilbertSpace.lean`; we
reuse them and add only the trivial two-sided reading of `|d| ≤ ε`. -/

namespace YMGap.Constructive.Q'

/-- From `|d| ≤ ε`: both `d ≤ ε` and `-d ≤ ε`. -/
theorem abs_le_two_sided {d ε : Q'} (h : Q'.abs d ≤ ε) : d ≤ ε ∧ -d ≤ ε :=
  ⟨Q'.le_trans' _ _ _ (Q'.le_abs_self d) h, Q'.le_trans' _ _ _ (Q'.neg_le_abs d) h⟩

end YMGap.Constructive.Q'

/-! ## Part 1 — the real-quotient negation `RCneg` / subtraction `RCsub` -/

namespace YMGap.Constructive.CReal

/-- **Negation on the real quotient** `RC = CReal/Equiv`. -/
def RCneg : RC → RC :=
  Quotient.lift (s := crealSetoid) (fun a => Quotient.mk crealSetoid (neg a))
    (fun _ _ h => Quotient.sound (neg_congr h))

@[simp] theorem RCneg_mk (a : CReal) :
    RCneg (Quotient.mk crealSetoid a) = Quotient.mk crealSetoid (neg a) := rfl

/-- **Subtraction on the real quotient** `a − b := a + (−b)`. -/
def RCsub (a b : RC) : RC := RCadd a (RCneg b)

@[simp] theorem RCsub_mk (a b : CReal) :
    RCsub (Quotient.mk crealSetoid a) (Quotient.mk crealSetoid b)
      = Quotient.mk crealSetoid (sub a b) := rfl

/-! ## Part 2 — three `CReal` convergence closure lemmas -/

/-- **Negation preserves convergence.**  `s → A ⟹ n ↦ neg (s n) → neg A`. -/
theorem convergesTo_neg {s : Nat → CReal} {A : CReal} (h : ConvergesTo s A) :
    ConvergesTo (fun N => neg (s N)) (neg A) := by
  intro ε hε
  obtain ⟨Nst, hst⟩ := h ε hε
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨P, hP⟩ := hst N hN
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hP n hn
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- **Limit-side `Equiv` transport.**  `s → L`, `L ≈ L' ⟹ s → L'`. -/
theorem convergesTo_limit_congr {s : Nat → CReal} {L L' : CReal}
    (h : ConvergesTo s L) (e : Equiv L L') : ConvergesTo s L' := by
  intro ε hε
  have hh : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nst, hst⟩ := h (HalfPow.half * ε) hh
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨P1, hP1⟩ := hst N hN
  obtain ⟨P2, hP2⟩ := e (HalfPow.half * ε) hh
  refine ⟨max P1 P2, fun n hn => ?_⟩
  have hn1 : P1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : P2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := hP1 n hn1     -- s N ≤ L + h·ε , L ≤ s N + h·ε
  obtain ⟨he1, he2⟩ := hP2 n hn2     -- L ≤ L' + h·ε , L' ≤ L + h·ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hs1
      (Q'.add_le_add_right _ _ (HalfPow.half * ε) he1)) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L'.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L'.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ he2
      (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs2)) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((s N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((s N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-- **The constant sequence converges to its value.** -/
theorem convergesTo_const (F : CReal) : ConvergesTo (fun _ => F) F :=
  fun ε hε => ⟨0, fun _ _ => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (F.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (F.approx n) ε (Q'.le_of_lt hε)⟩⟩⟩

/-- **Atom B.**  A fixed `CReal` factor `F` (uniformly bounded by `B` on
approximations) times a null sequence is null. -/
theorem convergesTo_null_mul_const {g : Nat → CReal} (F : CReal) (B : Q')
    (hB : (0 : Q') ≤ B) (hFb : ∀ n, Q'.abs (F.approx n) ≤ B)
    (hg : ConvergesTo g czero) :
    ConvergesTo (fun p => mul F (g p)) czero := by
  have hmul : ConvergesTo (fun p => mul F (g p)) (mul F czero) :=
    convergesTo_mul (B := B) hB (fun _ n => hFb n)
      (fun n => by
        show Q'.abs ((czero).approx n) ≤ B
        show Q'.abs (0 : Q') ≤ B
        unfold Q'.abs; rw [if_pos (Q'.le_refl' 0)]; exact hB)
      (convergesTo_const F) hg
  refine convergesTo_limit_congr hmul ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (F.approx n * (czero).approx n).eqv ((czero).approx n)
  show (F.approx n * (0 : Q')).eqv (0 : Q')
  exact Q'.mul_zero_eqv (F.approx n)

/-- **Atom C — squared→linear packaging (the one genuinely-new step).**
From `(aₚ − A)² ≤ eₚ` (as `leEv`) and `eₚ → 0`, conclude `aₚ → A`.  No square
root is taken: at each approximation index the rational squared bound is turned
into a linear bound via `le_of_sq_le_sq`. -/
theorem convergesTo_of_sqDiff_le_null {a : Nat → CReal} {A : CReal} {e : Nat → CReal}
    (hsq : ∀ p, leEv (mul (sub (a p) A) (sub (a p) A)) (e p))
    (he : ConvergesTo e czero) :
    ConvergesTo a A := by
  intro ε hε
  have hεε : (0 : Q') < ε * ε := Q'.mul_pos hε hε
  have hγ : (0 : Q') < HalfPow.half * (ε * ε) := ExpNeg.half_mul_pos _ hεε
  obtain ⟨S, hS⟩ := he (HalfPow.half * (ε * ε)) hγ
  refine ⟨S, fun N hN => ?_⟩
  obtain ⟨Pe, hPe⟩ := hS N hN
  obtain ⟨M, hM⟩ := hsq N (HalfPow.half * (ε * ε)) hγ
  refine ⟨max Pe M, fun n hn => ?_⟩
  have hnPe : Pe ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- squared bound from hsq (d := (a N).approx n + -(A.approx n), via defeq of mul/sub approx)
  have hsqn : ((a N).approx n + -(A.approx n)) * ((a N).approx n + -(A.approx n))
      ≤ (e N).approx n + HalfPow.half * (ε * ε) := hM n hnM
  -- e N upper bound from convergence to czero
  have heN : (e N).approx n ≤ HalfPow.half * (ε * ε) := by
    have hraw := (hPe n hnPe).1
    exact le_of_le_eqv hraw (Q'.eqv_of_eq (Q'.zero_add' (HalfPow.half * (ε * ε))))
  -- d² ≤ (half·ε²)+(half·ε²) = ε²
  have hd2 : ((a N).approx n + -(A.approx n)) * ((a N).approx n + -(A.approx n)) ≤ ε * ε := by
    refine le_of_le_eqv (Q'.le_trans' _ _ _ hsqn
      (Q'.add_le_add_right _ _ (HalfPow.half * (ε * ε)) heN)) ?_
    exact ExpNeg.two_halves (ε * ε)
  -- |d| ≤ ε, then two-sided
  have hdabs : Q'.abs ((a N).approx n + -(A.approx n)) ≤ ε := Q'.abs_le_of_sq_le_sq hε hd2
  obtain ⟨hup, hlo⟩ := Q'.abs_le_two_sided hdabs
  refine ⟨?_, ?_⟩
  · -- (a N).approx n ≤ A.approx n + ε
    exact Q'.le_add_of_sub_le hup
  · -- A.approx n ≤ (a N).approx n + ε
    have hlo' : A.approx n + -((a N).approx n) ≤ ε :=
      le_of_eqv_le (Q'.eqv_symm (Q'.neg_sub_eqv ((a N).approx n) (A.approx n))) hlo
    exact Q'.le_add_of_sub_le hlo'

end YMGap.Constructive.CReal

/-! ## Part 3 — Atom A (completion-level) and inner-product symmetry -/

namespace YMGap.Continuum.GNSQuotient.GNSData

open YMGap.Constructive.CReal

variable (D : GNSData)

/-- **Atom A (representative level).**  `⟨u−v, w⟩ ≈ ⟨u,w⟩ − ⟨v,w⟩`, descended from
`B_add_left` + `B_neg_left` through `Equiv_of_limit_of_equal`. -/
theorem cinnerRep_sub_left_equiv (u v w : CauchyGNS D) :
    CReal.Equiv (D.cinnerRep (D.subCauchy u v) w)
      (CReal.sub (D.cinnerRep u w) (D.cinnerRep v w)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq (D.subCauchy u v) w N))
    (bSeq := fun N => CReal.add (ofQ' (D.cInnerSeq u w N)) (CReal.neg (ofQ' (D.cInnerSeq v w N))))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_add (CReal.convergesTo_ofQ'CauchySeq _ _)
      (CReal.convergesTo_neg (CReal.convergesTo_ofQ'CauchySeq _ _)))
  intro N
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- LHS approx = B (u+(-v)) w ; RHS approx = B u w + -(B v w)
  refine Q'.eqv_trans _ _ _ (D.B_add_left (u.seq N) (D.neg (v.seq N)) (w.seq N)) ?_
  exact Q'.add_eqv_congr_left (D.B (u.seq N) (w.seq N))
    (D.B (D.neg (v.seq N)) (w.seq N)) (-(D.B (v.seq N) (w.seq N)))
    (D.B_neg_left (v.seq N) (w.seq N))

/-- **Left-slot negation of the completed inner product.**
`⟨−x, y⟩ = −⟨x, y⟩` on `RC`. -/
theorem cinnerCompl_cNeg_left (x y : GNSCompletionSpace D) :
    D.cinnerCompl (D.cNeg x) y = RCneg (D.cinnerCompl x y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq (D.cNegCauchy a) b N))
    (bSeq := fun N => CReal.neg (ofQ' (D.cInnerSeq a b N)))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_neg (CReal.convergesTo_ofQ'CauchySeq _ _))
  intro N
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  exact D.B_neg_left (a.seq N) (b.seq N)

/-- **Left-slot subtraction of the completed inner product.**
`⟨x−y, w⟩ = ⟨x,w⟩ − ⟨y,w⟩` on `RC`. -/
theorem cinnerCompl_cSub_left (x y w : GNSCompletionSpace D) :
    D.cinnerCompl (D.cSub x y) w = RCsub (D.cinnerCompl x w) (D.cinnerCompl y w) := by
  refine Quotient.inductionOn₃ x y w ?_
  intro a b c
  apply Quotient.sound
  exact D.cinnerRep_sub_left_equiv a b c

/-- **Symmetry of the representative inner product.**  `⟨x,y⟩ ≈ ⟨y,x⟩`. -/
theorem cinnerRep_comm (x y : CauchyGNS D) :
    CReal.Equiv (D.cinnerRep x y) (D.cinnerRep y x) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq x y N))
    (bSeq := fun N => ofQ' (D.cInnerSeq y x N))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro N
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  exact D.B_symm (x.seq N) (y.seq N)

/-! ## Part 4 — Atom C: inner-product limit-continuity at a carrier limit -/

/-- **Step (c) — the null modulus of the representative squared distance.**
`p ↦ ⟨Δp, Δp⟩ → 0` where `Δp = (X.pt p) − X.lim`, from `carrierLimit_converges`
(each squared distance `→ 0`) and `distSqQ ≥ 0`. -/
theorem cinnerRep_diffSelf_null (X : GeneralCompletionCauchy D) :
    ConvergesTo (fun p => D.cinnerRep (D.subCauchy (X.pt p) X.lim)
      (D.subCauchy (X.pt p) X.lim)) czero := by
  intro ε hε
  obtain ⟨P0, hP0⟩ := ContinuousFCCarrierLimit.carrierLimit_converges X ε hε
  refine ⟨P0, fun p hp => ?_⟩
  obtain ⟨N, hN⟩ := hP0 p hp
  refine ⟨N, fun k hk => ?_⟩
  -- the reindex the completion inner uses
  have hidx : N ≤ CReal.QMhat (fun n => D.distSqQ ((X.pt p).seq n) (X.lim.seq n))
      (D.distSqSeqCauchy (X.pt p) X.lim) k :=
    Nat.le_trans hk (CReal.self_le_QMhat _ _ k)
  have hbound : D.distSqQ ((X.pt p).seq (CReal.QMhat (fun n => D.distSqQ ((X.pt p).seq n)
        (X.lim.seq n)) (D.distSqSeqCauchy (X.pt p) X.lim) k))
      (X.lim.seq (CReal.QMhat (fun n => D.distSqQ ((X.pt p).seq n) (X.lim.seq n))
        (D.distSqSeqCauchy (X.pt p) X.lim) k)) ≤ ε :=
    hN _ hidx
  have hnn : (0 : Q') ≤ D.distSqQ ((X.pt p).seq (CReal.QMhat (fun n => D.distSqQ
        ((X.pt p).seq n) (X.lim.seq n)) (D.distSqSeqCauchy (X.pt p) X.lim) k))
      (X.lim.seq (CReal.QMhat (fun n => D.distSqQ ((X.pt p).seq n) (X.lim.seq n))
        (D.distSqSeqCauchy (X.pt p) X.lim) k)) :=
    D.self_nonneg _
  refine ⟨?_, ?_⟩
  · exact le_of_le_eqv hbound (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' ε)))
  · exact Q'.le_trans' _ _ _ hnn
      (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

/-- **Atom C (left slot).**  The completed inner product is continuous in the
LEFT slot at a completion Cauchy limit:
`p ↦ ⟨X.pt p, W⟩ → ⟨X.lim, W⟩`. -/
theorem cinnerRep_continuous_left (X : GeneralCompletionCauchy D) (W : CauchyGNS D) :
    ConvergesTo (fun p => D.cinnerRep (X.pt p) W) (D.cinnerRep X.lim W) := by
  -- uniform bound on ⟨W,W⟩'s approximations
  obtain ⟨B, hB0, hB⟩ := (D.cInnerQCauchy W W).globalBound
  -- e p := ⟨W,W⟩ · ⟨Δp,Δp⟩ is null (Atom B on the step-(c) null modulus)
  have henull : ConvergesTo (fun p => CReal.mul (D.cinnerRep W W)
      (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))) czero :=
    CReal.convergesTo_null_mul_const (D.cinnerRep W W) B hB0
      (fun n => hB (CReal.QMhat (D.cInnerSeq W W) (D.cInnerQCauchy W W) n))
      (D.cinnerRep_diffSelf_null X)
  -- squared bound per p via Cauchy–Schwarz + Atom A difference identity
  refine CReal.convergesTo_of_sqDiff_le_null (e := fun p => CReal.mul (D.cinnerRep W W)
      (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))) ?_ henull
  intro p
  -- Cauchy–Schwarz on ⟦Δp⟧, ⟦W⟧ (descended to reps by defeq)
  have hcs : CReal.leEv
      (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) W)
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) W))
      (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))
        (D.cinnerRep W W)) :=
    D.RC_cauchy_schwarz (Quotient.mk (cauchySetoid D) (D.subCauchy (X.pt p) X.lim))
      (Quotient.mk (cauchySetoid D) W)
  -- step (a): sub (⟨pt p,W⟩) (⟨lim,W⟩) ≈ ⟨Δp,W⟩
  have hstepa : CReal.Equiv (CReal.sub (D.cinnerRep (X.pt p) W) (D.cinnerRep X.lim W))
      (D.cinnerRep (D.subCauchy (X.pt p) X.lim) W) :=
    CReal.Equiv.symm (D.cinnerRep_sub_left_equiv (X.pt p) X.lim W)
  -- square the Equiv
  have hLeq : CReal.Equiv
      (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) W)
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) W))
      (CReal.mul (CReal.sub (D.cinnerRep (X.pt p) W) (D.cinnerRep X.lim W))
        (CReal.sub (D.cinnerRep (X.pt p) W) (D.cinnerRep X.lim W))) := by
    have h := CReal.Equiv.symm hstepa
    exact CReal.Equiv.trans (CReal.mul_congr_left h)
      (YMGap.Constructive.TrigSignedAdd.mul_congr_right h)
  -- commute the RHS product
  have hReq : CReal.Equiv
      (CReal.mul (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))
        (D.cinnerRep W W))
      (CReal.mul (D.cinnerRep W W)
        (D.cinnerRep (D.subCauchy (X.pt p) X.lim) (D.subCauchy (X.pt p) X.lim))) :=
    CRealAlg.cmul_comm _ _
  exact (CReal.leEv_congr hLeq hReq).mp hcs

/-- **Atom C (right slot).**  `p ↦ ⟨W, X.pt p⟩ → ⟨W, X.lim⟩`, from the left-slot
continuity through the representative symmetry `cinnerRep_comm`. -/
theorem cinnerRep_continuous_right (X : GeneralCompletionCauchy D) (W : CauchyGNS D) :
    ConvergesTo (fun p => D.cinnerRep W (X.pt p)) (D.cinnerRep W X.lim) := by
  have hleft := D.cinnerRep_continuous_left X W
  have hseq := YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (fun p => D.cinnerRep_comm (X.pt p) W) hleft
  exact CReal.convergesTo_limit_congr hseq (D.cinnerRep_comm X.lim W)

end YMGap.Continuum.GNSQuotient.GNSData

/-! ## Part 5 — retiring the `fcApply_selfAdjoint` field to a proved theorem

The carrier limit `fcApply (img x) = lim_n pₙ(T)x` is self-adjoint,
UNCONDITIONALLY, from the termwise `polyApply_selfAdjoint` and the two-slot
inner-product continuity of Atom C.  This discharges the `fcApply_selfAdjoint`
field of `ContinuousFCLimitData` (`Continuum/WilsonContinuousFC.lean`) — no data
residual remains for it. -/

namespace YMGap.Continuum.FCLimitContinuity

open YMGap.Continuum
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.GNSQuotient.GNSData

/-- **`fcApply` self-adjointness — PROVED, unconditionally.**  For a polynomial
sequence `pseq` and a per-point `PolyImageCauchy` supplier `img`, the carrier
limit `fcApply (img ·) = lim_n pₙ(T)·` satisfies
`⟨f(T)x, y⟩ = ⟨x, f(T)y⟩`.  Termwise this is `polyApply_selfAdjoint`; passing the
two limits through is Atom C's `cinnerRep_continuous_left` / `_right`.  This is
exactly the `fcApply_selfAdjoint` field of `ContinuousFCLimitData`, now a
theorem. -/
theorem fcApply_selfAdjoint_limit (SL : LinearSmulGNSData)
    (L : AdditiveTransferOperator SL.toGNSData) (pseq : Nat → QPoly.Poly)
    (img : ∀ x : GNSCompletionSpace SL.toGNSData, PolyImageCauchy SL L pseq x)
    (x y : GNSCompletionSpace SL.toGNSData) :
    SL.toGNSData.cinnerCompl (fcApply (img x)) y
      = SL.toGNSData.cinnerCompl x (fcApply (img y)) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun p => SL.toGNSData.cinnerRep
      ((img (Quotient.mk (cauchySetoid SL.toGNSData) a)).toGeneralCompletionCauchy.pt p) b)
    (bSeq := fun p => SL.toGNSData.cinnerRep a
      ((img (Quotient.mk (cauchySetoid SL.toGNSData) b)).toGeneralCompletionCauchy.pt p))
    ?_
    (SL.toGNSData.cinnerRep_continuous_left
      (img (Quotient.mk (cauchySetoid SL.toGNSData) a)).toGeneralCompletionCauchy b)
    (SL.toGNSData.cinnerRep_continuous_right
      (img (Quotient.mk (cauchySetoid SL.toGNSData) b)).toGeneralCompletionCauchy a)
  intro p
  -- termwise self-adjointness of pₚ(T), descended to representatives
  have hpsa := polyApply_selfAdjoint SL.toSmulGNSData L (pseq p)
    (Quotient.mk (cauchySetoid SL.toGNSData) a) (Quotient.mk (cauchySetoid SL.toGNSData) b)
  rw [← (img (Quotient.mk (cauchySetoid SL.toGNSData) a)).represents p,
      ← (img (Quotient.mk (cauchySetoid SL.toGNSData) b)).represents p] at hpsa
  exact Quotient.exact hpsa

end YMGap.Continuum.FCLimitContinuity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.abs_le_two_sided
#print axioms YMGap.Constructive.CReal.RCneg
#print axioms YMGap.Constructive.CReal.RCsub
#print axioms YMGap.Constructive.CReal.convergesTo_neg
#print axioms YMGap.Constructive.CReal.convergesTo_limit_congr
#print axioms YMGap.Constructive.CReal.convergesTo_const
#print axioms YMGap.Constructive.CReal.convergesTo_null_mul_const
#print axioms YMGap.Constructive.CReal.convergesTo_of_sqDiff_le_null
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_sub_left_equiv
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_cNeg_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_cSub_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_comm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_diffSelf_null
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_continuous_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_continuous_right
#print axioms YMGap.Continuum.FCLimitContinuity.fcApply_selfAdjoint_limit
