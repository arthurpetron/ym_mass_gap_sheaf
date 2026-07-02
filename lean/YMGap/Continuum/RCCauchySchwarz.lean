/-
The completed real-quotient product `RCmul` and the **RC-valued Cauchy–Schwarz
inequality** on the constructive GNS completion.

# What this module proves (all GENUINE, axiom-clean)

Working in the genuine constructive real line `RC = CReal / Equiv` and the
completed GNS inner product `cinnerCompl : GNSCompletionSpace D → … → RC`:

  * `RCmul` — the descended product on `RC`, well-defined by the two-sided
    congruence `Pivot2.mul_congr` (a mechanical `Quotient.lift₂`); with
    `RCmul_mk` and `RCmul_comm`.

  * `leEv_of_ofQ'_limit_le` — the ONE-SIDED monotone-limit principle: if the
    lifted rational sequences `n ↦ ofQ' (r n)`, `n ↦ ofQ' (r′ n)` converge to
    `A`, `B` and `r ≤ r′` eventually to every tolerance, then `leEv A B`.  A
    one-directional clone of `Equiv_of_ofQ'_limit_close`.

  * `QCauchy.globalBound` — a UNIFORM bound `∀ n, |r n| ≤ B` for a rational
    Cauchy datum (prefix-max ∪ post-modulus tail), the input that
    `convergesTo_mul`'s global-boundedness hypotheses require (`localBound`
    only gives a post-cutoff range).

  * `RC_cauchy_schwarz` — for `z w` in the completion,
    `⟨z,w⟩·⟨z,w⟩ ≤ ⟨z,z⟩·⟨w,w⟩` in `RC`.  Assembled from the termwise
    pre-Hilbert Cauchy–Schwarz `D.cauchy_schwarz`, the two product-limit
    identifications via `convergesTo_mul`, and the monotone-limit principle.

The termwise input `f n · f n ≤ g n · h n` (with `f = ⟨xₙ,yₙ⟩`, `g = ⟨xₙ,xₙ⟩`,
`h = ⟨yₙ,yₙ⟩`) is `D.cauchy_schwarz` verbatim, so `hle` is discharged with `N=0`
(pad-free).  This is the RC-valued inner-product continuity payoff
`|⟨z,w⟩| ≤ ‖z‖·‖w‖` on the completion.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.Pivot2Moments
import YMGap.Constructive.CRealExp
import YMGap.Constructive.RegularCRealArith

open YMGap.Constructive

namespace YMGap.Constructive

namespace Q'

/-! ## `Q'` helpers: monotone running max and an absolute-value tail bound -/

/-- **The running maximum is monotone.**  `a ≤ b → runningMax f a ≤ runningMax f b`. -/
theorem runningMax_mono (f : Nat → Q') {a b : Nat} (h : a ≤ b) :
    Q'.runningMax f a ≤ Q'.runningMax f b := by
  induction b with
  | zero =>
    have ha : a = 0 := Nat.le_zero.mp h
    subst ha; exact Q'.le_refl' _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Q'.le_trans' _ _ _ (ih (Nat.lt_succ_iff.mp hlt)) (Q'.le_runningMax_succ f b)
    · have hab : a = b + 1 := Nat.le_antisymm h hge
      subst hab; exact Q'.le_refl' _

/-- **Tail absolute-value bound.**  From the two-sided one-slack bounds
`a ≤ c + 1`, `c ≤ a + 1` conclude `|a| ≤ |c| + 1`. -/
theorem abs_le_abs_add_one_of_bounds {a c : Q'}
    (h1 : a ≤ c + 1) (h2 : c ≤ a + 1) : Q'.abs a ≤ Q'.abs c + 1 := by
  apply Q'.abs_le
  · -- -(|c| + 1) ≤ a
    -- lower bound on c:  -(|c|) ≤ c
    have hc : -(Q'.abs c) ≤ c :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs c)) (Q'.le_of_eqv (Q'.neg_neg_eqv c))
    -- (a + 1) + -1 ≃ a
    have ecancel : ((a + 1) + -1).eqv a := by
      have e1 := Q'.add_assoc_eqv a 1 (-1)
      have e2 : (a + (1 + -1)).eqv (a + 0) :=
        Q'.add_eqv_congr_left a (1 + -1) 0 (Q'.add_neg_self_eqv 1)
      rw [Q'.add_zero' a] at e2
      exact Q'.eqv_trans _ _ _ e1 e2
    -- c + -1 ≤ a
    have hca : c + -1 ≤ a :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right c (a + 1) (-1) h2) (Q'.le_of_eqv ecancel)
    -- -(|c|) + -1 ≤ c + -1 ≤ a
    have hstep : -(Q'.abs c) + -1 ≤ a :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-1) hc) hca
    -- -(|c| + 1) ≃ -(|c|) + -1
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_add_eqv (Q'.abs c) 1)) hstep
  · -- a ≤ |c| + 1
    exact Q'.le_trans' _ _ _ h1 (Q'.add_le_add_right c (Q'.abs c) 1 (Q'.le_abs_self c))

end Q'

namespace CReal

/-! ## The uniform bound on a rational Cauchy datum -/

/-- **Global bound of a `QCauchy` rational sequence.**  `∃ B ≥ 0, ∀ n, |r n| ≤ B`.
Take the prefix-max over `n ≤ M 1` unioned with `|r (M 1)| + 1` (the post-modulus
tail bound from the `ε = 1` Cauchy step).  Unlike `localBound`, this bounds the
WHOLE sequence — the form `convergesTo_mul` requires. -/
theorem QCauchy.globalBound {r : Nat → Q'} (c : QCauchy r) :
    ∃ B : Q', (0 : Q') ≤ B ∧ ∀ n, Q'.abs (r n) ≤ B := by
  refine ⟨Q'.max' (Q'.runningMax (fun k => Q'.abs (r k)) (c.M 1)) (Q'.abs (r (c.M 1)) + 1),
    ?_, ?_⟩
  · -- 0 ≤ B
    refine Q'.le_trans' _ (Q'.abs (r (c.M 1)) + 1) _ ?_ (Q'.le_max'_right _ _)
    exact Q'.le_trans' _ (Q'.abs (r (c.M 1))) _ (Q'.abs_nonneg _)
      (Q'.add_le_self_of_nonneg _ 1 (by decide))
  · intro n
    rcases Nat.le_total n (c.M 1) with hle | hge
    · -- n ≤ M 1 : |r n| ≤ runningMax n ≤ runningMax (M 1) ≤ B
      refine Q'.le_trans' _ (Q'.runningMax (fun k => Q'.abs (r k)) (c.M 1)) _ ?_
        (Q'.le_max'_left _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_runningMax (fun k => Q'.abs (r k)) n)
        (Q'.runningMax_mono (fun k => Q'.abs (r k)) hle)
    · -- M 1 ≤ n : |r n| ≤ |r (M 1)| + 1 ≤ B
      obtain ⟨hb1, hb2⟩ := c.bound 1 (by decide) n (c.M 1) hge (Nat.le_refl _)
      refine Q'.le_trans' _ (Q'.abs (r (c.M 1)) + 1) _ ?_ (Q'.le_max'_right _ _)
      exact Q'.abs_le_abs_add_one_of_bounds hb1 hb2

/-! ## The one-sided monotone-limit principle -/

/-- **One-sided monotone limit.**  If `n ↦ ofQ' (r n) → A`, `n ↦ ofQ' (r′ n) → B`
and `r ≤ r′` eventually to every tolerance, then `leEv A B`.  A one-directional
clone of `Equiv_of_ofQ'_limit_close` (the `q = ε/4` chase, keeping only the
`A_n ≤ B_n + ε` half). -/
theorem leEv_of_ofQ'_limit_le {r r' : Nat → Q'} {A B : CReal}
    (hA : ConvergesTo (fun N => ofQ' (r N)) A)
    (hB : ConvergesTo (fun N => ofQ' (r' N)) B)
    (hle : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → r n ≤ r' n + ε) :
    leEv A B := by
  intro ε hε
  let q : Q' := HalfPow.half * (HalfPow.half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨NstA, hstA⟩ := hA q hqpos
  obtain ⟨NstB, hstB⟩ := hB q hqpos
  obtain ⟨Ncl, hcl⟩ := hle q hqpos
  let N : Nat := max (max NstA NstB) Ncl
  have hNA : NstA ≤ N := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hNB : NstB ≤ N := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hNcl : Ncl ≤ N := Nat.le_max_right _ _
  obtain ⟨NapxA, hclA⟩ := hstA N hNA
  obtain ⟨NapxB, hclB⟩ := hstB N hNB
  have hE1 : r N ≤ r' N + q := hcl N hNcl
  refine ⟨max NapxA NapxB, fun n hn => ?_⟩
  have hnA : NapxA ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnB : NapxB ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨_, hA2⟩ := hclA n hnA   -- A_n ≤ (ofQ' (r N))_n + q  (= r N + q)
  obtain ⟨hB1, _⟩ := hclB n hnB   -- (ofQ' (r′ N))_n ≤ B_n + q  (= r′ N ≤ B_n + q)
  -- chain: u ≤ v+q, v ≤ w+q, w ≤ z+q ⟹ u ≤ z + ε  (4q = ε, one pad)
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
  exact chain3 (A.approx n) (r N) (r' N) (B.approx n) hA2 hE1 hB1

/-! ## The descended product `RCmul` on `RC = CReal / Equiv` -/

/-- **The product on the real quotient.**  `RCmul ⟦a⟧ ⟦b⟧ = ⟦a·b⟧`, well-defined
by the two-sided congruence `Pivot2.mul_congr`. -/
def RCmul : RC → RC → RC :=
  Quotient.lift₂ (s₁ := crealSetoid) (s₂ := crealSetoid)
    (fun a b => Quotient.mk crealSetoid (CReal.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (YMGap.Continuum.Pivot2.mul_congr ha hb))

@[simp] theorem RCmul_mk (a b : CReal) :
    RCmul (Quotient.mk crealSetoid a) (Quotient.mk crealSetoid b)
      = Quotient.mk crealSetoid (CReal.mul a b) := rfl

/-- **`RCmul` is commutative**, from the pointwise `mul_comm_equiv`. -/
theorem RCmul_comm (a b : RC) : RCmul a b = RCmul b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (YMGap.Continuum.Pivot2.mul_comm_equiv x y)

end CReal

end YMGap.Constructive

/-! ## The RC-valued Cauchy–Schwarz inequality on the GNS completion -/

namespace YMGap.Continuum.GNSQuotient

open YMGap.Constructive

namespace GNSData

variable (D : GNSData)

/-- **RC-valued Cauchy–Schwarz.**  On the constructive GNS completion,
`⟨z,w⟩·⟨z,w⟩ ≤ ⟨z,z⟩·⟨w,w⟩` in `RC = CReal / Equiv`.

Reduce to representatives by `Quotient.inductionOn₂`; then `cinnerCompl`,
`RCmul`, `RCle` all compute to the aligned representative statement
`leEv (P·P) (Pxx·Pyy)` with `P = cinnerRep x y`, `Pxx = cinnerRep x x`,
`Pyy = cinnerRep y y`.  The two products' limits are identified via
`convergesTo_mul` (fed the uniform `QCauchy.globalBound`s), and the termwise
pre-Hilbert Cauchy–Schwarz `D.cauchy_schwarz (xₙ) (yₙ)` — exactly
`f n · f n ≤ g n · h n` — discharges the monotone-limit hypothesis with `N=0`. -/
theorem RC_cauchy_schwarz (z w : GNSCompletionSpace D) :
    CReal.RCle (CReal.RCmul (D.cinnerCompl z w) (D.cinnerCompl z w))
               (CReal.RCmul (D.cinnerCompl z z) (D.cinnerCompl w w)) := by
  refine Quotient.inductionOn₂ z w ?_
  intro x y
  show CReal.leEv (CReal.mul (D.cinnerRep x y) (D.cinnerRep x y))
                  (CReal.mul (D.cinnerRep x x) (D.cinnerRep y y))
  -- uniform bounds on the three aligned rational inner-product sequences
  obtain ⟨Bf, hBf0, hBf⟩ := (D.cInnerQCauchy x y).globalBound
  obtain ⟨Bg, hBg0, hBg⟩ := (D.cInnerQCauchy x x).globalBound
  obtain ⟨Bh, _, hBh⟩ := (D.cInnerQCauchy y y).globalBound
  -- convergence of the base sequences to the completed inner products
  have hPconv := CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq x y) (D.cInnerQCauchy x y)
  have hXXconv := CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq x x) (D.cInnerQCauchy x x)
  have hYYconv := CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq y y) (D.cInnerQCauchy y y)
  -- product-limit: the aligned square converges to P·P
  have hAmul : CReal.ConvergesTo
      (fun k => CReal.mul (CReal.ofQ' (D.cInnerSeq x y k)) (CReal.ofQ' (D.cInnerSeq x y k)))
      (CReal.mul (D.cinnerRep x y) (D.cinnerRep x y)) :=
    CReal.convergesTo_mul (B := Bf)
      (u := fun N => CReal.ofQ' (D.cInnerSeq x y N))
      (v := fun N => CReal.ofQ' (D.cInnerSeq x y N))
      (U := D.cinnerRep x y) (V := D.cinnerRep x y)
      hBf0 (fun k _ => hBf k)
      (fun n => hBf (CReal.QMhat (D.cInnerSeq x y) (D.cInnerQCauchy x y) n))
      hPconv hPconv
  -- product-limit: the aligned cross product converges to Pxx·Pyy
  have hBmul : CReal.ConvergesTo
      (fun k => CReal.mul (CReal.ofQ' (D.cInnerSeq x x k)) (CReal.ofQ' (D.cInnerSeq y y k)))
      (CReal.mul (D.cinnerRep x x) (D.cinnerRep y y)) :=
    CReal.convergesTo_mul (B := Q'.max' Bg Bh)
      (u := fun N => CReal.ofQ' (D.cInnerSeq x x N))
      (v := fun N => CReal.ofQ' (D.cInnerSeq y y N))
      (U := D.cinnerRep x x) (V := D.cinnerRep y y)
      (Q'.le_trans' _ _ _ hBg0 (Q'.le_max'_left Bg Bh))
      (fun k _ => Q'.le_trans' _ _ _ (hBg k) (Q'.le_max'_left Bg Bh))
      (fun n => Q'.le_trans' _ _ _
        (hBh (CReal.QMhat (D.cInnerSeq y y) (D.cInnerQCauchy y y) n)) (Q'.le_max'_right Bg Bh))
      hXXconv hYYconv
  -- monotone limit + termwise Cauchy–Schwarz
  refine CReal.leEv_of_ofQ'_limit_le
    (r := fun n => D.cInnerSeq x y n * D.cInnerSeq x y n)
    (r' := fun n => D.cInnerSeq x x n * D.cInnerSeq y y n)
    hAmul hBmul ?_
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _ (D.cauchy_schwarz (x.seq n) (y.seq n))
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

end GNSData

end YMGap.Continuum.GNSQuotient

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.runningMax_mono
#print axioms YMGap.Constructive.Q'.abs_le_abs_add_one_of_bounds
#print axioms YMGap.Constructive.CReal.QCauchy.globalBound
#print axioms YMGap.Constructive.CReal.leEv_of_ofQ'_limit_le
#print axioms YMGap.Constructive.CReal.RCmul
#print axioms YMGap.Constructive.CReal.RCmul_comm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.RC_cauchy_schwarz
