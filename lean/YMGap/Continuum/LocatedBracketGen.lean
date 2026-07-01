/-
# General-`M` `LocatedBracketM`: collapse the four fields to ONE honest wall
# (`LocatedBracketGen` — the two Lipschitz fields discharged for ALL `M`)

`LocatedNodeDataGen.LocatedBracketM M` is the per-`M` rational datum whose four
non-trivial fields feed the general-`M` off-diagonal OS2 Gram positivity.  This
module discharges the two **Lipschitz** fields (`lipU`, `lipT`) UNCONDITIONALLY
for every `M`, by reusing the already-proved, axiom-clean four-way majorant
engine `ChebMarkovModulus.QB_all` (the `(1+√2)ⁿ`-style Markov induction).  The
crude constant `LipU = Amaj M` / `LipT = Amaj(M+1)+Amaj(M-1)` suffices because a
`LipBound` needs EXISTENCE of a constant, not tightness.

## What is PROVED here (axiom-clean)

  * `cov_plus` / `cov_minus` — the change-of-variables identities
    `½(a+b) + ½(b−a) ≈ b` and `½(a+b) − ½(b−a) ≈ a` (pure `Q'` ring `eqv`).
  * `onBox_of_subpair` — a subpair `−1 ≤ a ≤ b ≤ 1` yields the box datum
    `OnBox (½(a+b)) (½(b−a))`.
  * `Adiff_as_diff` — the antisymmetric first difference of the QB engine equals
    (via `U_arg_eqv`) the honest secant `U_M(b) − U_M(a)`.
  * `lipBound_U_of_QB M lo hi …` — the `lipU` field, for ALL `M`, constant
    `Amaj M`.
  * `twoT_as_Udiff` / `twoTdiff` — route the whole `T`-branch through the SAME
    `U`-difference engine via `ChebU.Ushift` (`2·T_{k+2} ≈ U_{k+2} − U_k`), no
    `T`-difference clone.
  * `lipBound_T_of_QB k lo hi …` — the `lipT` field, for ALL `M = k+1`, constant
    `Amaj(k+2)+Amaj k`.
  * `locatedBracket_of_enclosure` / `deMoivreNode_of_enclosure` — the assembly:
    the four fields reduce to the single Type-level `RootEnclosure` residual.

## The single honest wall (NOT closed here)

`RootEnclosure k` carries only the three genuine rational-`π` sign facts:
`U_{k+1}(lo) ≤ 0`, `0 ≤ U_{k+1}(hi)`, and the co-located `T`-sign certificate
`T_{k+2}(hi) + LipT·(hi−lo) ≤ 0`, together with the interval bounds.  This is the
two-sided rational enclosure of the largest `U`-root `cos(π/(k+2))` inside the
`T`-negative window — the standing rational-`π` residual.  It is a finite
`decide` for each fixed `M` and genuinely open uniformly in `M`.  The Lipschitz
toolkit provably cannot supply it (it upper-bounds motion; a sign certificate
needs a lower/descent bound).

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  `RootEnclosure` /
`LocatedBracketM` are `Type`-level records (witnesses as data, not `Prop`-∃).
-/

import YMGap.Continuum.LocatedNodeDataGen
import YMGap.Continuum.ChebOrthoLegProof

namespace YMGap.Continuum.LocatedBracketGen

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.ChebRoot
open YMGap.Continuum.ChebMarkovModulus
open YMGap.Continuum.ChebBracketTaylor

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'`/`half` arithmetic helpers -/

/-- `0 ≤ b + -a` from `a ≤ b`. -/
theorem sub_nonneg (a b : Q') (hab : a ≤ b) : (0 : Q') ≤ b + -a := by
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) ?_
  exact Q'.add_le_add_right a b (-a) hab

/-- `half · w ≤ w` for `0 ≤ w`. -/
theorem half_mul_le (w : Q') (hw : (0 : Q') ≤ w) : half * w ≤ w := by
  refine Q'.le_trans' _ ((1 : Q') * w) _ ?_ (Q'.le_of_eqv (Q'.one_mul_eqv w))
  exact Q'.mul_le_mul_of_nonneg_right half 1 w (by decide) hw

/-- `half · (2·w) ≈ w`. -/
theorem half_two_mul (w : Q') : half * ((2 : Q') * w) ≈ w := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (2 : Q') w)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (half * (2 : Q')) 1 w (by decide)) ?_
  exact Q'.one_mul_eqv w

/-! ## 1. Change-of-variables identities -/

/-- `½(a+b) + ½(b−a) ≈ b`. -/
theorem cov_plus (a b : Q') : half * (a + b) + half * (b + -a) ≈ b := by
  have h1 : half * (b + -a) ≈ b + -(half * (a + b)) :=
    Q'.eqv_symm (CReal.hi_sub_mid a b)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h1) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (half * (a + b)) b (-(half * (a + b))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (half * (a + b)) b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b (half * (a + b)) (-(half * (a + b)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (half * (a + b)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' b)

/-- `½(a+b) − ½(b−a) ≈ a`. -/
theorem cov_minus (a b : Q') : half * (a + b) + -(half * (b + -a)) ≈ a := by
  have h1 : half * (b + -a) ≈ half * (a + b) + -a := Q'.eqv_symm (CReal.mid_sub_lo a b)
  have h2 : -(half * (b + -a)) ≈ -(half * (a + b)) + a := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (half * (a + b)) (-a)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv a)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (half * (a + b)) (-(half * (a + b))) a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (half * (a + b)))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' a)

/-! ## 2. Box from a subpair -/

/-- A subpair `−1 ≤ a ≤ b ≤ 1` gives the QB box `OnBox (½(a+b)) (½(b−a))`. -/
theorem onBox_of_subpair {a b : Q'} (hlo : (-1 : Q') ≤ a) (hab : a ≤ b) (hhi : b ≤ (1 : Q')) :
    OnBox (half * (a + b)) (half * (b + -a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (CReal.mid_le hab) hhi
  · exact Q'.le_trans' _ _ _ hlo (CReal.le_mid hab)
  · exact Q'.mul_nonneg half (b + -a) (by decide) (sub_nonneg a b hab)
  · have hna : -a ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg hlo) (Q'.le_of_eqv (Q'.neg_neg_eqv 1))
    have hsum : b + -a ≤ (1 : Q') + (1 : Q') := Q'.add_le_add hhi hna
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ half hsum (by decide)) ?_
    exact Q'.le_of_eqv (by decide)

/-! ## 3. The QB `Adiff` equals the honest secant -/

/-- `Adiff (½(a+b)) (½(b−a)) M ≈ U_M(b) − U_M(a)` via `U_arg_eqv` and `cov_*`. -/
theorem Adiff_as_diff (M : Nat) (a b : Q') :
    Adiff (half * (a + b)) (half * (b + -a)) M ≈ Cheb.U M b + -(Cheb.U M a) := by
  show Cheb.U M (half * (a + b) + half * (b + -a))
        + -(Cheb.U M (half * (a + b) + -(half * (b + -a))))
      ≈ Cheb.U M b + -(Cheb.U M a)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (ChebOrthoLegProof.U_arg_eqv M (cov_plus a b))) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_eqv_congr _ _ (ChebOrthoLegProof.U_arg_eqv M (cov_minus a b)))

/-! ## 4. The `lipU` adapter — discharges `lipU` for ALL `M` -/

/-- **`U_M` is two-sided Lipschitz on `[lo,hi] ⊂ [−1,1]`** with constant `Amaj M`,
for EVERY `M`, from the proved `QB_all` bound on `Adiff`. -/
theorem lipBound_U_of_QB (M : Nat) (lo hi : Q') (hlo : (-1 : Q') ≤ lo) (hhi : hi ≤ (1 : Q')) :
    LipBound (Ueval M) lo hi (Q'.ofNat (Amaj M)) where
  nonneg := ofNat_nonneg _
  bound := by
    intro a b ha hab hb
    have ha1 : (-1 : Q') ≤ a := Q'.le_trans' _ _ _ hlo ha
    have hb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi
    have hbox := onBox_of_subpair ha1 hab hb1
    have hδle : half * (b + -a) ≤ (b + -a) := half_mul_le (b + -a) (sub_nonneg a b hab)
    have hUb : Adiff (half * (a + b)) (half * (b + -a)) M
        ≤ Q'.ofNat (Amaj M) * (half * (b + -a)) :=
      (QB_all (half * (a + b)) (half * (b + -a)) hbox M).1.2.1.2
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Adiff_as_diff M a b)) ?_
    refine Q'.le_trans' _ _ _ hUb ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hδle (ofNat_nonneg _)
  bound' := by
    intro a b ha hab hb
    have ha1 : (-1 : Q') ≤ a := Q'.le_trans' _ _ _ hlo ha
    have hb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi
    have hbox := onBox_of_subpair ha1 hab hb1
    have hδle : half * (b + -a) ≤ (b + -a) := half_mul_le (b + -a) (sub_nonneg a b hab)
    have hLb : -(Adiff (half * (a + b)) (half * (b + -a)) M)
        ≤ Q'.ofNat (Amaj M) * (half * (b + -a)) :=
      neg_flip (QB_all (half * (a + b)) (half * (b + -a)) hbox M).1.2.1.1
    -- U_M(a) − U_M(b) ≈ −(Adiff)
    have heqv : Cheb.U M a + -(Cheb.U M b) ≈ -(Adiff (half * (a + b)) (half * (b + -a)) M) := by
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Adiff_as_diff M a b)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (Cheb.U M b) (-(Cheb.U M a))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (Cheb.U M a))) ?_
      exact Q'.add_comm_eqv (-(Cheb.U M b)) (Cheb.U M a)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
    refine Q'.le_trans' _ _ _ hLb ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hδle (ofNat_nonneg _)

/-! ## 5. The `T`-branch through the same `U`-engine -/

/-- `2·T_{k+2}(z) ≈ U_{k+2}(z) − U_k(z)` — `ChebU.Ushift` rearranged. -/
theorem twoT_as_Udiff (k : Nat) (z : Q') :
    (2 : Q') * Cheb.T (k + 2) z ≈ Cheb.U (k + 2) z + -(Cheb.U k z) := by
  have h := ChebU.Ushift k z
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (Cheb.U k z) ((2 : Q') * Cheb.T (k + 2) z))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (Cheb.U k z))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Pure `Q'` rearrangement: `(P−Q) − (R−S) ≈ (P−R) − (Q−S)`. -/
theorem rearrange4 (P Q R S : Q') :
    (P + -Q) + -(R + -S) ≈ (P + -R) + -(Q + -S) := by
  have hL : (P + -Q) + -(R + -S) ≈ P + (-Q + (-R + S)) := by
    have e1 : -(R + -S) ≈ -R + S := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv R (-S)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv S)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (P + -Q) (-(R + -S)) (-R + S) e1) ?_
    exact Q'.add_assoc_eqv P (-Q) (-R + S)
  have hR : (P + -R) + -(Q + -S) ≈ P + (-R + (-Q + S)) := by
    have e2 : -(Q + -S) ≈ -Q + S := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv Q (-S)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv S)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (P + -R) (-(Q + -S)) (-Q + S) e2) ?_
    exact Q'.add_assoc_eqv P (-R) (-Q + S)
  refine Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR))
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-Q) (-R) S)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (-Q) (-R))) ?_
  exact Q'.add_assoc_eqv (-R) (-Q) S

/-- `2·(T_{k+2}(b) − T_{k+2}(a)) ≈ Adiff_{k+2} − Adiff_k` (same `x,δ` from `(a,b)`). -/
theorem twoTdiff (k : Nat) (a b : Q') :
    (2 : Q') * (Cheb.T (k + 2) b + -(Cheb.T (k + 2) a))
      ≈ Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
          + -(Adiff (half * (a + b)) (half * (b + -a)) k) := by
  have hdist : (2 : Q') * (Cheb.T (k + 2) b + -(Cheb.T (k + 2) a))
      ≈ (2 : Q') * Cheb.T (k + 2) b + -((2 : Q') * Cheb.T (k + 2) a) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (2 : Q') (Cheb.T (k + 2) b) (-(Cheb.T (k + 2) a))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (2 : Q') (Cheb.T (k + 2) a))
  have hsub : (2 : Q') * Cheb.T (k + 2) b + -((2 : Q') * Cheb.T (k + 2) a)
      ≈ (Cheb.U (k + 2) b + -(Cheb.U k b)) + -(Cheb.U (k + 2) a + -(Cheb.U k a)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (twoT_as_Udiff k b)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (twoT_as_Udiff k a))
  have hAdiff : (Cheb.U (k + 2) b + -(Cheb.U (k + 2) a)) + -(Cheb.U k b + -(Cheb.U k a))
      ≈ Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
          + -(Adiff (half * (a + b)) (half * (b + -a)) k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Adiff_as_diff (k + 2) a b))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Adiff_as_diff k a b)))
  exact Q'.eqv_trans _ _ _ hdist
    (Q'.eqv_trans _ _ _ hsub
      (Q'.eqv_trans _ _ _
        (rearrange4 (Cheb.U (k + 2) b) (Cheb.U k b) (Cheb.U (k + 2) a) (Cheb.U k a)) hAdiff))

/-! ## 6. The `lipT` adapter — discharges `lipT` for ALL `M = k+1` -/

/-- `0 ≤ (ofNat A · half·(b−a)) + (ofNat B · half·(b−a))` on a subpair. -/
private theorem W_nonneg (A B : Nat) {a b : Q'} (hab : a ≤ b) :
    (0 : Q') ≤ Q'.ofNat A * (half * (b + -a)) + Q'.ofNat B * (half * (b + -a)) := by
  have hδnn : (0 : Q') ≤ half * (b + -a) :=
    Q'.mul_nonneg half (b + -a) (by decide) (sub_nonneg a b hab)
  have ht1 : (0 : Q') ≤ Q'.ofNat A * (half * (b + -a)) := Q'.mul_nonneg _ _ (ofNat_nonneg _) hδnn
  have ht2 : (0 : Q') ≤ Q'.ofNat B * (half * (b + -a)) := Q'.mul_nonneg _ _ (ofNat_nonneg _) hδnn
  exact Q'.le_trans' _ _ _ ht1 (Q'.add_le_self_of_nonneg _ _ ht2)

/-- `(ofNat A · half·(b−a)) + (ofNat B · half·(b−a)) ≤ ofNat (A+B) · (b−a)`. -/
private theorem W_le (A B : Nat) {a b : Q'} (hab : a ≤ b) :
    Q'.ofNat A * (half * (b + -a)) + Q'.ofNat B * (half * (b + -a))
      ≤ Q'.ofNat (A + B) * (b + -a) := by
  have hδle : half * (b + -a) ≤ (b + -a) := half_mul_le (b + -a) (sub_nonneg a b hab)
  have h1 : Q'.ofNat A * (half * (b + -a)) ≤ Q'.ofNat A * (b + -a) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hδle (ofNat_nonneg _)
  have h2 : Q'.ofNat B * (half * (b + -a)) ≤ Q'.ofNat B * (b + -a) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hδle (ofNat_nonneg _)
  refine Q'.le_trans' _ _ _ (Q'.add_le_add h1 h2) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat A) (Q'.ofNat B) (b + -a))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (ChebU.ofNat_add_eqv A B)

/-- **`T_{k+2}` is two-sided Lipschitz on `[lo,hi] ⊂ [−1,1]`** with constant
`Amaj(k+2) + Amaj k`, for EVERY `k`, routed through the `U`-difference engine. -/
theorem lipBound_T_of_QB (k : Nat) (lo hi : Q') (hlo : (-1 : Q') ≤ lo) (hhi : hi ≤ (1 : Q')) :
    LipBound (Cheb.T (k + 2)) lo hi (Q'.ofNat (Amaj (k + 2) + Amaj k)) where
  nonneg := ofNat_nonneg _
  bound := by
    intro a b ha hab hb
    have ha1 : (-1 : Q') ≤ a := Q'.le_trans' _ _ _ hlo ha
    have hb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi
    have hbox := onBox_of_subpair ha1 hab hb1
    have hUb2 : Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
        ≤ Q'.ofNat (Amaj (k + 2)) * (half * (b + -a)) :=
      (QB_all (half * (a + b)) (half * (b + -a)) hbox (k + 2)).1.2.1.2
    have hLb0 : -(Adiff (half * (a + b)) (half * (b + -a)) k)
        ≤ Q'.ofNat (Amaj k) * (half * (b + -a)) :=
      neg_flip (QB_all (half * (a + b)) (half * (b + -a)) hbox k).1.2.1.1
    have hAdiffsum : Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
          + -(Adiff (half * (a + b)) (half * (b + -a)) k)
        ≤ Q'.ofNat (Amaj (k + 2)) * (half * (b + -a))
            + Q'.ofNat (Amaj k) * (half * (b + -a)) :=
      Q'.add_le_add hUb2 hLb0
    have hTeqv : Cheb.T (k + 2) b + -(Cheb.T (k + 2) a)
        ≈ half * (Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
            + -(Adiff (half * (a + b)) (half * (b + -a)) k)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (half_two_mul (Cheb.T (k + 2) b + -(Cheb.T (k + 2) a)))) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (twoTdiff k a b)
    have hTle : Cheb.T (k + 2) b + -(Cheb.T (k + 2) a)
        ≤ half * (Q'.ofNat (Amaj (k + 2)) * (half * (b + -a))
            + Q'.ofNat (Amaj k) * (half * (b + -a))) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hTeqv) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ half hAdiffsum (by decide)
    refine Q'.le_trans' _ _ _ hTle ?_
    exact Q'.le_trans' _ _ _
      (half_mul_le _ (W_nonneg (Amaj (k + 2)) (Amaj k) hab)) (W_le (Amaj (k + 2)) (Amaj k) hab)
  bound' := by
    intro a b ha hab hb
    have ha1 : (-1 : Q') ≤ a := Q'.le_trans' _ _ _ hlo ha
    have hb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _ hb hhi
    have hbox := onBox_of_subpair ha1 hab hb1
    have hUb0 : Adiff (half * (a + b)) (half * (b + -a)) k
        ≤ Q'.ofNat (Amaj k) * (half * (b + -a)) :=
      (QB_all (half * (a + b)) (half * (b + -a)) hbox k).1.2.1.2
    have hLb2 : -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2))
        ≤ Q'.ofNat (Amaj (k + 2)) * (half * (b + -a)) :=
      neg_flip (QB_all (half * (a + b)) (half * (b + -a)) hbox (k + 2)).1.2.1.1
    have hAdiffsum : Adiff (half * (a + b)) (half * (b + -a)) k
          + -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2))
        ≤ Q'.ofNat (Amaj k) * (half * (b + -a))
            + Q'.ofNat (Amaj (k + 2)) * (half * (b + -a)) :=
      Q'.add_le_add hUb0 hLb2
    -- 2·(T a − T b) ≈ Adiff_k − Adiff_{k+2}
    have htwo : (2 : Q') * (Cheb.T (k + 2) a + -(Cheb.T (k + 2) b))
        ≈ Adiff (half * (a + b)) (half * (b + -a)) k
            + -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2)) := by
      have hneg : Cheb.T (k + 2) a + -(Cheb.T (k + 2) b)
          ≈ -(Cheb.T (k + 2) b + -(Cheb.T (k + 2) a)) := by
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (Cheb.T (k + 2) b) (-(Cheb.T (k + 2) a))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (Cheb.T (k + 2) a))) ?_
        exact Q'.add_comm_eqv (-(Cheb.T (k + 2) b)) (Cheb.T (k + 2) a)
      have hfin : -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2)
            + -(Adiff (half * (a + b)) (half * (b + -a)) k))
          ≈ Adiff (half * (a + b)) (half * (b + -a)) k
              + -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.neg_add_eqv (Adiff (half * (a + b)) (half * (b + -a)) (k + 2))
            (-(Adiff (half * (a + b)) (half * (b + -a)) k))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.neg_neg_eqv (Adiff (half * (a + b)) (half * (b + -a)) k))) ?_
        exact Q'.add_comm_eqv _ _
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hneg) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (2 : Q') _) ?_
      exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (twoTdiff k a b)) hfin
    have hTeqv : Cheb.T (k + 2) a + -(Cheb.T (k + 2) b)
        ≈ half * (Adiff (half * (a + b)) (half * (b + -a)) k
            + -(Adiff (half * (a + b)) (half * (b + -a)) (k + 2))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (half_two_mul (Cheb.T (k + 2) a + -(Cheb.T (k + 2) b)))) ?_
      exact Q'.mul_eqv_congr_left _ _ _ htwo
    have hTle : Cheb.T (k + 2) a + -(Cheb.T (k + 2) b)
        ≤ half * (Q'.ofNat (Amaj k) * (half * (b + -a))
            + Q'.ofNat (Amaj (k + 2)) * (half * (b + -a))) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hTeqv) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ half hAdiffsum (by decide)
    -- half·W' ≤ W' ≤ ofNat(Amaj k + Amaj(k+2))·(b−a) = ofNat(Amaj(k+2)+Amaj k)·(b−a)
    have hcomm : Amaj k + Amaj (k + 2) = Amaj (k + 2) + Amaj k := Nat.add_comm _ _
    refine Q'.le_trans' _ _ _ hTle ?_
    refine Q'.le_trans' _ _ _
      (half_mul_le _ (W_nonneg (Amaj k) (Amaj (k + 2)) hab)) ?_
    have := W_le (Amaj k) (Amaj (k + 2)) hab
    rw [hcomm] at this
    exact this

/-! ## 7. The single honest wall (Type-level residual) and the assembly -/

/-- **The rational-`π` root-enclosure residual** (the ONE remaining wall).  Carries
only the three genuine sign facts for `U_{k+1}` / `T_{k+2}` and the interval
bounds; the two Lipschitz fields are supplied by the adapters above.  For each
fixed `k` this is a finite `decide`; uniformly in `k` it is the standing
two-sided rational enclosure of `cos(π/(k+2))` inside the `T`-negative window. -/
structure RootEnclosure (k : Nat) where
  /-- Rational left endpoint. -/
  lo : Q'
  /-- Rational right endpoint. -/
  hi : Q'
  /-- `−1 ≤ lo` (strict-interior left). -/
  hlo1 : (-1 : Q') ≤ lo
  /-- `hi ≤ 1` (strict-interior right). -/
  hhi1 : hi ≤ (1 : Q')
  /-- `lo ≤ hi`. -/
  hle : lo ≤ hi
  /-- `U_{k+1}(lo) ≤ 0` (left sign, the rational-`π` fact). -/
  loSign : Ueval (k + 1) lo ≤ (0 : Q')
  /-- `0 ≤ U_{k+1}(hi)` (right sign, the rational-`π` fact). -/
  hiSign : (0 : Q') ≤ Ueval (k + 1) hi
  /-- The co-located `T`-sign certificate across the bracket. -/
  tsign : Cheb.T (k + 2) hi + Q'.ofNat (Amaj (k + 2) + Amaj k) * (hi + -lo) ≤ (0 : Q')

/-- **The reduced constructor.**  From a `RootEnclosure k`, the four fields of
`LocatedBracketM (k+1)` are supplied (`lipU`, `lipT` by the adapters; `initU`,
`tsign` by the enclosure). -/
def locatedBracket_of_enclosure (k : Nat) (e : RootEnclosure k) :
    LocatedNodeDataGen.LocatedBracketM (k + 1) where
  lo := e.lo
  hi := e.hi
  LipU := Q'.ofNat (Amaj (k + 1))
  LipT := Q'.ofNat (Amaj (k + 2) + Amaj k)
  initU := ⟨e.hle, e.loSign, e.hiSign⟩
  lipU := lipBound_U_of_QB (k + 1) e.lo e.hi e.hlo1 e.hhi1
  lipT := lipBound_T_of_QB k e.lo e.hi e.hlo1 e.hhi1
  tsign := e.tsign

/-- A fully inhabited de Moivre node from the enclosure (branch collapse and both
Lipschitz fields already proved), hence general-`M` off-diagonal OS2 Gram
positivity downstream — conditional ONLY on the single `RootEnclosure` wall. -/
def deMoivreNode_of_enclosure (k : Nat) (e : RootEnclosure k) :
    ChebRotationPair.DeMoivreNode (k + 1) :=
  LocatedNodeDataGen.deMoivreNode_of_bracket (k + 1) (locatedBracket_of_enclosure k e)

end YMGap.Continuum.LocatedBracketGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LocatedBracketGen.cov_plus
#print axioms YMGap.Continuum.LocatedBracketGen.cov_minus
#print axioms YMGap.Continuum.LocatedBracketGen.onBox_of_subpair
#print axioms YMGap.Continuum.LocatedBracketGen.Adiff_as_diff
#print axioms YMGap.Continuum.LocatedBracketGen.lipBound_U_of_QB
#print axioms YMGap.Continuum.LocatedBracketGen.twoT_as_Udiff
#print axioms YMGap.Continuum.LocatedBracketGen.twoTdiff
#print axioms YMGap.Continuum.LocatedBracketGen.lipBound_T_of_QB
#print axioms YMGap.Continuum.LocatedBracketGen.locatedBracket_of_enclosure
#print axioms YMGap.Continuum.LocatedBracketGen.deMoivreNode_of_enclosure
