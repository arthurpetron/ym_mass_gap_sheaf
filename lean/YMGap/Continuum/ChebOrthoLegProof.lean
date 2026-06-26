/-
# The EVENTUAL smooth-bracket leg bound `EventualBrLegRemainder`.

This module discharges the eventual per-cell SMOOTH-BRACKET leg residual named in
`ChebOrthoLegAssembly` (the smooth-bracket leg of the centered midpoint-difference
remainder), against HALF the graded rate, for `M = N+1` beyond an explicit per-order
threshold `M₀(e) = max((44·Bbound e)², (2·C e)²)`.  All analytic inputs are proved
elsewhere; this module assembles them.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `U_arg_eqv` / `Gbracket_arg_eqv` — `Cheb.U`, `Gbracket` respect `≈` in their
    rational argument (two-step recurrence congruence + `mkPosScale_eqv`).
  * `bdyPoint_succ_eqv` / `bdyPoint_eqv` — the cell geometry `b_{k±1} ≈ x_k ± δ`.
  * `bracketDiff_eqv` — the bracket-difference identity `B_+ − B_- ≈ R_B + lebW·g`.
  * `bracketLeg_index_abstract` + `br_decomp` — the EXACT per-cell decomposition
    `legBr − LZA ≈ TermA + TermB` (`TermA = ¼·(lebW·g)·Δ₂`, `TermB = ¼·(s_++s_-)·R_B`).
  * `AbsLeRat.ofQ'_smul` — signed-scalar × two-sided-bounded `CReal` product bound.
  * `termA_le_quarter` / `termB_le_quarter` — each leg term `≤ ¼·gradedRate` on the
    eventual window (Term A via the tight `|Δ₂| ≤ 22/jdist²` modulus + the Markov
    bracket-derivative bound `|B_e′| ≤ Bbound e`; Term B via `|s_±| ≤ 1` and the cubic
    bracket Taylor bound `|R_B| ≤ C(e)·δ³`).
  * **`eventualBrLegRemainder`** — `ChebOrthoLegAssembly.EventualBrLegRemainder e he`.

The companion radical-leg bound (`EventualRadLegRemainder`) and its key
antisymmetric-second-difference reduction are NOT discharged here.

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide`/`ac_rfl` only on
closed/`Nat`-AC goals.  Axiom-gate at the foot.
-/

import YMGap.Continuum.ChebOrthoLegAssembly
import YMGap.Continuum.ChebOrthoTightModulus
import YMGap.Continuum.ChebMarkovModulus
import YMGap.Continuum.ChebBracketTaylor
import YMGap.Continuum.ChebOrthoCancelDiv
import YMGap.Continuum.ChebOrthoOffDiagClose

namespace YMGap.Continuum.ChebOrthoLegProof

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag (Gbracket)
open YMGap.Continuum.ChebOrthoWeightedFTC (Bderiv)
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 0. Argument congruence for `Cheb.U`, `Gbracket`, `Bderiv` -/

/-- The single-step `U`-recurrence congruence packaged for the two-step pair. -/
private theorem U_step_eqv (m : Nat) {x y : Q'} (h : x ≈ y)
    (ih0 : Cheb.U m x ≈ Cheb.U m y) (ih1 : Cheb.U (m + 1) x ≈ Cheb.U (m + 1) y) :
    Cheb.U (m + 2) x ≈ Cheb.U (m + 2) y := by
  show (((2 : Q') * x) * Cheb.U (m + 1) x + (-(Cheb.U m x)))
      ≈ (((2 : Q') * y) * Cheb.U (m + 1) y + (-(Cheb.U m y)))
  refine Cheb.add_eqv_congr _ _ _ _ ?_ (Q'.neg_eqv_congr _ _ ih0)
  exact Cheb.mul_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) ih1

/-- Two-step pair packager for `U` argument congruence. -/
private theorem U_arg_pair {x y : Q'} (h : x ≈ y) :
    ∀ n, (Cheb.U n x ≈ Cheb.U n y) ∧ (Cheb.U (n + 1) x ≈ Cheb.U (n + 1) y) := by
  intro n
  induction n with
  | zero =>
      refine ⟨Q'.eqv_refl _, ?_⟩
      show ((2 : Q') * x) ≈ ((2 : Q') * y)
      exact Q'.mul_eqv_congr_left _ _ _ h
  | succ k ih => exact ⟨ih.2, U_step_eqv k h ih.1 ih.2⟩

/-- **`Cheb.U` respects `≈` in its argument.** -/
theorem U_arg_eqv (n : Nat) {x y : Q'} (h : x ≈ y) : Cheb.U n x ≈ Cheb.U n y :=
  (U_arg_pair h n).1

/-- A scaled `U`-term `mkPos (U n x).num ((U n x).den·d)` respects `≈` in `x`:
both sides reduce (via `mkPosScale_eqv`) to `(U n ·)·(1/d)`, and `U n x ≈ U n y`. -/
theorem UTerm_arg_eqv (n d : Nat) (hd : 0 < d) {x y : Q'} (h : x ≈ y) :
    Q'.mkPos (Cheb.U n x).num ((Cheb.U n x).den * d) (Nat.mul_pos (Cheb.U n x).den_pos hd)
      ≈ Q'.mkPos (Cheb.U n y).num ((Cheb.U n y).den * d) (Nat.mul_pos (Cheb.U n y).den_pos hd) := by
  refine Q'.eqv_trans _ _ _
    (ChebUDClosure.mkPosScale_eqv (Cheb.U n x) d (Nat.mul_pos (Cheb.U n x).den_pos hd) hd) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (U_arg_eqv n h)) ?_
  exact Q'.eqv_symm
    (ChebUDClosure.mkPosScale_eqv (Cheb.U n y) d (Nat.mul_pos (Cheb.U n y).den_pos hd) hd)

/-- **`Gbracket e he` respects `≈` in its argument.** -/
theorem Gbracket_arg_eqv (e : Nat) (he : 0 < e) {x y : Q'} (h : x ≈ y) :
    Gbracket e he x ≈ Gbracket e he y := by
  show (Q'.mkPos (Cheb.U (e - 1) x).num ((Cheb.U (e - 1) x).den * e)
          (Nat.mul_pos (Cheb.U (e - 1) x).den_pos he)
        + (-(Q'.mkPos (Cheb.U (e + 1) x).num ((Cheb.U (e + 1) x).den * (e + 2))
            (Nat.mul_pos (Cheb.U (e + 1) x).den_pos (by omega)))))
      ≈ (Q'.mkPos (Cheb.U (e - 1) y).num ((Cheb.U (e - 1) y).den * e)
          (Nat.mul_pos (Cheb.U (e - 1) y).den_pos he)
        + (-(Q'.mkPos (Cheb.U (e + 1) y).num ((Cheb.U (e + 1) y).den * (e + 2))
            (Nat.mul_pos (Cheb.U (e + 1) y).den_pos (by omega)))))
  refine Cheb.add_eqv_congr _ _ _ _ (UTerm_arg_eqv (e - 1) e he h)
    (Q'.neg_eqv_congr _ _ (UTerm_arg_eqv (e + 1) (e + 2) (by omega) h))

/-! ## 1. Cell geometry: the boundary points are the midpoint ± δ -/

/-- The half-cell spacing `δ = 1/M`. -/
def delta (M : Nat) (hM : 0 < M) : Q' := Q'.mkPos 1 M hM

/-- `mkPos a M ≈ mkPos b M` when `a = b` as integers. -/
private theorem mkPos_num_eqv {a b : Int} (M : Nat) (hM : 0 < M) (h : a = b) :
    Q'.mkPos a M hM ≈ Q'.mkPos b M hM := by
  rw [h]; exact Q'.eqv_refl _

/-- **`bdyPoint M (k+1) ≈ x_k + δ`.**  Both are `(2k+2−M)/M` as rationals. -/
theorem bdyPoint_succ_eqv (M : Nat) (hM : 0 < M) (k : Nat) :
    ChebOrthoMidpoint.bdyPoint M hM (k + 1)
      ≈ (RiemannSOS.uniformMidpoint M hM k + delta M hM) := by
  -- RHS = mkPos (2k+1−M) M + mkPos 1 M ≈ mkPos ((2k+1−M)+1) M = mkPos (2(k+1)−M) M = bdyPoint
  have hadd : (RiemannSOS.uniformMidpoint M hM k + delta M hM)
      ≈ Q'.mkPos (((2 * (k : Int) + 1) - (M : Int)) + 1) M hM :=
    SemicircleIntegral.mkPos_add_same_den ((2 * (k : Int) + 1) - (M : Int)) 1 M hM
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hadd)
  show Q'.mkPos (2 * ((k + 1 : Nat) : Int) - (M : Int)) M hM
      ≈ Q'.mkPos (((2 * (k : Int) + 1) - (M : Int)) + 1) M hM
  refine mkPos_num_eqv M hM ?_
  push_cast; omega

/-- **`bdyPoint M k ≈ x_k + (−δ)`.**  Both are `(2k−M)/M`. -/
theorem bdyPoint_eqv (M : Nat) (hM : 0 < M) (k : Nat) :
    ChebOrthoMidpoint.bdyPoint M hM k
      ≈ (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))) := by
  have hneg : (-(delta M hM)) ≈ Q'.mkPos (-1) M hM := by
    show (-(Q'.mkPos 1 M hM)) ≈ Q'.mkPos (-1) M hM
    show (-(Q'.mkPos 1 M hM)).num * ((Q'.mkPos (-1) M hM).den : Int)
        = (Q'.mkPos (-1) M hM).num * ((-(Q'.mkPos 1 M hM)).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    show (-((Q'.mkPos 1 M hM).num)) * (M : Int) = (-1 : Int) * ((Q'.mkPos 1 M hM).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
  have hadd : (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM)))
      ≈ Q'.mkPos (((2 * (k : Int) + 1) - (M : Int)) + (-1)) M hM := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hneg) ?_
    exact SemicircleIntegral.mkPos_add_same_den ((2 * (k : Int) + 1) - (M : Int)) (-1) M hM
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hadd)
  show Q'.mkPos (2 * ((k : Nat) : Int) - (M : Int)) M hM
      ≈ Q'.mkPos (((2 * (k : Int) + 1) - (M : Int)) + (-1)) M hM
  refine mkPos_num_eqv M hM ?_
  push_cast; omega

/-! ## 2. The bracket difference identity `B_+ − B_- = R_B + h·g` -/

/-- `bP = Gbracket e he (bdyPoint M (k+1)) ≈ Gbracket e he (x_k + δ)`. -/
theorem bP_eqv (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
      ≈ Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM) :=
  Gbracket_arg_eqv e he (bdyPoint_succ_eqv M hM k)

/-- `bM = Gbracket e he (bdyPoint M k) ≈ Gbracket e he (x_k + (−δ))`. -/
theorem bM_eqv (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k)
      ≈ Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))) :=
  Gbracket_arg_eqv e he (bdyPoint_eqv M hM k)

/-- `lebW M = 2/M ≈ 2·δ = (1+1)·δ`. -/
theorem lebW_eq_twoDelta (M : Nat) (hM : 0 < M) :
    SemicircleIntegral.lebW M hM ≈ (((1 : Q') + 1) * delta M hM) := by
  -- lebW = mkPos 2 M ; (1+1)·mkPos 1 M cross-mult check
  show (SemicircleIntegral.lebW M hM).num * ((((1 : Q') + 1) * delta M hM).den : Int)
      = (((1 : Q') + 1) * delta M hM).num * ((SemicircleIntegral.lebW M hM).den : Int)
  rw [Q'.mul_den_cast]
  show (Q'.mkPos 2 M hM).num * (((((1 : Q') + 1)).den : Int) * ((Q'.mkPos 1 M hM).den : Int))
      = (((1 : Q') + 1) * Q'.mkPos 1 M hM).num * ((Q'.mkPos 2 M hM).den : Int)
  rw [show (((1 : Q') + 1) * Q'.mkPos 1 M hM).num
        = ((1 : Q') + 1).num * (Q'.mkPos 1 M hM).num from rfl]
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  show (2 : Int) * ((((1 : Q') + 1).den : Int) * (M : Int))
      = ((1 : Q') + 1).num * 1 * (M : Int)
  have hn : ((1 : Q') + 1).num = 2 := by decide
  have hd : (((1 : Q') + 1).den : Int) = 1 := by decide
  rw [hn, hd]; omega

/-- **The bracket-difference identity (rational).**
`bP − bM ≈ R_B e he x_k δ + lebW·g`, where `g = Bderiv e he x_k`, `δ = 1/M`,
`lebW = 2/M = 2δ`.  Substitutes the boundary points for `x_k ± δ` and unfolds
`R_B`. -/
theorem bracketDiff_eqv (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    (Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
        + (-(Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))))
      ≈ (ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM)
          + SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)) := by
  -- LHS ≈ G(x+d) − G(x−d)
  have hLHS : (Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
        + (-(Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))))
      ≈ (Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
          + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM)))))) :=
    Cheb.add_eqv_congr _ _ _ _ (bP_eqv e he M hM k)
      (Q'.neg_eqv_congr _ _ (bM_eqv e he M hM k))
  refine Q'.eqv_trans _ _ _ hLHS ?_
  -- R_B = DG − (1+1)·(d·g)
  have hRB : ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM)
      = ((Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))))))
          + (-(((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))))) := rfl
  rw [hRB]
  -- lebW·g ≈ 2·(d·g)
  have hlebg : SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)
      ≈ (((1 : Q') + 1) * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (lebW_eq_twoDelta M hM)) ?_
    exact Q'.mul_assoc_eqv ((1 : Q') + 1) (delta M hM)
      (Bderiv e he (RiemannSOS.uniformMidpoint M hM k))
  refine Q'.eqv_symm ?_
  calc ((Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))))))
          + (-(((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))))
        + SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)
      ≈ ((Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))))))
          + (-(((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))))
          + (((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))) :=
        Q'.add_eqv_congr_left _ _ _ hlebg
    _ ≈ (Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))))))
          + ((-(((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))))
            + (((1 : Q') + 1)
              * (delta M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))) :=
        Q'.add_assoc_eqv _ _ _
    _ ≈ (Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM))))))
          + (0 : Q') :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)
    _ ≈ (Gbracket e he (RiemannSOS.uniformMidpoint M hM k + delta M hM)
            + (-(Gbracket e he (RiemannSOS.uniformMidpoint M hM k + (-(delta M hM)))))) :=
        QPoly.q_add_zero_eqv _

/-! ## 2b. Signed-scalar product bound for `AbsLeRat` -/

/-- **Signed scalar times a two-sided-bounded `CReal`.**
`AbsLeRat y b`, `|c| ≤ Bc`, `b, Bc ≥ 0` ⇒ `AbsLeRat (mul (ofQ' c) y) (Bc·b)`. -/
theorem AbsLeRat.ofQ'_smul {y : CReal} {c Bc b : Q'}
    (hy : AbsLeRat y b) (hc1 : c ≤ Bc) (hc2 : (-c) ≤ Bc)
    (hBc : (0 : Q') ≤ Bc) (hb : (0 : Q') ≤ b) :
    AbsLeRat (CReal.mul (CReal.ofQ' c) y) (Bc * b) := by
  have hvlow : (-Bc) ≤ c := by
    have := Q'.neg_le_neg hc2
    exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv c))
  refine ⟨?_, ?_⟩
  · -- leRat (c·y) (Bc·b)
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hBc hε
    obtain ⟨N, hN⟩ := hy.1 δ hδpos
    obtain ⟨N2, hN2⟩ := hy.2 δ hδpos
    refine ⟨max N N2, fun n hn => ?_⟩
    have hub : y.approx n ≤ b + δ := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hlb' : (-(y.approx n)) ≤ b + δ := hN2 n (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hlow : (-(b + δ)) ≤ y.approx n := by
      have h1 : (-(b + δ)) ≤ (-(-(y.approx n))) := Q'.neg_le_neg hlb'
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    have hbδ0 : (0 : Q') ≤ b + δ :=
      Q'.le_trans' _ _ _ hb (Q'.add_le_self_of_nonneg b δ (Q'.le_of_lt hδpos))
    show (c * y.approx n) ≤ Bc * b + ε
    have hbnd := Q'.mul_le_of_bounds hBc hbδ0 hvlow hc1 hlow hub
    -- hbnd : c·y_n ≤ Bc·(b+δ)
    refine Q'.le_trans' _ _ _ hbnd ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv Bc b δ)) ?_
    exact Q'.add_le_add_left (Bc * b) (Bc * δ) ε hδ
  · -- leRat (neg (c·y)) (Bc·b)
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hBc hε
    obtain ⟨N, hN⟩ := hy.1 δ hδpos
    obtain ⟨N2, hN2⟩ := hy.2 δ hδpos
    refine ⟨max N N2, fun n hn => ?_⟩
    have hub : y.approx n ≤ b + δ := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hlb' : (-(y.approx n)) ≤ b + δ := hN2 n (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hlow : (-(b + δ)) ≤ y.approx n := by
      have h1 : (-(b + δ)) ≤ (-(-(y.approx n))) := Q'.neg_le_neg hlb'
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    have hbδ0 : (0 : Q') ≤ b + δ :=
      Q'.le_trans' _ _ _ hb (Q'.add_le_self_of_nonneg b δ (Q'.le_of_lt hδpos))
    show (-(c * y.approx n)) ≤ Bc * b + ε
    -- −(c·y_n) = c·(−y_n) ; bound with −(b+δ) ≤ −y_n ≤ b+δ
    have hyn_low : (-(b + δ)) ≤ (-(y.approx n)) := Q'.neg_le_neg hub
    have hbnd := Q'.mul_le_of_bounds hBc hbδ0 hvlow hc1 hyn_low hlb'
    -- hbnd : c·(−y_n) ≤ Bc·(b+δ)
    have hrw : (-(c * y.approx n)) ≈ (c * (-(y.approx n))) :=
      Q'.eqv_symm (Q'.mul_neg_eqv c (y.approx n))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrw) ?_
    refine Q'.le_trans' _ _ _ hbnd ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv Bc b δ)) ?_
    exact Q'.add_le_add_left (Bc * b) (Bc * δ) ε hδ


/-- The crux cancellation `hf·hf·L·(S+S) ≈ hf·(S·L)` given `hf+hf ≈ 1`. -/
private theorem crux_cancel (hf S L : Q') (hfsum : (hf + hf) ≈ (1 : Q')) :
    ((hf * hf) * (L * (S + S))) ≈ (hf * (S * L)) := by
  calc (hf * hf) * (L * (S + S))
      ≈ (hf * hf) * ((S + S) * L) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv L (S + S))
    _ ≈ (hf * hf) * ((S * L) + (S * L)) :=
        Q'.mul_eqv_congr_left _ _ _ (Cheb.add_mul_eqv S S L)
    _ ≈ (hf * hf) * (S * (L + L)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv S L L))
    _ ≈ hf * (hf * (S * (L + L))) := Q'.mul_assoc_eqv hf hf (S * (L + L))
    _ ≈ hf * ((hf * S) * (L + L)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv hf S (L + L)))
    _ ≈ hf * ((hf * S) * (L * (1 + 1))) := by
        refine Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ ?_)
        -- L + L ≈ L·(1+1)
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv L 1 1) ?_
        exact Cheb.add_eqv_congr _ _ _ _ (Q'.mul_one_eqv L) (Q'.mul_one_eqv L)
    _ ≈ hf * (((hf * S) * L) * (1 + 1)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (hf * S) L (1 + 1)))
    _ ≈ hf * ((1 + 1) * ((hf * S) * L)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv ((hf * S) * L) (1 + 1))
    _ ≈ hf * (((1 + 1) * (hf * S)) * L) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (1 + 1) (hf * S) L))
    _ ≈ hf * ((((1 + 1) * hf) * S) * L) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (1 + 1) hf S)))
    _ ≈ hf * (((hf + hf) * S) * L) := by
        refine Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ ?_))
        -- (1+1)·hf ≈ hf + hf
        refine Q'.eqv_trans _ _ _ (Cheb.add_mul_eqv 1 1 hf) ?_
        exact Cheb.add_eqv_congr _ _ _ _ (Q'.one_mul_eqv hf) (Q'.one_mul_eqv hf)
    _ ≈ hf * (((1 : Q') * S) * L) := by
        refine Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hfsum))
    _ ≈ hf * (S * L) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv S))

theorem bracketLeg_index_abstract (hf A B S D R L : Q') (hfsum : (hf + hf) ≈ (1 : Q'))
    (hD : D ≈ (R + L)) :
    (hf * (hf * ((A + B) * D)) + (-(S * (hf * L))))
      ≈ ((hf * hf) * L * ((A + B) + (-(S + S))) + (hf * hf) * ((A + B) * R)) := by
  -- substitute D ≈ R + L on the left
  have hstep1 : (hf * (hf * ((A + B) * D)) + (-(S * (hf * L))))
      ≈ (hf * (hf * ((A + B) * (R + L))) + (-(S * (hf * L)))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hD)))
  refine Q'.eqv_trans _ _ _ hstep1 ?_
  -- Expand LHS:  hf·(hf·((A+B)·(R+L))) ≈ (hf·hf)·((A+B)·R) + (hf·hf)·((A+B)·L)
  have hLexp : (hf * (hf * ((A + B) * (R + L))) + (-(S * (hf * L))))
      ≈ (((hf * hf) * ((A + B) * R) + (hf * hf) * ((A + B) * L)) + (-(S * (hf * L)))) := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    calc hf * (hf * ((A + B) * (R + L)))
        ≈ (hf * hf) * ((A + B) * (R + L)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv hf hf ((A + B) * (R + L)))
      _ ≈ (hf * hf) * ((A + B) * R + (A + B) * L) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv (A + B) R L)
      _ ≈ (hf * hf) * ((A + B) * R) + (hf * hf) * ((A + B) * L) :=
          Q'.mul_add_eqv (hf * hf) ((A + B) * R) ((A + B) * L)
  refine Q'.eqv_trans _ _ _ hLexp ?_
  -- Expand RHS:  (hf·hf)·L·((A+B) − (S+S)) + (hf·hf)·((A+B)·R)
  --           ≈ (hf·hf)·((A+B)·L) + (−((hf·hf)·(L·(S+S)))) + (hf·hf)·((A+B)·R)
  have hRexp : ((hf * hf) * L * ((A + B) + (-(S + S))) + (hf * hf) * ((A + B) * R))
      ≈ (((hf * hf) * ((A + B) * L) + (-((hf * hf) * (L * (S + S)))))
          + (hf * hf) * ((A + B) * R)) := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    calc (hf * hf) * L * ((A + B) + (-(S + S)))
        ≈ (hf * hf) * (L * ((A + B) + (-(S + S)))) := Q'.mul_assoc_eqv (hf * hf) L _
      _ ≈ (hf * hf) * (L * (A + B) + L * (-(S + S))) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv L (A + B) (-(S + S)))
      _ ≈ (hf * hf) * (L * (A + B)) + (hf * hf) * (L * (-(S + S))) :=
          Q'.mul_add_eqv (hf * hf) (L * (A + B)) (L * (-(S + S)))
      _ ≈ (hf * hf) * ((A + B) * L) + (hf * hf) * (L * (-(S + S))) :=
          Q'.add_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv L (A + B)))
      _ ≈ (hf * hf) * ((A + B) * L) + (-((hf * hf) * (L * (S + S)))) := by
          refine Q'.add_eqv_congr_left _ _ _ ?_
          -- (hf·hf)·(L·(−(S+S))) ≈ −((hf·hf)·(L·(S+S)))
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv L (S + S))) ?_
          exact Q'.mul_neg_eqv (hf * hf) (L * (S + S))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hRexp)
  -- n1 ≈ n2 :  −(S·(hf·L)) ≈ −((hf·hf)·(L·(S+S)))
  have hn : (-(S * (hf * L))) ≈ (-((hf * hf) * (L * (S + S)))) := by
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (crux_cancel hf S L hfsum))
    calc S * (hf * L)
        ≈ (S * hf) * L := Q'.eqv_symm (Q'.mul_assoc_eqv S hf L)
      _ ≈ (hf * S) * L := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv S hf)
      _ ≈ hf * (S * L) := Q'.mul_assoc_eqv hf S L
  -- (P + Q) + n1 ≈ (Q + n2) + P
  calc ((hf * hf) * ((A + B) * R) + (hf * hf) * ((A + B) * L)) + (-(S * (hf * L)))
      ≈ ((hf * hf) * ((A + B) * R) + (hf * hf) * ((A + B) * L))
          + (-((hf * hf) * (L * (S + S)))) := Q'.add_eqv_congr_left _ _ _ hn
    _ ≈ (hf * hf) * ((A + B) * R)
          + ((hf * hf) * ((A + B) * L) + (-((hf * hf) * (L * (S + S))))) :=
        Q'.add_assoc_eqv _ _ _
    _ ≈ ((hf * hf) * ((A + B) * L) + (-((hf * hf) * (L * (S + S)))))
          + (hf * hf) * ((A + B) * R) :=
        Q'.add_comm_eqv _ _

/-! ## 3. The per-cell bracket-leg decomposition `legBr − LZA ≈ TermA + TermB` -/

/-- The half constant (matching the private `half` of the leg defs). -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The quarter constant `¼ = ½·½`. -/
def quarter : Q' := half * half

/-- Term A: `¼·(lebW·g)·Δ₂` (`Δ₂ = symmD`, `g = Bderiv e he x_k`). -/
def TermA (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.mul
    (CReal.ofQ' (quarter * (SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))))
    (ChebOrthoTightModulus.symmD M hM k)

/-- Term B: `¼·(s_+ + s_-)·R_B`. -/
def TermB (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' quarter)
    (CReal.mul (ChebOrthoTightModulus.radSum M hM k)
      (CReal.ofQ' (ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM))))

/-- `half + half ≈ 1`. -/
private theorem half_add_half : (half + half) ≈ (1 : Q') := by decide

/-- **The per-cell bracket-leg decomposition.**
`legBr − LZA ≈ TermA + TermB`, the pointwise instantiation of
`bracketLeg_index_abstract` at the cell data (using the bracket-difference
identity `bracketDiff_eqv`). -/
theorem br_decomp (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv
      (CReal.add (ChebOrthoSecondDiff.legBr e he M hM k)
        (CReal.neg (ChebOrthoSecondDiff.LZA e he M hM k)))
      (CReal.add (TermA e he M hM k) (TermB e he M hM k)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    have hD := bracketDiff_eqv e he M hM k
    exact bracketLeg_index_abstract half
      ((ChebOrthoMidpoint.bdyRadical M hM (k + 1)).approx p)
      ((ChebOrthoMidpoint.bdyRadical M hM k).approx p)
      ((SemicircleIntegral.nodeWeight M hM k).approx p)
      (Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
        + (-(Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))))
      (ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM))
      (SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))
      half_add_half hD)

/-! ## 4. Bounding Term A: `AbsLeRat TermA (quarter·gradedRate)` (all M) -/

/-- `mkPos a D ≤ mkPos b E` from the cross-multiplied `Int` inequality `a·E ≤ b·D`. -/
theorem mkPos_le_mkPos {a b : Int} {D E : Nat} (hD : 0 < D) (hE : 0 < E)
    (h : a * (E : Int) ≤ b * (D : Int)) :
    Q'.mkPos a D hD ≤ Q'.mkPos b E hE := by
  show (Q'.mkPos a D hD).num * ((Q'.mkPos b E hE).den : Int)
      ≤ (Q'.mkPos b E hE).num * ((Q'.mkPos a D hD).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]; exact h

/-- `quarter·lebW ≈ mkPos 2 (4·M)`. -/
theorem quarter_lebW_eqv (M : Nat) (hM : 0 < M) :
    (quarter * SemicircleIntegral.lebW M hM) ≈ Q'.mkPos 2 (4 * M) (by omega) := by
  show (quarter * SemicircleIntegral.lebW M hM).num * ((Q'.mkPos 2 (4 * M) (by omega)).den : Int)
      = (Q'.mkPos 2 (4 * M) (by omega)).num * ((quarter * SemicircleIntegral.lebW M hM).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    show (quarter * SemicircleIntegral.lebW M hM).num = quarter.num * (SemicircleIntegral.lebW M hM).num from rfl]
  -- quarter = mkPos 1 4 ⟹ num 1, den 4 ; lebW = mkPos 2 M ⟹ num 2, den M
  show ((quarter.num) * (Q'.mkPos 2 M hM).num) * ((4 * M : Nat) : Int)
      = (2 : Int) * ((quarter.den : Int) * ((Q'.mkPos 2 M hM).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hqn : quarter.num = 1 := by decide
  have hqd : (quarter.den : Int) = 4 := by decide
  rw [hqn, hqd]; push_cast; omega

/-- `mkPos 2 (4M)·ofNat c ≈ mkPos (2·c) (4M)`. -/
theorem mkPos_mul_ofNat (c M : Nat) (hM : 0 < M) :
    (Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat c) ≈ Q'.mkPos (2 * (c : Int)) (4 * M) (by omega) := by
  show (Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat c).num
        * ((Q'.mkPos (2 * (c : Int)) (4 * M) (by omega)).den : Int)
      = (Q'.mkPos (2 * (c : Int)) (4 * M) (by omega)).num
        * ((Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat c).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    show (Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat c).num
        = (Q'.mkPos 2 (4 * M) (by omega)).num * (Q'.ofNat c).num from rfl]
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show ((2 : Int) * (Q'.ofNat c).num) * ((4 * M : Nat) : Int)
      = (2 * (c : Int)) * (((4 * M : Nat) : Int) * ((Q'.ofNat c).den : Int))
  have hcn : (Q'.ofNat c).num = (c : Int) := rfl
  have hcd : ((Q'.ofNat c).den : Int) = 1 := rfl
  rw [hcn, hcd, Int.mul_one]

/-- `0 ≤ mkPos 2 (4M)`. -/
private theorem mkPos2_nonneg (M : Nat) (hM : 0 < M) :
    (0 : Q') ≤ Q'.mkPos 2 (4 * M) (by omega) := by
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide

/-- **`cA` is two-sided bounded by `mkPos (2·Bbound e) (4M)`** on the interior cell.
`cA = ¼·(lebW·g)`, `|g| ≤ Bbound e` (`Bderiv_abs_le`). -/
theorem cA_abs_le (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    (quarter * (SemicircleIntegral.lebW M hM * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))
        ≤ Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
      ∧ (-(quarter * (SemicircleIntegral.lebW M hM
            * Bderiv e he (RiemannSOS.uniformMidpoint M hM k))))
        ≤ Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega) := by
  -- box bounds for x_k
  have hx1 : RiemannSOS.uniformMidpoint M hM k ≤ (1 : Q') := RiemannSOS.node_hi M hM k hk
  have hxm1 : (-(1 : Q')) ≤ RiemannSOS.uniformMidpoint M hM k := RiemannSOS.node_lo M hM k
  obtain ⟨hglo, hghi⟩ := ChebOrthoLegAssembly.Bderiv_abs_le e he
    (RiemannSOS.uniformMidpoint M hM k) hx1 hxm1
  -- cA ≈ mkPos 2 (4M) · g
  have hcAeqv : (quarter * (SemicircleIntegral.lebW M hM
        * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))
      ≈ (Q'.mkPos 2 (4 * M) (by omega) * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv quarter (SemicircleIntegral.lebW M hM)
        (Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (quarter_lebW_eqv M hM)
  -- two-sided bound on mkPos 2 (4M) · g  by  mkPos 2 (4M)·ofNat Bbound
  obtain ⟨hlo, hhi⟩ := ChebOrthoLegAssembly.mul_abs_le (u := Q'.mkPos 2 (4 * M) (by omega))
    (v := Bderiv e he (RiemannSOS.uniformMidpoint M hM k))
    (B := Q'.mkPos 2 (4 * M) (by omega)) (d := Q'.ofNat (ChebOrthoLegAssembly.Bbound e))
    (mkPos2_nonneg M hM) (ChebOrthoLegAssembly.ofNat_nonneg _)
    (by
      -- −mkPos2 ≤ mkPos2
      refine Q'.le_trans' _ (0 : Q') _ ?_ (mkPos2_nonneg M hM)
      have := mkPos2_nonneg M hM
      refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg this) (Q'.le_of_eqv (by decide)))
    (Q'.le_refl' _) hglo hghi
  -- (mkPos2·ofNat Bbound) ≈ mkPos (2Bbound) (4M)
  have hBprod : (Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat (ChebOrthoLegAssembly.Bbound e))
      ≈ Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega) :=
    mkPos_mul_ofNat (ChebOrthoLegAssembly.Bbound e) M hM
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcAeqv) ?_
    exact Q'.le_trans' _ _ _ hhi (Q'.le_of_eqv hBprod)
  · -- −cA ≈ −(u·v) ≤ B·d ≈ mkPos(2Bbound)
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.ge_of_eqv hcAeqv)) ?_
    -- −(u·v) ≤ B·d  from  −(B·d) ≤ u·v
    have hneguv : (-(Q'.mkPos 2 (4 * M) (by omega)
          * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))
        ≤ (Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat (ChebOrthoLegAssembly.Bbound e)) := by
      have h1 : (-(Q'.mkPos 2 (4 * M) (by omega)
            * Bderiv e he (RiemannSOS.uniformMidpoint M hM k)))
          ≤ (-(-(Q'.mkPos 2 (4 * M) (by omega) * Q'.ofNat (ChebOrthoLegAssembly.Bbound e)))) :=
        Q'.neg_le_neg hlo
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    exact Q'.le_trans' _ _ _ hneguv (Q'.le_of_eqv hBprod)

/-- The tight symmetric-quotient bound rational. -/
private def symmQuot (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ ChebOrthoGraded.jdist M k) : Q' :=
  ((ChebOrthoTightModulus.subSecondQuot_tight M k hM hkn
      + ChebOrthoTightModulus.subSecondQuot_tight M k hM hkn)
      + ChebOrthoTightModulus.twoDeltaSq M hM)
    * Q'.recipPos (ChebOrthoInterior.recipWitness M (ChebOrthoGraded.jdist M k) hM)
        (ChebOrthoInterior.recipWitness_pos M (ChebOrthoGraded.jdist M k) hM hj)

private theorem symmQuot_nonneg (M k : Nat) (hM : 0 < M) (hkn : k < M)
    (hj : 2 ≤ ChebOrthoGraded.jdist M k) : (0 : Q') ≤ symmQuot M k hM hkn hj := by
  refine Q'.mul_nonneg _ _ ?_ (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _
    (ChebOrthoTightModulus.subSecondQuot_tight_nonneg M k hM hkn)
    (ChebOrthoTightModulus.subSecondQuot_tight_nonneg M k hM hkn))
    (ChebOrthoTightModulus.twoDeltaSq_nonneg M hM)

/-- `0 ≤ mkPos (2·Bbound) (4M)`. -/
private theorem BcA_nonneg (e M : Nat) (hM : 0 < M) :
    (0 : Q') ≤ Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega) := by
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  have : (0 : Int) ≤ (ChebOrthoLegAssembly.Bbound e : Int) := Int.natCast_nonneg _
  omega

/-- **Term A bound.**  `AbsLeRat TermA (BcA · symmQuot)`. -/
theorem termA_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ ChebOrthoGraded.jdist M k) :
    AbsLeRat (TermA e he M hM k)
      (Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
        * symmQuot M k hM hkn hj) := by
  obtain ⟨hca1, hca2⟩ := cA_abs_le e he M hM k hkn
  have hsymm : AbsLeRat (ChebOrthoTightModulus.symmD M hM k) (symmQuot M k hM hkn hj) :=
    ChebOrthoTightModulus.symmSecondDiff_tight_AbsLeRat M hM k hk0 hkn hk1n hj
  exact AbsLeRat.ofQ'_smul hsymm hca1 hca2 (BcA_nonneg e M hM) (symmQuot_nonneg M k hM hkn hj)

/-- `mkPos a D · mkPos b E ≈ mkPos (a·b) (D·E)`. -/
theorem mkPos_mul_mkPos (a b : Int) (D E : Nat) (hD : 0 < D) (hE : 0 < E) :
    (Q'.mkPos a D hD * Q'.mkPos b E hE) ≈ Q'.mkPos (a * b) (D * E) (Nat.mul_pos hD hE) := by
  show (Q'.mkPos a D hD * Q'.mkPos b E hE).num * ((Q'.mkPos (a * b) (D * E) (Nat.mul_pos hD hE)).den : Int)
      = (Q'.mkPos (a * b) (D * E) (Nat.mul_pos hD hE)).num
        * ((Q'.mkPos a D hD * Q'.mkPos b E hE).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    show (Q'.mkPos a D hD * Q'.mkPos b E hE).num = (Q'.mkPos a D hD).num * (Q'.mkPos b E hE).num from rfl]
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  show (a * b) * ((D * E : Nat) : Int) = (a * b) * (((D : Nat) : Int) * ((E : Nat) : Int))
  rw [Int.natCast_mul]

/-- `quarter·gradedRate ≈ mkPos cRateNum (4·(isqrt M·(j·j)))` at an interior cell. -/
theorem quarter_gradedRate_eqv (e M k : Nat) (hM : 0 < M) (hk : k < M) :
    (quarter * ChebOrthoGraded.gradedRate e M hM k)
      ≈ Q'.mkPos (ChebOrthoMidpointCore.cRateNum e : Int)
          (4 * (ChebOrthoMidpointEst.isqrt M * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k)))
          (by
            have hj : 0 < ChebOrthoGraded.jdist M k := ChebOrthoGraded.jdist_pos hk
            have hq : 0 < ChebOrthoMidpointEst.isqrt M := ChebOrthoMidpointEst.isqrt_pos hM
            have : 0 < ChebOrthoMidpointEst.isqrt M * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) :=
              Nat.mul_pos hq (Nat.mul_pos hj hj)
            omega) := by
  have hj : 0 < ChebOrthoGraded.jdist M k := ChebOrthoGraded.jdist_pos hk
  have hq : 0 < ChebOrthoMidpointEst.isqrt M := ChebOrthoMidpointEst.isqrt_pos hM
  -- gradedRate = scaledTerm e M j = mkPos cRateNum (isqrt M·(j·j))
  have hgr : ChebOrthoGraded.gradedRate e M hM k
      = Q'.mkPos (ChebOrthoMidpointCore.cRateNum e : Int)
          (ChebOrthoMidpointEst.isqrt M * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k))
          (Nat.mul_pos hq (Nat.mul_pos hj hj)) := by
    show ChebOrthoGraded.scaledTerm e M hM (ChebOrthoGraded.jdist M k) = _
    unfold ChebOrthoGraded.scaledTerm
    rw [dif_pos hj]
  rw [hgr]
  -- quarter = mkPos 1 4 ; product
  have hquar : quarter = Q'.mkPos 1 4 (by decide) := by decide
  rw [hquar]
  refine Q'.eqv_trans _ _ _
    (mkPos_mul_mkPos 1 (ChebOrthoMidpointCore.cRateNum e : Int) 4
      (ChebOrthoMidpointEst.isqrt M * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k))
      (by decide) (Nat.mul_pos hq (Nat.mul_pos hj hj))) ?_
  -- mkPos (1·cRateNum) (4·(...)) ≈ mkPos cRateNum (4·(...))
  refine mkPos_num_eqv _ _ ?_
  omega

/-- Bridge the Int-grouped cross-multiplication goal to the Nat monomial inequality
`(176·bb·q)·jj ≤ (4·cn·M)·jj` (with `jj = j·j`).  Reassociation is done by extracting
the common `jj` factor and `Int.mul_le_mul_of_nonneg_right`. -/
theorem intMono4 (bb q cn M j : Nat) (hjpos : 0 < j)
    (h : (176 * bb * q) * (j * j) ≤ (4 * cn * M) * (j * j)) :
    (2 * (bb : Int)) * 22 * ((4 * (q * (j * j)) : Nat) : Int)
      ≤ (cn : Int) * (((4 * M) * (j * j) : Nat) : Int) := by
  -- rewrite both sides as (Nat-coeff : Int) * (j·j : Int)
  have hcoefL : 2 * bb * 22 * (4 * q) = 176 * bb * q := by
    rw [show (176 : Nat) = 2 * 22 * 4 from rfl]; ac_rfl
  have hcoefR : cn * (4 * M) = 4 * cn * M := by ac_rfl
  have hL : (2 * (bb : Int)) * 22 * ((4 * (q * (j * j)) : Nat) : Int)
      = (((176 * bb * q : Nat)) : Int) * ((j * j : Nat) : Int) := by
    have e1 : ((4 * (q * (j * j)) : Nat) : Int) = ((4 * q : Nat) : Int) * ((j * j : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc]
    rw [e1, ← Int.mul_assoc]
    refine congrArg (· * ((j * j : Nat) : Int)) ?_
    rw [show (2 * (bb : Int)) * 22 * ((4 * q : Nat) : Int) = ((2 * bb * 22 * (4 * q) : Nat) : Int) from by
      push_cast; rfl]
    rw [hcoefL]
  have hR : (cn : Int) * (((4 * M) * (j * j) : Nat) : Int)
      = (((4 * cn * M : Nat)) : Int) * ((j * j : Nat) : Int) := by
    have e2 : (((4 * M) * (j * j) : Nat) : Int) = ((4 * M : Nat) : Int) * ((j * j : Nat) : Int) := by
      push_cast; rfl
    rw [e2, ← Int.mul_assoc]
    refine congrArg (· * ((j * j : Nat) : Int)) ?_
    rw [show (cn : Int) * ((4 * M : Nat) : Int) = ((cn * (4 * M) : Nat) : Int) from by
      push_cast; rfl]
    rw [hcoefR]
  rw [hL, hR]
  refine Int.mul_le_mul_of_nonneg_right ?_ (Int.natCast_nonneg _)
  have hjjpos : 0 < j * j := Nat.mul_pos hjpos hjpos
  have : ((176 * bb * q : Nat)) ≤ ((4 * cn * M : Nat)) :=
    Nat.le_of_mul_le_mul_right h hjjpos
  exact Int.ofNat_le.mpr this

/-- The Term-A threshold `M₀ = (44·Bbound e)²`. -/
def M0A (e : Nat) : Nat := (44 * ChebOrthoLegAssembly.Bbound e) * (44 * ChebOrthoLegAssembly.Bbound e)

/-- **Term A cross-mult.**  `BcA · symmQuot ≤ quarter · gradedRate` for `M ≥ M₀A e`. -/
theorem BcA_symmQuot_le (e M k : Nat) (hM : 0 < M) (hk0 : 0 < k) (hkn : k < M)
    (hk1n : k + 1 < M) (hj : 2 ≤ ChebOrthoGraded.jdist M k) (hthr : M0A e ≤ M) :
    (Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
        * symmQuot M k hM hkn hj)
      ≤ quarter * ChebOrthoGraded.gradedRate e M hM k := by
  have hjpos : 0 < ChebOrthoGraded.jdist M k := ChebOrthoGraded.jdist_pos hkn
  have hjj : 0 < ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k := Nat.mul_pos hjpos hjpos
  have hq : 0 < ChebOrthoMidpointEst.isqrt M := ChebOrthoMidpointEst.isqrt_pos hM
  -- (1) symmQuot ≤ mkPos 22 (j·j)
  have hsq : symmQuot M k hM hkn hj
      ≤ Q'.mkPos 22 (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) hjj :=
    ChebOrthoTightModulus.symmQuot_tight_le_recip_sq M hM k hkn hk1n hj
  -- (2) BcA · symmQuot ≤ BcA · mkPos 22 (j·j)
  have hstep1 : (Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
        * symmQuot M k hM hkn hj)
      ≤ (Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
        * Q'.mkPos 22 (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) hjj) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq (BcA_nonneg e M hM)
  refine Q'.le_trans' _ _ _ hstep1 ?_
  -- (3) BcA · mkPos 22 (j²) ≈ mkPos (44·Bbound) (4M·(j²))
  have hprod : (Q'.mkPos (2 * (ChebOrthoLegAssembly.Bbound e : Int)) (4 * M) (by omega)
        * Q'.mkPos 22 (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) hjj)
      ≈ Q'.mkPos ((2 * (ChebOrthoLegAssembly.Bbound e : Int)) * 22)
          ((4 * M) * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k))
          (Nat.mul_pos (by omega) hjj) :=
    mkPos_mul_mkPos _ _ _ _ _ _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hprod) ?_
  -- (4) ≤ quarter·gradedRate ≈ mkPos cRateNum (4·(isqrt M·j²))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (quarter_gradedRate_eqv e M k hM hkn))
  -- mkPos (44Bbound) (4M·j²) ≤ mkPos cRateNum (4·(isqrt M·j²))
  refine mkPos_le_mkPos _ _ ?_
  -- cross-mult:  (44Bbound)·(4·(isqrt M·j²)) ≤ cRateNum·(4M·j²)
  -- key:  44Bbound·isqrt M ≤ cRateNum·M
  have hisq : 44 * ChebOrthoLegAssembly.Bbound e ≤ ChebOrthoMidpointEst.isqrt M := by
    refine ChebOrthoMidpointEst.isqrt_ge ?_
    -- (44Bbound)² = M0A e ≤ M
    have : M0A e = (44 * ChebOrthoLegAssembly.Bbound e) * (44 * ChebOrthoLegAssembly.Bbound e) := rfl
    omega
  -- 44Bbound·isqrt M ≤ isqrt M·isqrt M ≤ M ≤ cRateNum·M
  have hsqle : ChebOrthoMidpointEst.isqrt M * ChebOrthoMidpointEst.isqrt M ≤ M :=
    ChebOrthoMidpointEst.isqrt_sq_le M
  have hcn1 : 1 ≤ ChebOrthoMidpointCore.cRateNum e := by
    unfold ChebOrthoMidpointCore.cRateNum; omega
  -- The full Nat inequality:  176·bb·q·jj ≤ 4·cn·M·jj
  have hkeyNat : (176 * ChebOrthoLegAssembly.Bbound e * ChebOrthoMidpointEst.isqrt M)
        * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k)
      ≤ (4 * ChebOrthoMidpointCore.cRateNum e * M)
        * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) := by
    refine Nat.mul_le_mul_right _ ?_
    -- 176·bb·q ≤ 4·cn·M  from 44·bb·q ≤ cn·M
    have hkey : (44 * ChebOrthoLegAssembly.Bbound e) * ChebOrthoMidpointEst.isqrt M
        ≤ ChebOrthoMidpointCore.cRateNum e * M := by
      have h1 : (44 * ChebOrthoLegAssembly.Bbound e) * ChebOrthoMidpointEst.isqrt M
          ≤ ChebOrthoMidpointEst.isqrt M * ChebOrthoMidpointEst.isqrt M :=
        Nat.mul_le_mul_right _ hisq
      have h2 : ChebOrthoMidpointEst.isqrt M * ChebOrthoMidpointEst.isqrt M
          ≤ ChebOrthoMidpointCore.cRateNum e * M := by
        refine Nat.le_trans hsqle ?_
        calc M = 1 * M := (Nat.one_mul M).symm
          _ ≤ ChebOrthoMidpointCore.cRateNum e * M := Nat.mul_le_mul_right _ hcn1
      exact Nat.le_trans h1 h2
    -- 176·bb·q = 4·(44·bb·q) ≤ 4·(cn·M) = 4·cn·M
    have h4 : 4 * ((44 * ChebOrthoLegAssembly.Bbound e) * ChebOrthoMidpointEst.isqrt M)
        ≤ 4 * (ChebOrthoMidpointCore.cRateNum e * M) := Nat.mul_le_mul_left _ hkey
    have heL : 176 * ChebOrthoLegAssembly.Bbound e * ChebOrthoMidpointEst.isqrt M
        = 4 * ((44 * ChebOrthoLegAssembly.Bbound e) * ChebOrthoMidpointEst.isqrt M) := by
      rw [show (176 : Nat) = 4 * 44 from rfl]; ac_rfl
    have heR : 4 * ChebOrthoMidpointCore.cRateNum e * M
        = 4 * (ChebOrthoMidpointCore.cRateNum e * M) := by ac_rfl
    rw [heL, heR]; exact h4
  -- Int cross-mult:  (2bb·22)·(4·(q·j²)) ≤ cRateNum·(4M·j²)
  show (2 * (ChebOrthoLegAssembly.Bbound e : Int)) * 22
        * ((4 * (ChebOrthoMidpointEst.isqrt M
            * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k)) : Nat) : Int)
      ≤ (ChebOrthoMidpointCore.cRateNum e : Int)
        * (((4 * M) * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) : Nat) : Int)
  have hkeyI : ((176 * ChebOrthoLegAssembly.Bbound e * ChebOrthoMidpointEst.isqrt M)
        * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) : Nat)
      ≤ (((4 * ChebOrthoMidpointCore.cRateNum e * M)
        * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k) : Nat)) := hkeyNat
  -- Cast both sides to the Nat monomials and compare via hkeyNat.  Use the helper
  -- `intMono4` to bridge the Int-grouped products to the Nat casts.
  refine intMono4 (ChebOrthoLegAssembly.Bbound e) (ChebOrthoMidpointEst.isqrt M)
    (ChebOrthoMidpointCore.cRateNum e) M (ChebOrthoGraded.jdist M k) hjpos hkeyNat

/-- **Term A vs `¼·gradedRate`.**  `AbsLeRat TermA (quarter·gradedRate)` for `M ≥ M₀A e`. -/
theorem termA_le_quarter (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ ChebOrthoGraded.jdist M k)
    (hthr : M0A e ≤ M) :
    AbsLeRat (TermA e he M hM k) (quarter * ChebOrthoGraded.gradedRate e M hM k) :=
  AbsLeRat.mono (termA_AbsLeRat e he M hM k hk0 hkn hk1n hj)
    (BcA_symmQuot_le e M k hM hk0 hkn hk1n hj hthr)

/-! ## 5. Bounding Term B: `AbsLeRat TermB (quarter·gradedRate)` (M ≥ M₀B) -/

/-- `geRat radSum 0` (the √-sum is nonnegative). -/
theorem radSum_geRat_zero (M : Nat) (hM : 0 < M) (k : Nat) :
    ExpPos.geRat (ChebOrthoTightModulus.radSum M hM k) (0 : Q') := by
  refine ExpPos.geRat_of_eventually ⟨0, fun n _ => ?_⟩
  show (0 : Q') ≤ ((ChebOrthoMidpoint.bdyRadical M hM (k + 1)).approx n
      + (ChebOrthoMidpoint.bdyRadical M hM k).approx n)
  exact Q'.zero_le_add _ _
    (ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n)
    (ChebOrthoInterior.bdyRadical_approx_nonneg M hM k n)

/-- `leRat radSum 2` (each radical `≤ 1`). -/
theorem radSum_leRat_two (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M)
    (hk1n : k + 1 < M) :
    CReal.leRat (ChebOrthoTightModulus.radSum M hM k) (1 + 1 : Q') := by
  have h1 := ChebOrthoOffDiagClose.bdyRadical_le_one M hM (k + 1) (by omega) hk1n
  have h0 := ChebOrthoOffDiagClose.bdyRadical_le_one M hM k hk0 hkn
  exact CReal.leRat_add h1.1 h0.1

/-- The Term-B remainder constant `C(e) = KA(e−1)+KA(e+1)`. -/
def Cnum (e : Nat) : Nat := ChebMarkovModulus.KA (e - 1) + ChebMarkovModulus.KA (e + 1)

/-- **`|R_B| ≤ C(e)·δ³`** at the interior cell. -/
theorem RB_abs_le (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) :
    ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM)
        ≤ Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM)
      ∧ (-(ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM)))
        ≤ Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM) := by
  have hbox := ChebOrthoOffDiagClose.OnBox_node M hM k hkn
  have hcb := ChebMarkovModulus.bracketCubeBound_holds e he
      (RiemannSOS.uniformMidpoint M hM k) (delta M hM) hbox
  exact hcb

/-- **Term B bound (symbolic).**  `AbsLeRat TermB (quarter·(2·(C·δ³)))`. -/
theorem termB_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat (TermB e he M hM k)
      (quarter * ((1 + 1 : Q')
        * (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM)))) := by
  obtain ⟨hrb1, hrb2⟩ := RB_abs_le e he M hM k hkn
  have hC0 : (0 : Q') ≤ Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM) := by
    refine Q'.mul_nonneg _ _ (ChebOrthoLegAssembly.ofNat_nonneg _) ?_
    have hd0 : (0 : Q') ≤ delta M hM := by
      show (0 : Q') ≤ Q'.mkPos 1 M hM
      rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hd0 hd0) hd0
  have h2 : (0 : Q') ≤ (1 + 1 : Q') := by decide
  -- inner: mul radSum (ofQ' R_B)
  have hinner : AbsLeRat
      (CReal.mul (ChebOrthoTightModulus.radSum M hM k)
        (CReal.ofQ' (ChebBracketTaylor.R_B e he (RiemannSOS.uniformMidpoint M hM k) (delta M hM))))
      ((1 + 1 : Q') * (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM))) :=
    AbsLeRat.mul_nonneg_ofQ' (radSum_geRat_zero M hM k) (radSum_leRat_two M hM k hk0 hkn hk1n)
      hrb1 hrb2 h2 hC0
  -- outer: smul by quarter ≥ 0
  have hq0 : (0 : Q') ≤ quarter := by
    show (0 : Q') ≤ half * half
    exact Q'.mul_nonneg _ _ (by decide) (by decide)
  exact AbsLeRat.smul_nonneg hq0 hinner

/-- `mkPos a D ≈ mkPos b E` when `a = b` and `D = E` as values. -/
theorem mkPos_eqv_val {a b : Int} {D E : Nat} (hD : 0 < D) (hE : 0 < E)
    (ha : a = b) (hde : D = E) : Q'.mkPos a D hD ≈ Q'.mkPos b E hE := by
  subst ha; subst hde; exact Q'.eqv_refl _

/-- `(δ·δ)·δ ≈ mkPos 1 (M·M·M)`. -/
theorem delta_cube_eqv (M : Nat) (hM : 0 < M) :
    ((delta M hM * delta M hM) * delta M hM)
      ≈ Q'.mkPos 1 (M * M * M) (Nat.mul_pos (Nat.mul_pos hM hM) hM) := by
  have hd2 : (delta M hM * delta M hM) ≈ Q'.mkPos (1 * 1) (M * M) (Nat.mul_pos hM hM) :=
    mkPos_mul_mkPos 1 1 M M hM hM
  have hd2' : (delta M hM * delta M hM) ≈ Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM) :=
    Q'.eqv_trans _ _ _ hd2 (mkPos_num_eqv (M * M) (Nat.mul_pos hM hM) (by decide))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hd2') ?_
  refine Q'.eqv_trans _ _ _ (mkPos_mul_mkPos 1 1 (M * M) M (Nat.mul_pos hM hM) hM) ?_
  exact mkPos_num_eqv (M * M * M) (Nat.mul_pos (Nat.mul_pos hM hM) hM) (by decide)

/-- `ofNat C · mkPos 1 D ≈ mkPos C D`. -/
theorem ofNat_mul_recip (C D : Nat) (hD : 0 < D) :
    (Q'.ofNat C * Q'.mkPos 1 D hD) ≈ Q'.mkPos (C : Int) D hD := by
  show (Q'.ofNat C * Q'.mkPos 1 D hD).num * ((Q'.mkPos (C : Int) D hD).den : Int)
      = (Q'.mkPos (C : Int) D hD).num * ((Q'.ofNat C * Q'.mkPos 1 D hD).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    show (Q'.ofNat C * Q'.mkPos 1 D hD).num = (Q'.ofNat C).num * (Q'.mkPos 1 D hD).num from rfl]
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show ((Q'.ofNat C).num * 1) * (D : Int) = (C : Int) * (((Q'.ofNat C).den : Int) * (D : Int))
  have hcn : (Q'.ofNat C).num = (C : Int) := rfl
  have hcd : ((Q'.ofNat C).den : Int) = 1 := rfl
  rw [hcn, hcd]; rw [Int.mul_one, Int.one_mul]

/-- `BcB ≈ mkPos (2·C) (4·(M·M·M))`. -/
theorem BcB_eqv (e M : Nat) (hM : 0 < M) :
    (quarter * ((1 + 1 : Q')
        * (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM))))
      ≈ Q'.mkPos (2 * (Cnum e : Int)) (4 * (M * M * M))
          (Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos hM hM) hM)) := by
  have hMMM : 0 < M * M * M := Nat.mul_pos (Nat.mul_pos hM hM) hM
  -- ofNat C·δ³ ≈ ofNat C·mkPos 1 M³ ≈ mkPos C M³
  have hCd : (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM))
      ≈ Q'.mkPos (Cnum e : Int) (M * M * M) hMMM := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (delta_cube_eqv M hM)) ?_
    exact ofNat_mul_recip (Cnum e) (M * M * M) hMMM
  -- (1+1)·that ≈ mkPos 2 1 · mkPos C M³ ≈ mkPos (2C) M³
  have h2C : ((1 + 1 : Q') * (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM)))
      ≈ Q'.mkPos (2 * (Cnum e : Int)) (M * M * M) hMMM := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hCd) ?_
    -- (1+1) ≈ mkPos 2 1, then product
    have h11 : (1 + 1 : Q') ≈ Q'.mkPos 2 1 (by decide) := by decide
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h11) ?_
    refine Q'.eqv_trans _ _ _ (mkPos_mul_mkPos 2 (Cnum e : Int) 1 (M * M * M) (by decide) hMMM) ?_
    exact mkPos_eqv_val _ hMMM (by omega) (by omega)
  -- quarter·that ≈ mkPos 1 4·mkPos (2C) M³ ≈ mkPos (2C) (4M³)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h2C) ?_
  have hquar : quarter = Q'.mkPos 1 4 (by decide) := by decide
  rw [hquar]
  refine Q'.eqv_trans _ _ _ (mkPos_mul_mkPos 1 (2 * (Cnum e : Int)) 4 (M * M * M) (by decide) hMMM) ?_
  exact mkPos_eqv_val _ _ (by omega) (by omega)

/-- The Term-B threshold `M₀B = (2·C e)²`. -/
def M0B (e : Nat) : Nat := (2 * Cnum e) * (2 * Cnum e)

/-- Int cross-mult bridge for Term B:
`(2C)·(4·(q·jj)) ≤ cRateNum·(4·MMM)` from the Nat key `(2C·q)·jj ≤ cn·MMM`. -/
theorem intMonoB (Cc q cn MMM j : Nat) (hjpos : 0 < j)
    (h : (2 * Cc * q) * (j * j) ≤ cn * MMM) :
    (2 * (Cc : Int)) * ((4 * (q * (j * j)) : Nat) : Int)
      ≤ (cn : Int) * ((4 * MMM : Nat) : Int) := by
  have hL : (2 * (Cc : Int)) * ((4 * (q * (j * j)) : Nat) : Int)
      = (4 : Int) * (((2 * Cc * q) * (j * j) : Nat) : Int) := by
    push_cast
    rw [show (2 : Int) * (Cc : Int) * (4 * ((q : Int) * ((j : Int) * (j : Int))))
          = 4 * (2 * (Cc : Int) * (q : Int) * ((j : Int) * (j : Int))) from by ac_rfl]
  have hR : (cn : Int) * ((4 * MMM : Nat) : Int) = (4 : Int) * (((cn * MMM : Nat)) : Int) := by
    push_cast
    rw [show (cn : Int) * (4 * (MMM : Int)) = 4 * ((cn : Int) * (MMM : Int)) from by ac_rfl]
  rw [hL, hR]
  refine Int.mul_le_mul_of_nonneg_left ?_ (by decide)
  exact Int.ofNat_le.mpr h

/-- **Term B cross-mult.**  `BcB ≤ quarter·gradedRate` for `M ≥ M₀B e`. -/
theorem BcB_le (e M k : Nat) (hM : 0 < M) (hkn : k < M) (hthr : M0B e ≤ M) :
    (quarter * ((1 + 1 : Q')
        * (Q'.ofNat (Cnum e) * ((delta M hM * delta M hM) * delta M hM))))
      ≤ quarter * ChebOrthoGraded.gradedRate e M hM k := by
  have hjpos : 0 < ChebOrthoGraded.jdist M k := ChebOrthoGraded.jdist_pos hkn
  have hq : 0 < ChebOrthoMidpointEst.isqrt M := ChebOrthoMidpointEst.isqrt_pos hM
  have hMMM : 0 < M * M * M := Nat.mul_pos (Nat.mul_pos hM hM) hM
  -- BcB ≈ mkPos (2C)(4M³)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (BcB_eqv e M hM)) ?_
  -- ≤ quarter·gradedRate ≈ mkPos cRateNum (4·(q·j²))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (quarter_gradedRate_eqv e M k hM hkn))
  refine mkPos_le_mkPos _ _ ?_
  -- (2C)·(4·(q·j²)) ≤ cRateNum·(4·M³)
  -- Nat key: (2C·q)·j² ≤ cn·M³
  have hisq : 2 * Cnum e ≤ ChebOrthoMidpointEst.isqrt M := by
    refine ChebOrthoMidpointEst.isqrt_ge ?_
    have : M0B e = (2 * Cnum e) * (2 * Cnum e) := rfl
    omega
  have hjM : ChebOrthoGraded.jdist M k ≤ M := ChebOrthoTightModulus.jdist_le_M M k hkn
  have hsqle : ChebOrthoMidpointEst.isqrt M * ChebOrthoMidpointEst.isqrt M ≤ M :=
    ChebOrthoMidpointEst.isqrt_sq_le M
  have hcn1 : 1 ≤ ChebOrthoMidpointCore.cRateNum e := by
    unfold ChebOrthoMidpointCore.cRateNum; omega
  -- (2C·q)·j² ≤ cn·M³  :  2C·q ≤ q² ≤ ... ; chain
  have hkeyNat : (2 * Cnum e * ChebOrthoMidpointEst.isqrt M)
        * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k)
      ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * M) := by
    -- 2C·q ≤ q·q ≤ M  (since 2C ≤ q and q·q ≤ M)
    have ha : 2 * Cnum e * ChebOrthoMidpointEst.isqrt M
        ≤ ChebOrthoMidpointEst.isqrt M * ChebOrthoMidpointEst.isqrt M :=
      Nat.mul_le_mul_right _ hisq
    have haM : 2 * Cnum e * ChebOrthoMidpointEst.isqrt M ≤ M := Nat.le_trans ha hsqle
    -- j² ≤ M²
    have hj2 : ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k ≤ M * M :=
      Nat.mul_le_mul hjM hjM
    -- (2C·q)·j² ≤ M·(M·M) = M³ ≤ cn·M³
    have hb : (2 * Cnum e * ChebOrthoMidpointEst.isqrt M)
          * (ChebOrthoGraded.jdist M k * ChebOrthoGraded.jdist M k)
        ≤ M * (M * M) := Nat.mul_le_mul haM hj2
    have hMMMeq : M * (M * M) = M * M * M := by ac_rfl
    have hc : M * M * M ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * M) := by
      calc M * M * M = 1 * (M * M * M) := (Nat.one_mul _).symm
        _ ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * M) := Nat.mul_le_mul_right _ hcn1
    refine Nat.le_trans hb ?_
    rw [hMMMeq]; exact hc
  exact intMonoB (Cnum e) (ChebOrthoMidpointEst.isqrt M) (ChebOrthoMidpointCore.cRateNum e)
    (M * M * M) (ChebOrthoGraded.jdist M k) hjpos hkeyNat

/-- **Term B vs `¼·gradedRate`.**  `AbsLeRat TermB (quarter·gradedRate)` for `M ≥ M₀B e`. -/
theorem termB_le_quarter (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hthr : M0B e ≤ M) :
    AbsLeRat (TermB e he M hM k) (quarter * ChebOrthoGraded.gradedRate e M hM k) :=
  AbsLeRat.mono (termB_AbsLeRat e he M hM k hk0 hkn hk1n) (BcB_le e M k hM hkn hthr)

/-! ## 6. Assembling `EventualBrLegRemainder` -/

/-- `quarter·g + quarter·g ≈ half·g = ChebOrthoLegAssembly.half · g`. -/
private theorem quarter_add_quarter (g : Q') :
    (quarter * g + quarter * g) ≈ (ChebOrthoLegAssembly.half * g) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Cheb.add_mul_eqv quarter quarter g)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  decide

/-- **The eventual bracket-leg remainder.**  Threshold `M₀ = max(M₀A e, M₀B e)`. -/
theorem eventualBrLegRemainder (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) :
    ChebOrthoLegAssembly.EventualBrLegRemainder e he := by
  refine ⟨max (M0A e) (M0B e), fun N k hN hk1 hkN => ?_⟩
  -- M = N+1
  have hM : 0 < N + 1 := Nat.succ_pos N
  -- interior cell bounds:  1 ≤ k ≤ N−1  ⟹  0<k, k<N+1, k+1<N+1, jdist≥2
  have hk0 : 0 < k := hk1
  have hkN' : k ≤ N - 1 := hkN
  have hkn : k < N + 1 := by omega
  have hk1n : k + 1 < N + 1 := by omega
  -- jdist (N+1) k = min (k+1) (N+1−k) ≥ 2  (k≥1 ⟹ k+1≥2 ; k≤N−1 ⟹ N+1−k≥2)
  have hj : 2 ≤ ChebOrthoGraded.jdist (N + 1) k := by
    show 2 ≤ Nat.min (k + 1) ((N + 1) - k)
    refine Nat.le_min.mpr ⟨by omega, by omega⟩
  have hthrA : M0A e ≤ N + 1 := Nat.le_trans (Nat.le_max_left _ _) hN
  have hthrB : M0B e ≤ N + 1 := Nat.le_trans (Nat.le_max_right _ _) hN
  -- per-leg bounds
  have hA := termA_le_quarter e he (N + 1) hM k hk0 hkn hk1n hj hthrA
  have hB := termB_le_quarter e he (N + 1) hM k hk0 hkn hk1n hthrB
  -- add: AbsLeRat (TermA + TermB) (quarter·g + quarter·g)
  have hadd := AbsLeRat.add hA hB
  -- collapse to half·g
  have hcollapse := AbsLeRat.mono hadd
    (Q'.le_of_eqv (quarter_add_quarter (ChebOrthoGraded.gradedRate e (N + 1) hM k)))
  -- transfer back along br_decomp
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv (br_decomp e he (N + 1) hM k) hcollapse

end YMGap.Continuum.ChebOrthoLegProof

#print axioms YMGap.Continuum.ChebOrthoLegProof.eventualBrLegRemainder
#print axioms YMGap.Continuum.ChebOrthoLegProof.br_decomp
#print axioms YMGap.Continuum.ChebOrthoLegProof.termA_le_quarter
#print axioms YMGap.Continuum.ChebOrthoLegProof.termB_le_quarter
#print axioms YMGap.Continuum.ChebOrthoLegProof.bracketLeg_index_abstract
#print axioms YMGap.Continuum.ChebOrthoLegProof.bracketDiff_eqv
#print axioms YMGap.Continuum.ChebOrthoLegProof.U_arg_eqv
