/-
# The constructive dimensional-transmutation limit on the self-similar flow

This module closes the open exp-limit crux of dimensional transmutation **on the
self-similar model flow**: the rescaled lattice margin converges, as a genuine
`CReal` `ConvergesTo`, to the physical gap scale.

## The object

For a block factor `b ≥ 1` and a positive `[0,1]` rational seed `w₀`, the
self-similar exponent flow is `w_k = w₀ / (b+1)^k`, with separators
`sep_k = e^{−w_k}` (`expNeg` of a rational exponent — an irrational real).  The
**rescaled lattice margin** is

    transmuted_k  :=  (b+1)^k · (1 − sep_k)  =  (b+1)^k · (1 − e^{−w_k}),

realised as the `(b+1)^k`-fold `CReal` sum `scaleN ((b+1)^k) (cone − sep_k)`.

## The limit (genuine constructive content)

The two-sided bracket on `1 − e^{−t}` for `0 ≤ t ≤ 1`,

    t − t²  ≤  1 − e^{−t}  ≤  t,

(the upper half is `CReal.oneSub_le_expNeg`; the lower half is proved here from
`e^{−t} ≤ 1/(1+t) ≤ 1 − t + t²`), together with the exact scaling identity
`(b+1)^k · w_k = w₀` and the vanishing quadratic defect
`(b+1)^k · w_k² = w₀·w_k → 0`, squeezes

    w₀ − w₀·w_k  ≤  transmuted_k  ≤  w₀ ,

hence `transmuted_k → w₀` as a `CReal` `ConvergesTo`.  This is
`transmutation_limit_generic`; the concrete corollary
`dimensional_transmutation_limit` fixes `w₀ = 1`, i.e. the separator seed
`sep_0 = e^{−1}`, so the limit is the physical gap scale `w₀ = 1 = −ln(e^{−1})`.

## Honest scope / residual

* This is the limit for the **self-similar model flow** `w_k = w₀ / (b+1)^k`
  (geometric exponents).  The PHYSICAL Yang–Mills RG flow's separators must
  additionally be shown to be self-similar with this geometric law — that is the
  open RG content, NOT discharged here.
* `w₀ = 1` is the genuine `−ln(sep_0) = −ln(e^{−1})` *by construction* (the
  defining exponent of `sep_0` is `1`).  A formal `CReal.log` of the irrational
  `sep_0` is not invoked: the repository's constructive logarithm is built for
  rational arguments (`logRat`), and `sep_0 = e^{−1}` is irrational.

## Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CRealExp` / `SelfSimilarFlow` / `Soundness` backbones;
all moduli are `Type`-level data.  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Constructive.SelfSimilarFlow
import YMGap.Constructive.CRealExp
import YMGap.Constructive.CRealLe
import YMGap.Constructive.ExpPos
import YMGap.Constructive.Soundness
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.CReal

/-! ## 1. Small `Q'` algebra helpers -/

/-- `((u + -t) + (t + d)) ≃ (u + d)` — the middle `-t`/`t` cancel. -/
theorem reassoc_cancel (u t d : Q') : ((u + -t) + (t + d)).eqv (u + d) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv u (-t) (t + d)) ?_
  refine Q'.add_eqv_congr_left u (-t + (t + d)) d ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-t) t d)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (-t + t) 0 d (Q'.neg_add_self_eqv t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 d) ?_
  exact QPoly.q_add_zero_eqv d

/-- `(-a) ≃ (-b)` from `a ≃ b` (neg preserves `Q'` equivalence). -/
theorem neg_eqv {a b : Q'} (h : a.eqv b) : (-a).eqv (-b) := by
  show (-(a.num)) * ((b.den : Int)) = (-(b.num)) * ((a.den : Int))
  have hh : a.num * (b.den : Int) = b.num * (a.den : Int) := h
  rw [Int.neg_mul, Int.neg_mul, hh]

/-- `((a + -b) + b) ≃ a`. -/
theorem cancel_addNeg (a b : Q') : ((a + -b) + b).eqv a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

/-- `(1+t)·(1−t) ≃ 1 − t²` (difference of squares). -/
theorem mul_oneSub (t : Q') : ((1 + t) * (1 + -t)).eqv (1 + -(t * t)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 t (1 + -t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 + -t))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 + -t) (t * (1 + -t)) (t + -(t * t)) ?_) ?_
  · refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv t 1 (-t)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv t)) ?_
    exact Q'.add_eqv_congr_left t (t * -t) (-(t * t)) (Q'.mul_neg_eqv t t)
  · exact reassoc_cancel 1 t (-(t * t))

/-- `(1+t)·((1−t) + t²) ≃ 1 + t³`. -/
theorem poly_id (t : Q') :
    ((1 + t) * ((1 + -t) + t * t)).eqv (1 + t * (t * t)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (1 + t) (1 + -t) (t * t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (mul_oneSub t)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 + -(t * t)) ((1 + t) * (t * t)) ((t * t) + t * (t * t)) ?_) ?_
  · refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 t (t * t)) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (t * t))
  · exact reassoc_cancel 1 (t * t) (t * (t * t))

/-! ## 2. The rational lower bracket `e^{−t} ≤ 1 − t + t²` -/

/-- `0 < 1 + t` for `t ≥ 0`. -/
theorem one_add_pos {t : Q'} (ht : (0 : Q') ≤ t) : (0 : Q') < 1 + t := by
  have hnum : (1 + t).num = (t.den : Int) + t.num := by
    show (1 : Int) * (t.den : Int) + t.num * (((1 : Q').den) : Int) = (t.den : Int) + t.num
    show (1 : Int) * (t.den : Int) + t.num * (1 : Int) = (t.den : Int) + t.num
    rw [Int.one_mul, Int.mul_one]
  have htnum : (0 : Int) ≤ t.num := (Q'.zero_le_iff_num_nonneg t).mp ht
  have htden : (1 : Int) ≤ (t.den : Int) := by have h := t.den_pos; omega
  show (0 : Q').num * (((1 + t).den) : Int) < (1 + t).num * (((0 : Q').den) : Int)
  rw [hnum]
  show (0 : Int) * (((1 + t).den) : Int) < ((t.den : Int) + t.num) * (((0 : Q').den) : Int)
  have hd0 : (((0 : Q').den) : Int) = 1 := rfl
  rw [hd0, Int.mul_one, Int.zero_mul]
  omega

/-- `1/(1+t) ≤ 1 − t + t²` for `t ≥ 0`.  Cancel the positive factor `1+t`:
`(1+t)·(1/(1+t)) ≃ 1 ≤ 1 + t³ ≃ (1+t)·(1 − t + t²)`. -/
theorem oneOver1p_le_quad (t : Q') (ht : (0 : Q') ≤ t) :
    ExpUBInstance.oneOver1p t ≤ (1 + -t) + t * t := by
  have h1t_pos : (0 : Q') < 1 + t := one_add_pos ht
  have hLHS : ((1 + t) * ExpUBInstance.oneOver1p t).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + t) (ExpUBInstance.oneOver1p t))
      (ExpUBInstance.oneOver1p_mul_oneAddX t ht)
  have hRHS : ((1 + t) * ((1 + -t) + t * t)).eqv (1 + t * (t * t)) := poly_id t
  have ht3 : (0 : Q') ≤ t * (t * t) := Q'.mul_nonneg t (t * t) ht (Q'.mul_nonneg t t ht ht)
  have h1le : (1 : Q') ≤ 1 + t * (t * t) := Q'.add_le_self_of_nonneg 1 (t * (t * t)) ht3
  refine Q'.le_of_mul_le_mul_left
    (a := ExpUBInstance.oneOver1p t) (b := (1 + -t) + t * t) (c := 1 + t) ?_ h1t_pos
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  exact Q'.le_trans' _ _ _ h1le (Q'.le_of_eqv (Q'.eqv_symm hRHS))

/-- `e^{−t} ≤ 1 − t + t²` (as the sound rational bound `leRat`). -/
theorem expNeg_le_quad (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (ExpNeg.expNeg t ht) ((1 + -t) + t * t) :=
  CReal.leRat_mono (expNeg_le_oneOver1p t ht) (oneOver1p_le_quad t ht)

/-! ## 3. The margin `1 − e^{−t}` and its two-sided bracket -/

/-- The lattice margin at exponent `q`: `margin q = 1 − e^{−q}`. -/
def margin (q : Q') (hq : (0 : Q') ≤ q) : CReal :=
  CReal.sub CReal.cone (ExpNeg.expNeg q hq)

/-- Lower-bound dual of an upper bound: `leRat X c → geRat (1 − X) (1 − c)`. -/
theorem geRat_sub_cone {X : CReal} {c : Q'} (h : CReal.leRat X c) :
    ExpPos.geRat (CReal.sub CReal.cone X) (1 + -c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  show (1 : Q') + -c ≤ ((1 : Q') + -(X.approx n)) + ε
  have hneg : -c ≤ -(X.approx n) + ε := Q'.neg_le_neg_add hb
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-c) (-(X.approx n) + ε) hneg) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-(X.approx n)) ε))

/-- `(1 + -((1 + -q) + q²)) ≃ q + -q²` — the lower bracket value simplification. -/
theorem boundSimp (q : Q') : ((1 : Q') + -((1 + -q) + q * q)).eqv (q + -(q * q)) := by
  have hnegr : (-((1 + -q) + q * q)).eqv ((-(1 : Q') + q) + -(q * q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 + -q) (q * q)) ?_
    refine Q'.add_eqv_congr_right (-(1 + -q)) (-(1 : Q') + q) (-(q * q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-q)) ?_
    exact Q'.add_eqv_congr_left (-(1 : Q')) (-(-q)) q (Q'.neg_neg_eqv q)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ hnegr) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-(1 : Q') + q) (-(q * q)))) ?_
  refine Q'.add_eqv_congr_right (1 + (-(1 : Q') + q)) q (-(q * q)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-(1 : Q')) q)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (1 + -(1 : Q')) 0 q (Q'.add_neg_self_eqv 1)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 q) ?_
  exact QPoly.q_add_zero_eqv q

/-- **Lower bracket** `q − q² ≤ 1 − e^{−q}` (as `geRat`). -/
theorem margin_geRat (q : Q') (hq : (0 : Q') ≤ q) :
    ExpPos.geRat (margin q hq) (q + -(q * q)) := by
  show ExpPos.geRat (CReal.sub CReal.cone (ExpNeg.expNeg q hq)) (q + -(q * q))
  exact ExpPos.geRat_mono (geRat_sub_cone (expNeg_le_quad q hq))
    (Q'.le_of_eqv (Q'.eqv_symm (boundSimp q)))

/-- **Upper bracket** `1 − e^{−q} ≤ q` (as `leRat`) — `CReal.oneSub_le_expNeg`. -/
theorem margin_leRat (q : Q') (hq : (0 : Q') ≤ q) (hq1 : q ≤ 1) :
    CReal.leRat (margin q hq) q :=
  oneSub_le_expNeg hq hq1

/-! ## 4. Scaling the brackets by the integer factor `(M+1)` -/

/-- `(M+1)·(1/(M+1)) = 1` lifts `leRat m c` to `leRat ((M+1)·m) ((M+1)·c)`. -/
theorem scaleN_succ_leRat (M : Nat) (m : CReal) (c : Q') (h : CReal.leRat m c) :
    CReal.leRat (CReal.scaleN (M + 1) m) (Q'.ofNat (M + 1) * c) := by
  intro ε hε
  have hεpos : (0 : Q') < ε * Q'.invSucc M := Q'.mul_pos hε (Q'.invSucc_pos M)
  obtain ⟨K, hK⟩ := h (ε * Q'.invSucc M) hεpos
  refine ⟨K, fun n hn => ?_⟩
  have happrox := CReal.scaleN_approx (M + 1) m n
  have hm := hK n hn
  have hofnn : (0 : Q') ≤ Q'.ofNat (M + 1) := ExpNeg.ofNat_nonneg' (M + 1)
  have step1 : Q'.ofNat (M + 1) * m.approx n
      ≤ Q'.ofNat (M + 1) * (c + ε * Q'.invSucc M) :=
    Q'.mul_le_mul_of_nonneg_left (m.approx n) (c + ε * Q'.invSucc M) (Q'.ofNat (M + 1)) hm hofnn
  have step2 : (Q'.ofNat (M + 1) * (c + ε * Q'.invSucc M)).eqv
      (Q'.ofNat (M + 1) * c + ε) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat (M + 1)) c (ε * Q'.invSucc M)) ?_
    refine Q'.add_eqv_congr_left (Q'.ofNat (M + 1) * c) _ ε ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (M + 1)) (ε * Q'.invSucc M) (Q'.invSucc M * ε)
        (Q'.mul_comm_eqv ε (Q'.invSucc M))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (M + 1)) (Q'.invSucc M) ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat (M + 1) * Q'.invSucc M) 1 ε (Q'.ofNat_succ_mul_invSucc M)) ?_
    exact Q'.one_mul_eqv ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv happrox) ?_
  exact Q'.le_trans' _ _ _ step1 (Q'.le_of_eqv step2)

/-- The `geRat` analogue: lifts `geRat m c` to `geRat ((M+1)·m) ((M+1)·c)`. -/
theorem scaleN_succ_geRat (M : Nat) (m : CReal) (c : Q') (h : ExpPos.geRat m c) :
    ExpPos.geRat (CReal.scaleN (M + 1) m) (Q'.ofNat (M + 1) * c) := by
  intro ε hε
  have hεpos : (0 : Q') < ε * Q'.invSucc M := Q'.mul_pos hε (Q'.invSucc_pos M)
  obtain ⟨K, hK⟩ := h (ε * Q'.invSucc M) hεpos
  refine ⟨K, fun n hn => ?_⟩
  have happrox := CReal.scaleN_approx (M + 1) m n
  have hm := hK n hn
  have hofnn : (0 : Q') ≤ Q'.ofNat (M + 1) := ExpNeg.ofNat_nonneg' (M + 1)
  have step1 : Q'.ofNat (M + 1) * c
      ≤ Q'.ofNat (M + 1) * (m.approx n + ε * Q'.invSucc M) :=
    Q'.mul_le_mul_of_nonneg_left c (m.approx n + ε * Q'.invSucc M) (Q'.ofNat (M + 1)) hm hofnn
  have step2 : (Q'.ofNat (M + 1) * (m.approx n + ε * Q'.invSucc M)).eqv
      (Q'.ofNat (M + 1) * m.approx n + ε) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat (M + 1)) (m.approx n) (ε * Q'.invSucc M)) ?_
    refine Q'.add_eqv_congr_left (Q'.ofNat (M + 1) * m.approx n) _ ε ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (M + 1)) (ε * Q'.invSucc M) (Q'.invSucc M * ε)
        (Q'.mul_comm_eqv ε (Q'.invSucc M))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (M + 1)) (Q'.invSucc M) ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat (M + 1) * Q'.invSucc M) 1 ε (Q'.ofNat_succ_mul_invSucc M)) ?_
    exact Q'.one_mul_eqv ε
  refine Q'.le_trans' _ _ _ step1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv step2) ?_
  exact Q'.add_le_add_right _ _ ε (Q'.le_of_eqv (Q'.eqv_symm happrox))

/-! ## 5. The scaling identities of the self-similar flow -/

/-- `1/(m+1) ≤ 1`. -/
theorem invSucc_le_one (m : Nat) : Q'.invSucc m ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le m)) (by decide)

/-- The exponent `t_k = w₀ · (1/(m+1))` is `≤ 1`. -/
theorem tk_le_one (w0 : Q') (hw0nn : (0 : Q') ≤ w0) (hw0le1 : w0 ≤ 1) (m : Nat) :
    w0 * Q'.invSucc m ≤ 1 := by
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (Q'.invSucc m) 1 w0 (invSucc_le_one m) hw0nn) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv w0)) hw0le1

/-- **The exact scaling identity** `(m+1) · (w₀·(1/(m+1))) ≃ w₀`. -/
theorem exact_scale (w0 : Q') (m : Nat) :
    (Q'.ofNat (m + 1) * (w0 * Q'.invSucc m)).eqv w0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (m + 1)) (w0 * Q'.invSucc m) (Q'.invSucc m * w0)
      (Q'.mul_comm_eqv w0 (Q'.invSucc m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (m + 1)) (Q'.invSucc m) w0)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat (m + 1) * Q'.invSucc m) 1 w0 (Q'.ofNat_succ_mul_invSucc m)) ?_
  exact Q'.one_mul_eqv w0

/-- **The lower-bracket value identity**
`(m+1) · (t_k − t_k²) ≃ w₀ − w₀·t_k` with `t_k = w₀·(1/(m+1))`. -/
theorem lower_scale (w0 : Q') (m : Nat) :
    (Q'.ofNat (m + 1) *
      ((w0 * Q'.invSucc m) + -((w0 * Q'.invSucc m) * (w0 * Q'.invSucc m)))).eqv
      (w0 + -(w0 * (w0 * Q'.invSucc m))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (Q'.ofNat (m + 1)) (w0 * Q'.invSucc m)
      (-((w0 * Q'.invSucc m) * (w0 * Q'.invSucc m)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (Q'.ofNat (m + 1) * (w0 * Q'.invSucc m)) w0
      (Q'.ofNat (m + 1) * (-((w0 * Q'.invSucc m) * (w0 * Q'.invSucc m)))) (exact_scale w0 m)) ?_
  refine Q'.add_eqv_congr_left w0
    (Q'.ofNat (m + 1) * (-((w0 * Q'.invSucc m) * (w0 * Q'.invSucc m))))
    (-(w0 * (w0 * Q'.invSucc m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_neg_eqv (Q'.ofNat (m + 1)) ((w0 * Q'.invSucc m) * (w0 * Q'.invSucc m))) ?_
  refine neg_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (m + 1)) (w0 * Q'.invSucc m) (w0 * Q'.invSucc m))) ?_
  exact Q'.mul_eqv_congr_right (Q'.ofNat (m + 1) * (w0 * Q'.invSucc m)) w0
    (w0 * Q'.invSucc m) (exact_scale w0 m)

/-- The quadratic defect is dominated by `1/(m+1)`: `w₀·(w₀·(1/(m+1))) ≤ 1/(m+1)`. -/
theorem defect_le (w0 : Q') (hw0nn : (0 : Q') ≤ w0) (hw0le1 : w0 ≤ 1) (m : Nat) :
    w0 * (w0 * Q'.invSucc m) ≤ Q'.invSucc m := by
  have hww : w0 * w0 ≤ 1 := by
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left w0 1 w0 hw0le1 hw0nn) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv w0)) hw0le1
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv w0 w0 (Q'.invSucc m)))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (w0 * w0) 1 (Q'.invSucc m) hww (Q'.invSucc_nonneg m)) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc m))

/-! ## 6. The rescaled lattice margin and the transmutation limit -/

/-- **The rescaled lattice margin** of the self-similar flow with seed `w₀` and
predecessor sequence `n` (so the block at scale `k` has size `n k + 1`):

    transmuted_k  =  (n k + 1) · (1 − e^{−w₀·(1/(n k + 1))}). -/
def transmuted (w0 : Q') (hw0 : (0 : Q') ≤ w0) (n : Nat → Nat) (k : Nat) : CReal :=
  CReal.scaleN (n k + 1)
    (margin (w0 * Q'.invSucc (n k))
      (Q'.mul_nonneg w0 (Q'.invSucc (n k)) hw0 (Q'.invSucc_nonneg (n k))))

/-- **THE CONSTRUCTIVE DIMENSIONAL-TRANSMUTATION LIMIT (self-similar model).**
For a positive `[0,1]` seed `w₀` and any predecessor sequence `n` that grows
without bound (`hgrow`), the rescaled lattice margin converges to `w₀`:

    ConvergesTo (fun k => (n k + 1) · (1 − e^{−w₀/(n k + 1)}))  w₀.

The physical gap scale `w₀ = −ln(sep_0)` emerges as the limit of the rescaled
lattice margin.  Squeeze: `w₀ − w₀·t_k ≤ transmuted_k ≤ w₀` with the defect
`w₀·t_k ≤ 1/(n k + 1) → 0`. -/
theorem transmutation_limit_generic
    (w0 : Q') (hw0pos : (0 : Q') < w0) (hw0le1 : w0 ≤ 1)
    (n : Nat → Nat)
    (hgrow : ∀ T : Nat, ∃ Ns : Nat, ∀ K : Nat, Ns ≤ K → T ≤ n K) :
    CReal.ConvergesTo (transmuted w0 (Q'.le_of_lt hw0pos) n) (CReal.ofQ' w0) := by
  have hw0nn : (0 : Q') ≤ w0 := Q'.le_of_lt hw0pos
  intro ε hε
  have hδpos : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Ns, hNs⟩ := hgrow (HalfPow.half * ε).den
  refine ⟨Ns, fun K hK => ?_⟩
  -- `1/(n K + 1) ≤ δ`.
  have hnK : (HalfPow.half * ε).den ≤ n K := hNs K hK
  have hinv : Q'.invSucc (n K) ≤ HalfPow.half * ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hnK)
      (HalfPow.invSucc_den_le (HalfPow.half * ε) hδpos)
  -- exponent data at scale `K`.
  have htk0 : (0 : Q') ≤ w0 * Q'.invSucc (n K) :=
    Q'.mul_nonneg w0 (Q'.invSucc (n K)) hw0nn (Q'.invSucc_nonneg (n K))
  have htk1 : w0 * Q'.invSucc (n K) ≤ 1 := tk_le_one w0 hw0nn hw0le1 (n K)
  have hdef : w0 * (w0 * Q'.invSucc (n K)) ≤ HalfPow.half * ε :=
    Q'.le_trans' _ _ _ (defect_le w0 hw0nn hw0le1 (n K)) hinv
  -- upper one-sided bound: `transmuted_K ≤ w₀`.
  have hUp : CReal.leRat (transmuted w0 hw0nn n K) w0 := by
    have hsc := scaleN_succ_leRat (n K)
      (margin (w0 * Q'.invSucc (n K)) htk0) (w0 * Q'.invSucc (n K))
      (margin_leRat (w0 * Q'.invSucc (n K)) htk0 htk1)
    exact CReal.leRat_mono hsc (Q'.le_of_eqv (exact_scale w0 (n K)))
  -- lower one-sided bound: `transmuted_K ≥ w₀ − w₀·t_K`.
  have hLow : ExpPos.geRat (transmuted w0 hw0nn n K)
      (w0 + -(w0 * (w0 * Q'.invSucc (n K)))) := by
    have hsc := scaleN_succ_geRat (n K)
      (margin (w0 * Q'.invSucc (n K)) htk0)
      ((w0 * Q'.invSucc (n K)) + -((w0 * Q'.invSucc (n K)) * (w0 * Q'.invSucc (n K))))
      (margin_geRat (w0 * Q'.invSucc (n K)) htk0)
    exact ExpPos.geRat_mono hsc (Q'.le_of_eqv (Q'.eqv_symm (lower_scale w0 (n K))))
  -- assemble the two-sided `ConvergesTo` bound.
  obtain ⟨A, hA⟩ := hUp ε hε
  obtain ⟨B, hB⟩ := hLow (HalfPow.half * ε) hδpos
  refine ⟨max A B, fun nn hnn => ?_⟩
  have hnA : A ≤ nn := Nat.le_trans (Nat.le_max_left _ _) hnn
  have hnB : B ≤ nn := Nat.le_trans (Nat.le_max_right _ _) hnn
  refine ⟨?_, ?_⟩
  · -- `transmuted_K.approx nn ≤ w₀ + ε`.
    show (transmuted w0 hw0nn n K).approx nn ≤ w0 + ε
    exact hA nn hnA
  · -- `w₀ ≤ transmuted_K.approx nn + ε`.
    show w0 ≤ (transmuted w0 hw0nn n K).approx nn + ε
    have hBb := hB nn hnB
    have hsplit : w0.eqv
        ((w0 + -(w0 * (w0 * Q'.invSucc (n K)))) + (w0 * (w0 * Q'.invSucc (n K)))) :=
      Q'.eqv_symm (cancel_addNeg w0 (w0 * (w0 * Q'.invSucc (n K))))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (w0 * (w0 * Q'.invSucc (n K))) hBb) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left ((transmuted w0 hw0nn n K).approx nn + HalfPow.half * ε)
        (w0 * (w0 * Q'.invSucc (n K))) (HalfPow.half * ε) hdef) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((transmuted w0 hw0nn n K).approx nn) (HalfPow.half * ε)
        (HalfPow.half * ε)) ?_
    exact Q'.add_eqv_congr_left ((transmuted w0 hw0nn n K).approx nn)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)

/-! ## 7. The concrete self-similar `(b+1)^k` flow with seed `sep_0 = e^{−1}` -/

/-- `K + 1 ≤ 2^K`. -/
theorem two_pow_ge : ∀ K : Nat, K + 1 ≤ 2 ^ K
  | 0 => by decide
  | (K + 1) => by
      have ih := two_pow_ge K
      have hp : 2 ^ (K + 1) = 2 ^ K * 2 := by rw [Nat.pow_succ]
      omega

/-- `K + 1 ≤ (b+1)^K` for `b ≥ 1`. -/
theorem nat_pow_succ_ge (b K : Nat) (hb : 1 ≤ b) : K + 1 ≤ (b + 1) ^ K := by
  have h2 : (2 : Nat) ≤ b + 1 := by omega
  exact Nat.le_trans (two_pow_ge K) (Nat.pow_le_pow_left h2 K)

/-- The self-similar block predecessor `(b+1)^K − 1` grows without bound (`b ≥ 1`). -/
theorem selfSimilar_grow (b : Nat) (hb : 1 ≤ b) :
    ∀ T : Nat, ∃ Ns : Nat, ∀ K : Nat, Ns ≤ K → T ≤ (b + 1) ^ K - 1 := by
  intro T
  refine ⟨T, fun K hK => ?_⟩
  have hpow := nat_pow_succ_ge b K hb
  omega

/-- **THE DIMENSIONAL-TRANSMUTATION LIMIT ON THE CONCRETE SELF-SIMILAR FLOW.**
For block factor `b ≥ 1`, with the geometric flow `w_k = 1/(b+1)^k` (so the
separator seed is `sep_0 = e^{−1}` and the gap scale is `w₀ = 1`), the rescaled
lattice margin `(b+1)^k · (1 − e^{−1/(b+1)^k})` converges to `w₀ = 1`:

    ConvergesTo (fun k => ((b+1)^k − 1 + 1) · (1 − e^{−1/(b+1)^k}))  1.

Here `(b+1)^k − 1 + 1 = (b+1)^k`, and `w₀ = 1 = −ln(e^{−1})` is the physical gap
scale.  This constructively closes the exp-limit crux ON THE SELF-SIMILAR MODEL. -/
theorem dimensional_transmutation_limit (b : Nat) (hb : 1 ≤ b) :
    CReal.ConvergesTo (transmuted 1 (by decide) (fun k => (b + 1) ^ k - 1)) (CReal.ofQ' 1) :=
  transmutation_limit_generic 1 (by decide) (Q'.le_refl' 1)
    (fun k => (b + 1) ^ k - 1) (selfSimilar_grow b hb)

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.reassoc_cancel
#print axioms YMGap.Continuum.neg_eqv
#print axioms YMGap.Continuum.poly_id
#print axioms YMGap.Continuum.oneOver1p_le_quad
#print axioms YMGap.Continuum.expNeg_le_quad
#print axioms YMGap.Continuum.geRat_sub_cone
#print axioms YMGap.Continuum.boundSimp
#print axioms YMGap.Continuum.margin_geRat
#print axioms YMGap.Continuum.scaleN_succ_leRat
#print axioms YMGap.Continuum.scaleN_succ_geRat
#print axioms YMGap.Continuum.exact_scale
#print axioms YMGap.Continuum.lower_scale
#print axioms YMGap.Continuum.defect_le
#print axioms YMGap.Continuum.transmutation_limit_generic
#print axioms YMGap.Continuum.selfSimilar_grow
#print axioms YMGap.Continuum.dimensional_transmutation_limit
