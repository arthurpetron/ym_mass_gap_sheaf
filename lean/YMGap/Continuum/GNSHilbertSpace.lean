/-
The genuine `CReal`-valued inner product on the GNS metric completion, and the
constructive GNS Hilbert space.

# Which gap this closes

`Continuum/GNSCompletion.lean` built the completion carrier
`GNSCompletionSpace = CauchyGNS / CauchyNull`, the isometric injective embedding
`embedQuot` of the pre-Hilbert quotient, and recorded the ONE open brick: the
`CReal`-valued inner product on ALL of `GNSCompletionSpace`, i.e. the limit
`lim cInner(xₙ,yₙ)`.  This module supplies it.

# What is genuine here (constructed / proved, axiom-clean)

  * **Limit of a `Q′`-Cauchy sequence (`CReal.ofQ'CauchySeq`).**  A rational
    sequence `r : Nat → Q′` with an explicit Cauchy modulus is reindexed through
    a running-max `QMhat` (which is monotone AND dominates the diagonal, so it is
    unbounded) into a genuine `CReal`.  `convergesTo_ofQ'CauchySeq` proves the
    `CReal` is the limit of the lifted sequence `n ↦ ofQ' (r n)`.

  * **The Cauchy–Schwarz term bound (`cs_term_bound`).**  From the sharp GNS
    Cauchy–Schwarz `⟨u,w⟩² ≤ ⟨u,u⟩·⟨w,w⟩` (`GNSData.cauchy_schwarz`), a budget
    `⟨u,u⟩·⟨w,w⟩ ≤ e²` yields `|⟨u,w⟩| ≤ e` — sqrt-free, via the square-reflection
    `Q'.le_of_sq_le_sq`.

  * **Uniform norm bound (`normCeil_bound`).**  Every GNS Cauchy sequence has its
    squared norms bounded past a base index, by `2·d²(zₙ,z_base) + 2·⟨z_base⟩`
    (`B_cross_le`, sqrt-free), rounded up to a `Nat` ceiling.

  * **The inner-product Cauchy estimate.**  `cInnerSeq x y n = ⟨xₙ,yₙ⟩` is shown
    `QCauchy` (and the difference of two null-equivalent pairs is null) by the
    bilinear split `⟨a,b⟩−⟨a′,b′⟩ = ⟨a−a′,b⟩ + ⟨a′,b−b′⟩` plus two
    `cs_term_bound`s.

  * **The completed inner product.**  `cinnerRep x y := ofQ'CauchySeq (cInnerSeq
    x y) …`, descended through `CauchyNull` on both arguments into the genuine
    real quotient `RC = CReal/Equiv` as `cinnerCompl : GNSCompletionSpace →
    GNSCompletionSpace → RC`, agreeing with `cInner` on the dense image.

  * **The capstone `GNSHilbertSpace`.**  Carrier `GNSCompletionSpace`, dense
    isometric embedding `embedQuot`, real-valued inner product `cinnerCompl`
    extending `cInner` — the metric completion of the GNS pre-Hilbert quotient.

# Honest residual

Full metric completeness of `GNSCompletionSpace` (every `cDistSq`-Cauchy sequence
in the completion converges) is NOT proved here; it is the named residual
`MetricCompleteResidual`.  What IS delivered is the completed `CReal`-valued
inner-product space with the original observables densely/isometrically embedded.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.GNSCompletion
import YMGap.Continuum.WilsonGNS
import YMGap.Constructive.Sqrt

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Constructive

/-! ## `Q′` glue: square-reflection of absolute value, `ofNat` facts -/

namespace Q'

/-- `|t|·|t| ≃ t·t`. -/
theorem abs_mul_self_eqv (t : Q') : (Q'.abs t * Q'.abs t).eqv (t * t) := by
  unfold Q'.abs
  by_cases h : (0 : Q') ≤ t
  · rw [if_pos h]; exact Q'.eqv_refl _
  · rw [if_neg h]
    -- (-t)*(-t) ≃ t*t
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv t (-t)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr (t * (-t)) (-(t * t)) (Q'.mul_neg_eqv t t)) ?_
    exact Q'.neg_neg_eqv (t * t)

/-- **Square reflection for absolute value.**  `0 < e` and `t² ≤ e²` give
`|t| ≤ e`.  Sqrt-free, via `le_of_sq_le_sq` applied to `|t|`. -/
theorem abs_le_of_sq_le_sq {t e : Q'} (he : (0 : Q') < e) (h : t * t ≤ e * e) :
    Q'.abs t ≤ e :=
  CReal.le_of_sq_le_sq he (Q'.abs_nonneg t)
    (le_of_eqv_le (Q'.abs_mul_self_eqv t) h)

/-- `a ≤ b` (on `Nat`) lifts to `ofNat a ≤ ofNat b`. -/
theorem ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (Q'.ofNat a).num * ((Q'.ofNat b).den : Int) ≤ (Q'.ofNat b).num * ((Q'.ofNat a).den : Int)
  rw [Q'.ofNat_num_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.ofNat_den_cast,
      Int.mul_one, Int.mul_one]
  exact_mod_cast h

/-- Any rational is `≤` the `Nat` ceiling `q.num.toNat + 1`. -/
theorem le_ofNat_ceil (q : Q') : q ≤ Q'.ofNat (q.num.toNat + 1) := by
  show q.num * ((Q'.ofNat (q.num.toNat + 1)).den : Int)
      ≤ (Q'.ofNat (q.num.toNat + 1)).num * (q.den : Int)
  rw [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one]
  -- goal: q.num ≤ ((q.num.toNat + 1 : Nat) : Int) * q.den
  have hden : (1 : Int) ≤ (q.den : Int) := by exact_mod_cast q.den_pos
  have hnum : q.num ≤ (((q.num.toNat + 1 : Nat)) : Int) := by omega
  have hpos : (0 : Int) ≤ (((q.num.toNat + 1 : Nat)) : Int) := by omega
  have hstep : (((q.num.toNat + 1 : Nat)) : Int)
      ≤ (((q.num.toNat + 1 : Nat)) : Int) * (q.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left hden hpos
    rwa [Int.mul_one] at this
  exact Int.le_trans hnum hstep

/-- `invSucc (Cn−1) · ofNat Cn ≃ 1` when `1 ≤ Cn`. -/
theorem invSucc_mul_ofNat_eqv_one {Cn : Nat} (h : 1 ≤ Cn) :
    (Q'.invSucc (Cn - 1) * Q'.ofNat Cn).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.invSucc (Cn - 1)) (Q'.ofNat Cn)) ?_
  -- ofNat Cn * invSucc (Cn-1) ≃ 1
  show (Q'.ofNat Cn * Q'.invSucc (Cn - 1)).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((Q'.ofNat Cn * Q'.invSucc (Cn - 1)).den : Int)
  rw [Q'.ofNat_mul_invSucc_num, Q'.ofNat_mul_invSucc_den]
  show (Cn : Int) * (1 : Int) = (1 : Int) * (((Cn - 1 : Nat) : Int) + 1)
  have : ((Cn - 1 : Nat) : Int) + 1 = (Cn : Int) := by omega
  rw [this, Int.mul_one, Int.one_mul]

/-- `0 ≤ ofNat n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n :=
  (Q'.zero_le_iff_num_nonneg (Q'.ofNat n)).mpr (by rw [Q'.ofNat_num_cast]; exact Int.natCast_nonneg n)

/-- **The Cauchy-estimate budget.**  `((e²)·invSucc(Cn−1))·ofNat Cn ≤ e²` for
`1 ≤ Cn`. -/
theorem budget_le (e : Q') (Cn : Nat) (hCn : 1 ≤ Cn) (hee : (0 : Q') ≤ e * e) :
    ((e * e) * Q'.invSucc (Cn - 1)) * Q'.ofNat Cn ≤ e * e := by
  have ha : (((e * e) * Q'.invSucc (Cn - 1)) * Q'.ofNat Cn).eqv
      ((e * e) * (Q'.invSucc (Cn - 1) * Q'.ofNat Cn)) :=
    Q'.mul_assoc_eqv _ _ _
  have hle1 : (e * e) * (Q'.invSucc (Cn - 1) * Q'.ofNat Cn) ≤ (e * e) * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ (e * e)
      (Q'.le_of_eqv (Q'.invSucc_mul_ofNat_eqv_one hCn)) hee
  exact le_of_le_eqv (le_of_eqv_le ha hle1) (Q'.mul_one_eqv (e * e))

end Q'

/-! ## The `CReal` limit of a `Q′`-Cauchy sequence -/

namespace CReal

/-- A **rational Cauchy datum**: a `Type`-level two-sided modulus for `r`. -/
structure QCauchy (r : Nat → Q') where
  /-- The Cauchy modulus. -/
  M : Q' → Nat
  /-- Two-sided Cauchy bound past `M ε`. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ p q : Nat, M ε ≤ p → M ε ≤ q →
    r p ≤ r q + ε ∧ r q ≤ r p + ε

/-- The running-max reindex, baking in the diagonal `k` so it is unbounded
(`QMhat r c k ≥ k`) as well as monotone and dominating `M (invSucc k)`. -/
def QMhat (r : Nat → Q') (c : QCauchy r) : Nat → Nat
  | 0 => max (c.M (Q'.invSucc 0)) 0
  | k + 1 => max (QMhat r c k) (max (c.M (Q'.invSucc (k + 1))) (k + 1))

theorem QMhat_mono_succ (r : Nat → Q') (c : QCauchy r) (k : Nat) :
    QMhat r c k ≤ QMhat r c (k + 1) := Nat.le_max_left _ _

theorem QMhat_mono (r : Nat → Q') (c : QCauchy r) {a b : Nat} (h : a ≤ b) :
    QMhat r c a ≤ QMhat r c b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (QMhat_mono_succ r c b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

theorem QM_le_QMhat (r : Nat → Q') (c : QCauchy r) (k : Nat) :
    c.M (Q'.invSucc k) ≤ QMhat r c k := by
  cases k with
  | zero => exact Nat.le_max_left _ _
  | succ k => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem self_le_QMhat (r : Nat → Q') (c : QCauchy r) (k : Nat) : k ≤ QMhat r c k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The directed core bound: for `a ≤ b` with `ε.den ≤ a`,
`|r (QMhat a) − r (QMhat b)| ≤ ε`. -/
theorem QMhat_directed (r : Nat → Q') (c : QCauchy r) (ε : Q') (hε : (0 : Q') < ε)
    (a b : Nat) (hab : a ≤ b) (hda : ε.den ≤ a) :
    r (QMhat r c a) ≤ r (QMhat r c b) + ε ∧ r (QMhat r c b) ≤ r (QMhat r c a) + ε := by
  have hinva : Q'.invSucc a ≤ ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hda) (HalfPow.invSucc_den_le ε hε)
  have hinvapos : (0 : Q') < Q'.invSucc a := Q'.invSucc_pos a
  have hMa : c.M (Q'.invSucc a) ≤ QMhat r c a := QM_le_QMhat r c a
  have hMb : c.M (Q'.invSucc a) ≤ QMhat r c b :=
    Nat.le_trans hMa (QMhat_mono r c hab)
  obtain ⟨h1, h2⟩ := c.bound (Q'.invSucc a) hinvapos (QMhat r c a) (QMhat r c b) hMa hMb
  exact ⟨Q'.le_trans' _ _ _ h1 (Q'.add_le_add_left _ _ ε hinva),
         Q'.le_trans' _ _ _ h2 (Q'.add_le_add_left _ _ ε hinva)⟩

/-- **The `CReal` limit of a `Q′`-Cauchy sequence.** -/
def ofQ'CauchySeq (r : Nat → Q') (c : QCauchy r) : CReal where
  approx k := r (QMhat r c k)
  cauchy := by
    intro ε hε
    refine ⟨ε.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact QMhat_directed r c ε hε m n hmn hm
    · exact (QMhat_directed r c ε hε n m hnm hn).symm

@[simp] theorem ofQ'CauchySeq_approx (r : Nat → Q') (c : QCauchy r) (k : Nat) :
    (ofQ'CauchySeq r c).approx k = r (QMhat r c k) := rfl

/-- **The limit is the limit of the lifted sequence `n ↦ ofQ' (r n)`.** -/
theorem convergesTo_ofQ'CauchySeq (r : Nat → Q') (c : QCauchy r) :
    ConvergesTo (fun N => ofQ' (r N)) (ofQ'CauchySeq r c) := by
  intro ε hε
  refine ⟨c.M ε, fun N hN => ⟨c.M ε, fun n hn => ?_⟩⟩
  -- (ofQ' (r N)).approx n = r N ; L.approx n = r (QMhat n) ; both indices ≥ c.M ε.
  have hQn : c.M ε ≤ QMhat r c n := Nat.le_trans hn (self_le_QMhat r c n)
  obtain ⟨h1, h2⟩ := c.bound ε hε N (QMhat r c n) hN hQn
  exact ⟨h1, h2⟩

/-! ### `Equiv` reflexivity, the real quotient, and the close-limit uniqueness -/

/-- `Equiv` is reflexive. -/
theorem Equiv.refl (A : CReal) : CReal.Equiv A A :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)⟩⟩

/-- Two `CReal`s with equal approximation sequences are `Equiv`. -/
theorem Equiv_of_approx_eq {A B : CReal} (h : ∀ k, A.approx k = B.approx k) :
    CReal.Equiv A B := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [h n]
  exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε),
         Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)⟩

/-- The setoid of `CReal`s under `Equiv` — the genuine constructive reals. -/
def crealSetoid : Setoid CReal where
  r := CReal.Equiv
  iseqv := ⟨CReal.Equiv.refl, fun h => CReal.Equiv.symm h, fun h1 h2 => CReal.Equiv.trans h1 h2⟩

/-- `RC = CReal / Equiv`, the genuine constructive real line. -/
def RC : Type := Quotient crealSetoid

/-- **Close-limit uniqueness for lifted rational sequences.**  If the lifted
sequences `n ↦ ofQ' (r n)` and `n ↦ ofQ' (r′ n)` converge to `A`, `B`, and `r`,
`r′` are termwise within every tolerance, then `A ≃ B`. -/
theorem Equiv_of_ofQ'_limit_close {r r' : Nat → Q'} {A B : CReal}
    (hA : ConvergesTo (fun N => ofQ' (r N)) A)
    (hB : ConvergesTo (fun N => ofQ' (r' N)) B)
    (hclose : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      r n ≤ r' n + ε ∧ r' n ≤ r n + ε) :
    CReal.Equiv A B := by
  intro ε hε
  let q : Q' := HalfPow.half * (HalfPow.half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨NstA, hstA⟩ := hA q hqpos
  obtain ⟨NstB, hstB⟩ := hB q hqpos
  obtain ⟨Ncl, hcl⟩ := hclose q hqpos
  let N : Nat := max (max NstA NstB) Ncl
  have hNA : NstA ≤ N := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hNB : NstB ≤ N := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hNcl : Ncl ≤ N := Nat.le_max_right _ _
  obtain ⟨NapxA, hclA⟩ := hstA N hNA
  obtain ⟨NapxB, hclB⟩ := hstB N hNB
  obtain ⟨hE1, hE2⟩ := hcl N hNcl   -- r N ≤ r' N + q , r' N ≤ r N + q
  refine ⟨max NapxA NapxB, fun n hn => ?_⟩
  have hnA : NapxA ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnB : NapxB ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hA1, hA2⟩ := hclA n hnA   -- r N ≤ A_n + q , A_n ≤ r N + q
  obtain ⟨hB1, hB2⟩ := hclB n hnB   -- r' N ≤ B_n + q , B_n ≤ r' N + q
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
  refine ⟨?_, ?_⟩
  · -- A_n ≤ B_n + ε : A_n ≤ r N + q, r N ≤ r' N + q, r' N ≤ B_n + q
    exact chain3 (A.approx n) (r N) (r' N) (B.approx n) hA2 hE1 hB1
  · -- B_n ≤ A_n + ε : B_n ≤ r' N + q, r' N ≤ r N + q, r N ≤ A_n + q
    exact chain3 (B.approx n) (r' N) (r N) (A.approx n) hB2 hE2 hA1

end CReal

/-! ## `Q′` rearrangement and subtraction glue for the estimate -/

namespace Q'

/-- `(a + (−b)) + b ≃ a`. -/
theorem sub_add_cancel_eqv (a b : Q') : ((a + (-b)) + b).eqv a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

/-- From `a + (−b) ≤ c` deduce `a ≤ b + c`. -/
theorem le_add_of_sub_le {a b c : Q'} (h : a + (-b) ≤ c) : a ≤ b + c := by
  have h1 : (a + (-b)) + b ≤ c + b := Q'.add_le_add_right _ _ b h
  have ha : a ≤ c + b := le_of_eqv_le (Q'.eqv_symm (Q'.sub_add_cancel_eqv a b)) h1
  exact le_of_le_eqv ha (Q'.add_comm_eqv c b)

/-- `−(a + (−b)) ≃ b + (−a)`. -/
theorem neg_sub_eqv (a b : Q') : (-(a + (-b))).eqv (b + (-a)) := by
  -- −(a + (−b)) ≃ (−a) + (−(−b)) ≃ (−a) + b ≃ b + (−a)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (GNSAux.neg_add_eqv a (-b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) (-(-b)) b (Q'.neg_neg_eqv b)) ?_
  exact Q'.add_comm_eqv (-a) b

/-- From `|a + (−b)| ≤ e` deduce the two-sided `a ≤ b + e ∧ b ≤ a + e`. -/
theorem two_sided_of_abs_sub_le {a b e : Q'} (h : Q'.abs (a + (-b)) ≤ e) :
    a ≤ b + e ∧ b ≤ a + e := by
  refine ⟨Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self (a + (-b))) h), ?_⟩
  have h2 : b + (-a) ≤ e :=
    le_of_eqv_le (Q'.eqv_symm (Q'.neg_sub_eqv a b))
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs (a + (-b))) h)
  exact Q'.le_add_of_sub_le h2

/-- `(A + X) + (Y + B) ≃ (A + B) + (X + Y)`. -/
theorem rearr_ABXY (A X Y B : Q') : ((A + X) + (Y + B)).eqv ((A + B) + (X + Y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A X (Y + B)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A (X + (Y + B)) (X + (B + Y))
      (Q'.add_eqv_congr_left X (Y + B) (B + Y) (Q'.add_comm_eqv Y B))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A (X + (B + Y)) ((X + B) + Y)
      (Q'.eqv_symm (Q'.add_assoc_eqv X B Y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A ((X + B) + Y) ((B + X) + Y)
      (Q'.add_eqv_congr_right (X + B) (B + X) Y (Q'.add_comm_eqv X B))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A ((B + X) + Y) (B + (X + Y)) (Q'.add_assoc_eqv B X Y)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv A B (X + Y))

end Q'

end YMGap.Constructive

namespace YMGap.Continuum.GNSQuotient

open YMGap.Constructive

namespace GNSData

variable (D : GNSData)

/-! ## Cauchy–Schwarz term bound and the bilinear difference split -/

/-- **The Cauchy–Schwarz term bound.**  From `⟨u,w⟩² ≤ ⟨u,u⟩·⟨w,w⟩`, squared-norm
upper bounds `⟨u,u⟩ ≤ bu`, `⟨w,w⟩ ≤ bw`, and a budget `bu·bw ≤ e²`, conclude
`|⟨u,w⟩| ≤ e`.  Sqrt-free. -/
theorem cs_term_bound (u w : D.V) (bu bw e : Q')
    (he : (0 : Q') < e) (hbu : (0 : Q') ≤ bu)
    (huu : D.B u u ≤ bu) (hww : D.B w w ≤ bw)
    (hbudget : bu * bw ≤ e * e) :
    Q'.abs (D.B u w) ≤ e := by
  have hcs : D.B u w * D.B u w ≤ D.B u u * D.B w w := D.cauchy_schwarz u w
  have hprod : D.B u u * D.B w w ≤ bu * bw :=
    Q'.mul_le_mul_of_nonneg huu hww hbu (D.self_nonneg w)
  exact Q'.abs_le_of_sq_le_sq he
    (Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hcs hprod) hbudget)

/-- **The bilinear difference split** `⟨a,b⟩ − ⟨a′,b′⟩ ≃ ⟨a−a′,b⟩ + ⟨a′,b−b′⟩`. -/
theorem B_diff_split (a a' b b' : D.V) :
    (D.B a b + (-(D.B a' b'))).eqv
      (D.B (D.sub a a') b + D.B a' (D.sub b b')) := by
  -- term1 ≃ ⟨a,b⟩ + (−⟨a′,b⟩)
  have e1 : (D.B (D.sub a a') b).eqv (D.B a b + (-(D.B a' b))) :=
    Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg a') b)
      (Q'.add_eqv_congr_left (D.B a b) (D.B (D.neg a') b) (-(D.B a' b)) (D.B_neg_left a' b))
  -- term2 ≃ ⟨a′,b⟩ + (−⟨a′,b′⟩)
  have e2 : (D.B a' (D.sub b b')).eqv (D.B a' b + (-(D.B a' b'))) :=
    Q'.eqv_trans _ _ _ (D.B_add_right a' b (D.neg b'))
      (Q'.add_eqv_congr_left (D.B a' b) (D.B a' (D.neg b')) (-(D.B a' b')) (D.B_neg_right a' b'))
  -- telescope: (P + (−Q)) + (Q + (−R)) ≃ P + (−R)
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (QPoly.q_add_congr e1 e2) ?_)
  -- (⟨a,b⟩ + (−⟨a′,b⟩)) + (⟨a′,b⟩ + (−⟨a′,b′⟩)) ≃ ⟨a,b⟩ + (−⟨a′,b′⟩)
  refine Q'.eqv_trans _ _ _
    (Q'.rearr_ABXY (D.B a b) (-(D.B a' b)) (D.B a' b) (-(D.B a' b'))) ?_
  -- (⟨a,b⟩ + (−⟨a′,b′⟩)) + ((−⟨a′,b⟩) + ⟨a′,b⟩) ≃ ⟨a,b⟩ + (−⟨a′,b′⟩)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ ((-(D.B a' b)) + (D.B a' b)) 0 (Q'.neg_add_self_eqv (D.B a' b))) ?_
  exact QPoly.q_add_zero_eqv _

/-- **The absolute-value difference bound.** -/
theorem abs_B_diff_le (a a' b b' : D.V) :
    Q'.abs (D.B a b + (-(D.B a' b')))
      ≤ Q'.abs (D.B (D.sub a a') b) + Q'.abs (D.B a' (D.sub b b')) := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (D.B_diff_split a a' b b'))) ?_
  exact Q'.abs_add_le' (D.B (D.sub a a') b) (D.B a' (D.sub b b'))

/-! ## Uniform norm bound on a GNS Cauchy sequence -/

/-- The base index `z.modulus 1` past which `d²(zₙ,z_base) ≤ 1`. -/
def normBase (z : CauchyGNS D) : Nat := z.modulus (Q'.ofNat 1)

/-- The rational norm bound `2 + 2·⟨z_base,z_base⟩`. -/
def normBoundQ (z : CauchyGNS D) : Q' :=
  (Q'.ofNat 1 + Q'.ofNat 1)
    + (D.B (z.seq (D.normBase z)) (z.seq (D.normBase z))
        + D.B (z.seq (D.normBase z)) (z.seq (D.normBase z)))

/-- The `Nat` ceiling of the norm bound (always `≥ 1`). -/
def normCeil (z : CauchyGNS D) : Nat := (D.normBoundQ z).num.toNat + 1

theorem one_le_normCeil (z : CauchyGNS D) : 1 ≤ D.normCeil z := Nat.le_add_left _ _

/-- `d²(a, 0) ≃ ⟨a,a⟩`. -/
theorem distSqQ_zero_eqv (a : D.V) : (D.distSqQ a D.zero).eqv (D.B a a) := by
  have hv : D.veq (D.sub a D.zero) a :=
    D.veq_trans (D.add_congr (D.veq_refl a) D.neg_zero) (D.add_zero a)
  exact D.B_diag_congr hv

/-- **Uniform squared-norm bound.**  For `n ≥ z.modulus 1`,
`⟨zₙ,zₙ⟩ ≤ ofNat (normCeil z)`. -/
theorem normCeil_bound (z : CauchyGNS D) (n : Nat) (hn : D.normBase z ≤ n) :
    D.B (z.seq n) (z.seq n) ≤ Q'.ofNat (D.normCeil z) := by
  -- d²(z_n, z_base) ≤ 1
  have hd1 : D.distSqQ (z.seq n) (z.seq (D.normBase z)) ≤ Q'.ofNat 1 :=
    z.isCauchy (Q'.ofNat 1) (by decide) n (D.normBase z) hn (Nat.le_refl _)
  -- d²(z_base, 0) ≃ ⟨z_base,z_base⟩
  have hd2 : (D.distSqQ (z.seq (D.normBase z)) D.zero).eqv
      (D.B (z.seq (D.normBase z)) (z.seq (D.normBase z))) :=
    D.distSqQ_zero_eqv (z.seq (D.normBase z))
  -- triangle: d²(z_n,0) ≤ (d²(z_n,base)+d²) + (d²(base,0)+d²)
  have htri := D.distSqQ_triangle (z.seq n) (z.seq (D.normBase z)) D.zero
  have hbound : D.distSqQ (z.seq n) D.zero ≤ D.normBoundQ z := by
    refine Q'.le_trans' _ _ _ htri ?_
    refine Q'.add_le_add (Q'.add_le_add hd1 hd1) ?_
    exact Q'.add_le_add (Q'.le_of_eqv hd2) (Q'.le_of_eqv hd2)
  -- ⟨z_n,z_n⟩ ≃ d²(z_n,0)
  have hnorm : D.B (z.seq n) (z.seq n) ≤ D.normBoundQ z :=
    le_of_eqv_le (Q'.eqv_symm (D.distSqQ_zero_eqv (z.seq n))) hbound
  exact Q'.le_trans' _ _ _ hnorm (Q'.le_ofNat_ceil (D.normBoundQ z))

/-! ## The inner-product Cauchy estimate (task 1) -/

/-- The representative-level inner-product sequence `n ↦ ⟨xₙ,yₙ⟩`. -/
def cInnerSeq (x y : CauchyGNS D) (n : Nat) : Q' := D.B (x.seq n) (y.seq n)

/-- The uniform `Nat` norm-ceiling shared by `x` and `y`. -/
def innerCn (x y : CauchyGNS D) : Nat := max (D.normCeil x) (D.normCeil y)

/-- The distance tolerance driving the inner-product Cauchy estimate. -/
def innerδ (x y : CauchyGNS D) (ε : Q') : Q' :=
  ((HalfPow.half * ε) * (HalfPow.half * ε)) * Q'.invSucc (D.innerCn x y - 1)

/-- The inner-product Cauchy modulus. -/
def innerM (x y : CauchyGNS D) (ε : Q') : Nat :=
  max (max (D.normBase x) (D.normBase y))
      (max (x.modulus (D.innerδ x y ε)) (y.modulus (D.innerδ x y ε)))

/-- **The core estimate.**  `|⟨xₚ,yₚ⟩ − ⟨x_q,y_q⟩| ≤ ε` for `p,q ≥ innerM ε`. -/
theorem cInner_abs_bound (x y : CauchyGNS D) (ε : Q') (hε : (0 : Q') < ε)
    (p q : Nat) (hp : D.innerM x y ε ≤ p) (hq : D.innerM x y ε ≤ q) :
    Q'.abs (D.B (x.seq p) (y.seq p) + (-(D.B (x.seq q) (y.seq q)))) ≤ ε := by
  have he : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  have hee : (0 : Q') ≤ (HalfPow.half * ε) * (HalfPow.half * ε) := Q'.le_of_lt (Q'.mul_pos he he)
  have hCn1 : 1 ≤ D.innerCn x y :=
    Nat.le_trans (D.one_le_normCeil x) (Nat.le_max_left _ _)
  have hδpos : (0 : Q') < D.innerδ x y ε :=
    Q'.mul_pos (Q'.mul_pos he he) (Q'.invSucc_pos _)
  -- index extractions
  have hAp : max (D.normBase x) (D.normBase y) ≤ p := Nat.le_trans (Nat.le_max_left _ _) hp
  have hAq : max (D.normBase x) (D.normBase y) ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hBp : max (x.modulus (D.innerδ x y ε)) (y.modulus (D.innerδ x y ε)) ≤ p :=
    Nat.le_trans (Nat.le_max_right _ _) hp
  have hBq : max (x.modulus (D.innerδ x y ε)) (y.modulus (D.innerδ x y ε)) ≤ q :=
    Nat.le_trans (Nat.le_max_right _ _) hq
  have hnbx_q : D.normBase x ≤ q := Nat.le_trans (Nat.le_max_left _ _) hAq
  have hnby_p : D.normBase y ≤ p := Nat.le_trans (Nat.le_max_right _ _) hAp
  have hxmod_p : x.modulus (D.innerδ x y ε) ≤ p := Nat.le_trans (Nat.le_max_left _ _) hBp
  have hxmod_q : x.modulus (D.innerδ x y ε) ≤ q := Nat.le_trans (Nat.le_max_left _ _) hBq
  have hymod_p : y.modulus (D.innerδ x y ε) ≤ p := Nat.le_trans (Nat.le_max_right _ _) hBp
  have hymod_q : y.modulus (D.innerδ x y ε) ≤ q := Nat.le_trans (Nat.le_max_right _ _) hBq
  -- distances
  have hdx : D.distSqQ (x.seq p) (x.seq q) ≤ D.innerδ x y ε :=
    x.isCauchy (D.innerδ x y ε) hδpos p q hxmod_p hxmod_q
  have hdy : D.distSqQ (y.seq p) (y.seq q) ≤ D.innerδ x y ε :=
    y.isCauchy (D.innerδ x y ε) hδpos p q hymod_p hymod_q
  -- norm bounds
  have hby_p : D.B (y.seq p) (y.seq p) ≤ Q'.ofNat (D.innerCn x y) :=
    Q'.le_trans' _ _ _ (D.normCeil_bound y p hnby_p) (Q'.ofNat_le_ofNat (Nat.le_max_right _ _))
  have hbx_q : D.B (x.seq q) (x.seq q) ≤ Q'.ofNat (D.innerCn x y) :=
    Q'.le_trans' _ _ _ (D.normCeil_bound x q hnbx_q) (Q'.ofNat_le_ofNat (Nat.le_max_left _ _))
  -- budgets
  have hbudget : D.innerδ x y ε * Q'.ofNat (D.innerCn x y)
      ≤ (HalfPow.half * ε) * (HalfPow.half * ε) :=
    Q'.budget_le (HalfPow.half * ε) (D.innerCn x y) hCn1 hee
  have hbudget' : Q'.ofNat (D.innerCn x y) * D.innerδ x y ε
      ≤ (HalfPow.half * ε) * (HalfPow.half * ε) :=
    le_of_eqv_le (Q'.mul_comm_eqv (Q'.ofNat (D.innerCn x y)) (D.innerδ x y ε)) hbudget
  -- the two CS terms
  have ht1 : Q'.abs (D.B (D.sub (x.seq p) (x.seq q)) (y.seq p)) ≤ HalfPow.half * ε :=
    D.cs_term_bound (D.sub (x.seq p) (x.seq q)) (y.seq p)
      (D.innerδ x y ε) (Q'.ofNat (D.innerCn x y)) (HalfPow.half * ε)
      he (Q'.le_of_lt hδpos) hdx hby_p hbudget
  have ht2 : Q'.abs (D.B (x.seq q) (D.sub (y.seq p) (y.seq q))) ≤ HalfPow.half * ε :=
    D.cs_term_bound (x.seq q) (D.sub (y.seq p) (y.seq q))
      (Q'.ofNat (D.innerCn x y)) (D.innerδ x y ε) (HalfPow.half * ε)
      he (Q'.ofNat_nonneg (D.innerCn x y)) hbx_q hdy hbudget'
  -- assemble
  have habs : Q'.abs (D.B (x.seq p) (y.seq p) + (-(D.B (x.seq q) (y.seq q))))
      ≤ (HalfPow.half * ε) + (HalfPow.half * ε) :=
    Q'.le_trans' _ _ _ (D.abs_B_diff_le (x.seq p) (x.seq q) (y.seq p) (y.seq q))
      (Q'.add_le_add ht1 ht2)
  exact le_of_le_eqv habs (ExpNeg.two_halves ε)

/-- **Task 1.**  `n ↦ ⟨xₙ,yₙ⟩` is a `Q′`-Cauchy sequence. -/
def cInnerQCauchy (x y : CauchyGNS D) : CReal.QCauchy (D.cInnerSeq x y) where
  M := D.innerM x y
  bound := fun ε hε p q hp hq =>
    Q'.two_sided_of_abs_sub_le (D.cInner_abs_bound x y ε hε p q hp hq)

/-! ## The well-definedness estimate (task 2) -/

/-- The uniform `Nat` norm-ceiling for the closeness estimate. -/
def closeCn (y x' : CauchyGNS D) : Nat := max (D.normCeil y) (D.normCeil x')

/-- The distance tolerance for the closeness estimate. -/
def closeδ (y x' : CauchyGNS D) (ε : Q') : Q' :=
  ((HalfPow.half * ε) * (HalfPow.half * ε)) * Q'.invSucc (D.closeCn y x' - 1)

/-- **The closeness estimate.**  If `x ≈ x′` and `y ≈ y′` are `CauchyNull`, then
`|⟨xₙ,yₙ⟩ − ⟨x′ₙ,y′ₙ⟩| → 0`. -/
theorem cInner_close (x x' y y' : CauchyGNS D)
    (hx : CauchyNull D x x') (hy : CauchyNull D y y')
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Q'.abs (D.B (x.seq n) (y.seq n) + (-(D.B (x'.seq n) (y'.seq n)))) ≤ ε := by
  have he : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  have hee : (0 : Q') ≤ (HalfPow.half * ε) * (HalfPow.half * ε) := Q'.le_of_lt (Q'.mul_pos he he)
  have hCn1 : 1 ≤ D.closeCn y x' :=
    Nat.le_trans (D.one_le_normCeil y) (Nat.le_max_left _ _)
  have hδpos : (0 : Q') < D.closeδ y x' ε :=
    Q'.mul_pos (Q'.mul_pos he he) (Q'.invSucc_pos _)
  obtain ⟨N1, hN1⟩ := hx (D.closeδ y x' ε) hδpos
  obtain ⟨N2, hN2⟩ := hy (D.closeδ y x' ε) hδpos
  refine ⟨max (max (D.normBase y) (D.normBase x')) (max N1 N2), fun n hn => ?_⟩
  have hAn : max (D.normBase y) (D.normBase x') ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hBn : max N1 N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hnby : D.normBase y ≤ n := Nat.le_trans (Nat.le_max_left _ _) hAn
  have hnbx' : D.normBase x' ≤ n := Nat.le_trans (Nat.le_max_right _ _) hAn
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hBn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hBn
  -- distances → 0
  have hd_x : D.distSqQ (x.seq n) (x'.seq n) ≤ D.closeδ y x' ε := hN1 n hn1
  have hd_y : D.distSqQ (y.seq n) (y'.seq n) ≤ D.closeδ y x' ε := hN2 n hn2
  -- norm bounds
  have hby_n : D.B (y.seq n) (y.seq n) ≤ Q'.ofNat (D.closeCn y x') :=
    Q'.le_trans' _ _ _ (D.normCeil_bound y n hnby) (Q'.ofNat_le_ofNat (Nat.le_max_left _ _))
  have hbx'_n : D.B (x'.seq n) (x'.seq n) ≤ Q'.ofNat (D.closeCn y x') :=
    Q'.le_trans' _ _ _ (D.normCeil_bound x' n hnbx') (Q'.ofNat_le_ofNat (Nat.le_max_right _ _))
  -- budgets
  have hbudget : D.closeδ y x' ε * Q'.ofNat (D.closeCn y x')
      ≤ (HalfPow.half * ε) * (HalfPow.half * ε) :=
    Q'.budget_le (HalfPow.half * ε) (D.closeCn y x') hCn1 hee
  have hbudget' : Q'.ofNat (D.closeCn y x') * D.closeδ y x' ε
      ≤ (HalfPow.half * ε) * (HalfPow.half * ε) :=
    le_of_eqv_le (Q'.mul_comm_eqv (Q'.ofNat (D.closeCn y x')) (D.closeδ y x' ε)) hbudget
  -- the two CS terms
  have ht1 : Q'.abs (D.B (D.sub (x.seq n) (x'.seq n)) (y.seq n)) ≤ HalfPow.half * ε :=
    D.cs_term_bound (D.sub (x.seq n) (x'.seq n)) (y.seq n)
      (D.closeδ y x' ε) (Q'.ofNat (D.closeCn y x')) (HalfPow.half * ε)
      he (Q'.le_of_lt hδpos) hd_x hby_n hbudget
  have ht2 : Q'.abs (D.B (x'.seq n) (D.sub (y.seq n) (y'.seq n))) ≤ HalfPow.half * ε :=
    D.cs_term_bound (x'.seq n) (D.sub (y.seq n) (y'.seq n))
      (Q'.ofNat (D.closeCn y x')) (D.closeδ y x' ε) (HalfPow.half * ε)
      he (Q'.ofNat_nonneg (D.closeCn y x')) hbx'_n hd_y hbudget'
  have habs : Q'.abs (D.B (x.seq n) (y.seq n) + (-(D.B (x'.seq n) (y'.seq n))))
      ≤ (HalfPow.half * ε) + (HalfPow.half * ε) :=
    Q'.le_trans' _ _ _ (D.abs_B_diff_le (x.seq n) (x'.seq n) (y.seq n) (y'.seq n))
      (Q'.add_le_add ht1 ht2)
  exact le_of_le_eqv habs (ExpNeg.two_halves ε)

/-! ## The completed `CReal`-valued inner product and the capstone -/

/-- The representative-level completed inner product, a `CReal`. -/
def cinnerRep (x y : CauchyGNS D) : CReal :=
  CReal.ofQ'CauchySeq (D.cInnerSeq x y) (D.cInnerQCauchy x y)

/-- **Task 2.**  `cinnerRep` respects `CauchyNull` on both arguments. -/
theorem cinnerRep_welldef (x x' y y' : CauchyGNS D)
    (hx : CauchyNull D x x') (hy : CauchyNull D y y') :
    CReal.Equiv (D.cinnerRep x y) (D.cinnerRep x' y') :=
  CReal.Equiv_of_ofQ'_limit_close
    (CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq x y) (D.cInnerQCauchy x y))
    (CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq x' y') (D.cInnerQCauchy x' y'))
    (fun ε hε => by
      obtain ⟨N, hN⟩ := D.cInner_close x x' y y' hx hy ε hε
      exact ⟨N, fun n hn => Q'.two_sided_of_abs_sub_le (hN n hn)⟩)

/-- The real-quotient-valued representative inner product. -/
def cinnerRepR (x y : CauchyGNS D) : CReal.RC :=
  Quotient.mk CReal.crealSetoid (D.cinnerRep x y)

/-- **The completed `CReal`-valued inner product** on the metric completion,
valued in the genuine real line `RC = CReal/Equiv`. -/
def cinnerCompl : GNSCompletionSpace D → GNSCompletionSpace D → CReal.RC :=
  Quotient.lift₂ (fun x y => D.cinnerRepR x y)
    (fun _ _ _ _ ha hb => Quotient.sound (D.cinnerRep_welldef _ _ _ _ ha hb))

/-- **Task 3.**  On the dense image the completed inner product agrees with the
pre-Hilbert form: `cinnerCompl (ι[a]) (ι[b]) = [⟨a,b⟩]`. -/
theorem cinnerCompl_embed (a b : D.V) :
    D.cinnerCompl (embedQuot D (D.qmk a)) (embedQuot D (D.qmk b))
      = Quotient.mk CReal.crealSetoid (D.cInner a b) := by
  -- both sides are the class of a constant `CReal` at `⟨a,b⟩`.
  refine Quotient.sound ?_
  refine CReal.Equiv_of_approx_eq (fun k => ?_)
  -- (cinnerRep (const a) (const b)).approx k = ⟨a,b⟩ = (cInner a b).approx k
  rfl

/-- **The constructive GNS Hilbert space datum**: a carrier with an injective
dense embedding of the pre-Hilbert quotient and a real-valued inner product
extending the GNS form on the image. -/
structure GNSHilbertSpace where
  /-- The completed carrier. -/
  carrier : Type
  /-- The dense isometric embedding of the quotient. -/
  ι : D.QuotSpace → carrier
  /-- The embedding is injective. -/
  ι_injective : ∀ {p q : D.QuotSpace}, ι p = ι q → p = q
  /-- The real-valued (`RC = CReal/Equiv`) inner product. -/
  cinner : carrier → carrier → CReal.RC
  /-- The inner product extends `⟨·,·⟩` on the dense image. -/
  ι_inner : ∀ a b : D.V,
    cinner (ι (D.qmk a)) (ι (D.qmk b)) = Quotient.mk CReal.crealSetoid (D.cInner a b)

/-- **CAPSTONE.**  The genuine constructive GNS Hilbert space: the metric
completion `GNSCompletionSpace` of the pre-Hilbert quotient, with the injective
dense embedding `embedQuot` and the completed real-valued inner product
`cinnerCompl`. -/
def gnsHilbertSpace : D.GNSHilbertSpace where
  carrier := GNSCompletionSpace D
  ι := embedQuot D
  ι_injective := fun h => embedQuot_injective D h
  cinner := D.cinnerCompl
  ι_inner := fun a b => D.cinnerCompl_embed a b

end GNSData

end YMGap.Continuum.GNSQuotient

/-! ## Task 5: the GNS Hilbert space of a finite-volume Wilson theory -/

namespace YMGap.Continuum.WilsonGNS

open YMGap.Continuum.GNSQuotient

/-- **The constructive GNS Hilbert space of the finite-volume Wilson theory.**
The Wilson observable bundle `W` yields a `GNSData` (`W.toGNSData`), whose metric
completion is the genuine real-valued GNS Hilbert space with the Wilson
observables densely and isometrically embedded. -/
def WilsonGNSData.gnsHilbertSpace {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A) :
    W.toGNSData.GNSHilbertSpace :=
  W.toGNSData.gnsHilbertSpace

end YMGap.Continuum.WilsonGNS

namespace YMGap.Constructive

/-! ## Axiom gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.abs_le_of_sq_le_sq
#print axioms YMGap.Constructive.Q'.le_ofNat_ceil
#print axioms YMGap.Constructive.Q'.invSucc_mul_ofNat_eqv_one
#print axioms YMGap.Constructive.Q'.budget_le
#print axioms YMGap.Constructive.CReal.ofQ'CauchySeq
#print axioms YMGap.Constructive.CReal.convergesTo_ofQ'CauchySeq
#print axioms YMGap.Constructive.CReal.Equiv_of_ofQ'_limit_close
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cs_term_bound
#print axioms YMGap.Continuum.GNSQuotient.GNSData.normCeil_bound
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_abs_bound
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInnerQCauchy
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_close
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_welldef
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_embed
#print axioms YMGap.Continuum.GNSQuotient.GNSData.gnsHilbertSpace
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.gnsHilbertSpace
