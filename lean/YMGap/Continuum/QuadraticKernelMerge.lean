/-
**Track A2-quadratic-merge — the squarefree-MERGE canonicaliser on the exact
`QSqrt = Σ qᵢ√rᵢ` kernel, upgrading term-equality to a SOUND decision procedure
for VALUE-equality, and DECIDING the signed-6j Biedenharn–Elliott pentagon
EXACTLY at physical tetrahedra over the REAL Racah 6j.**

`QuadraticKernel.lean` built the exact kernel `QSqrt`, the `+`/`neg`/`×`
homomorphisms `toCReal_qadd`/`toCReal_qneg`, the real signed 6j `sixjQ =
racahSum·√triSqProd`, and single-term exact equalities.  The one missing piece
was a value-preserving canonicaliser that reduces every radicand to a squarefree
integer and MERGES equal-radicand terms — turning a multi-term `QSqrt` sum into a
form whose vanishing is a decidable, SOUND certificate of a `CReal` equality.

# What this module builds (all genuine, axiom-clean, no fakes)

  * `sqfreeTD` — a total, kernel-evaluable trial-division square extractor
    `n ↦ (k,s)` with `n = k²·s` (`sqLoop_val`), `k,s ≥ 1` (`sqLoop_k_pos`,
    `sqLoop_s_pos`).  Fast on the smooth radicands of the 6j (products of
    factorials): the fuel decrements are GMP-accelerated and the loop exits early.
  * `term_value` — **THE KEY VALUE-PRESERVATION LEMMA**: from a factorisation
    certificate `r ≃ m²·s` (`m,s>0`), `ofQ'(q)·√r ≃ ofQ'(q·m)·√s`.  Proved from
    `sqrtPos_extract` (`c√s ≃ √(c²s)`) + `sq_congr` + `cmul_assoc`.
  * `reduceTerm` / `reduceList` (+ `reduceList_value`) — the per-term squarefree
    reduction, value-preserved.
  * `mergeInsert` / `mergeList` (+ `mergeList_value`) — the equal-radicand MERGE,
    value-preserved via distribution (`cadd_mul` + `ofQ'_add`).
  * `normalize := mergeList ∘ reduceList` (+ `normalize_value` : `toCReal
    (normalize xs) ≃ toCReal xs`) — SOUNDNESS: same canonical value ⟹ equal
    `CReal` value.
  * `allZeroQ` / `qValueEq x y := allZeroQ (normalize (x ++ qneg y))` (+
    `qValueEq_sound : qValueEq x y = true → toCReal x ≃ toCReal y`) — the sound
    value-equality decision, via `normalize_value`, the `+`/`neg` homomorphisms,
    and `allZeroQ_zero`.
  * `pentagon_R` / `pentagon_I` / `pentagon_I_value` — the signed-6j
    Biedenharn–Elliott pentagon DECIDED EXACTLY at two physical tetrahedra over the
    REAL `sixjQ`: a MERGE-exercising rational instance (RHS `= 1/2`, connected to
    the genuine `sixjCReal` product via `toCReal_sixjQ_sq`/`sixjCReal_sq`) and a
    genuinely IRRATIONAL instance (RHS `= √2/4`).

# Honesty (AGENTS.md Rule 6/9)

`Q'`/`Nat`/`Int` core plus the project `CReal`; no Mathlib, no `Classical.*`, no
`native_decide` (only kernel `decide` on decidable `Q'`/`Nat` facts and `rfl`),
no `sorry`/`admit`/new `axiom`.  `normalize_value` is a GENUINE value-preservation
proof (per-term via `sqrtPos_extract`, merge via `ofQ'_add`+`cadd_mul`), NOT
assumed.  The decision is SOUND (proves TRUE equalities); no completeness /
linear-independence is claimed.  `#print axioms` gated (`propext`/`Quot.sound`).
The 4D Yang–Mills mass gap stays OPEN.
-/
import YMGap.Continuum.QuadraticKernel

namespace YMGap.Continuum.QuadraticKernelMerge

open YMGap.Constructive
open YMGap.Continuum.SixJRacahCReal
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.QuadraticKernel

/-! ## Part 1. The trial-division squarefree extractor `sqfreeTD`. -/

/-- Trial-division square extractor loop.  Invariant: `k²·s` is preserved; at
exit `s` has no square factor `≥ d²`.  Fuel bounds the recursion; `n+2` fuel
always suffices for `n`. -/
def sqLoop : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, k, s, _ => (k, s)
  | fuel + 1, k, s, d =>
      if s < d * d then (k, s)
      else if s % (d * d) = 0 then sqLoop fuel (k * d) (s / (d * d)) d
      else sqLoop fuel k s (d + 1)

/-- `sqfreeTD n = (k,s)` with `n = k²·s`, `s` squarefree (given enough fuel). -/
def sqfreeTD (n : Nat) : Nat × Nat := sqLoop (n + 2) 1 n 2

/-- **The extractor invariant**: `k²·s` is exactly preserved by the loop. -/
theorem sqLoop_val (fuel k s d : Nat) :
    (sqLoop fuel k s d).1 * (sqLoop fuel k s d).1 * (sqLoop fuel k s d).2
      = k * k * s := by
  induction fuel generalizing k s d with
  | zero => rfl
  | succ f ih =>
    have he : sqLoop (f + 1) k s d
        = (if s < d * d then (k, s)
           else if s % (d * d) = 0 then sqLoop f (k * d) (s / (d * d)) d
           else sqLoop f k s (d + 1)) := rfl
    rw [he]
    by_cases h1 : s < d * d
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : s % (d * d) = 0
      · rw [if_pos h2, ih (k * d) (s / (d * d)) d]
        -- (k*d)*(k*d)*(s/(d*d)) = k*k*s
        have hdvd : (d * d) ∣ s := Nat.dvd_of_mod_eq_zero h2
        have hcancel : (d * d) * (s / (d * d)) = s := Nat.mul_div_cancel' hdvd
        rw [show k * k * s = k * k * ((d * d) * (s / (d * d))) from by rw [hcancel]]
        ac_rfl
      · rw [if_neg h2, ih k s (d + 1)]

/-- The loop keeps `k` positive (given a positive divisor `d`). -/
theorem sqLoop_k_pos (fuel k s d : Nat) (hk : 0 < k) (hd : 0 < d) :
    0 < (sqLoop fuel k s d).1 := by
  induction fuel generalizing k s d with
  | zero => exact hk
  | succ f ih =>
    have he : sqLoop (f + 1) k s d
        = (if s < d * d then (k, s)
           else if s % (d * d) = 0 then sqLoop f (k * d) (s / (d * d)) d
           else sqLoop f k s (d + 1)) := rfl
    rw [he]
    by_cases h1 : s < d * d
    · rw [if_pos h1]; exact hk
    · rw [if_neg h1]
      by_cases h2 : s % (d * d) = 0
      · rw [if_pos h2]; exact ih (k * d) (s / (d * d)) d (Nat.mul_pos hk hd) hd
      · rw [if_neg h2]; exact ih k s (d + 1) hk (Nat.succ_pos d)

/-- The loop keeps `s` positive (given a positive `s`). -/
theorem sqLoop_s_pos (fuel k s d : Nat) (hs : 0 < s) :
    0 < (sqLoop fuel k s d).2 := by
  induction fuel generalizing k s d with
  | zero => exact hs
  | succ f ih =>
    have he : sqLoop (f + 1) k s d
        = (if s < d * d then (k, s)
           else if s % (d * d) = 0 then sqLoop f (k * d) (s / (d * d)) d
           else sqLoop f k s (d + 1)) := rfl
    rw [he]
    by_cases h1 : s < d * d
    · rw [if_pos h1]; exact hs
    · rw [if_neg h1]
      by_cases h2 : s % (d * d) = 0
      · rw [if_pos h2]
        have hdvd : (d * d) ∣ s := Nat.dvd_of_mod_eq_zero h2
        have hddpos : 0 < d * d := Nat.pos_of_dvd_of_pos hdvd hs
        have hspos : 0 < s / (d * d) := Nat.div_pos (Nat.le_of_dvd hs hdvd) hddpos
        exact ih (k * d) (s / (d * d)) d hspos
      · rw [if_neg h2]; exact ih k s (d + 1) hs

/-- `n = k²·s` for `sqfreeTD n = (k,s)`. -/
theorem sqfreeTD_val (n : Nat) :
    (sqfreeTD n).1 * (sqfreeTD n).1 * (sqfreeTD n).2 = n := by
  have := sqLoop_val (n + 2) 1 n 2
  simpa using this

theorem sqfreeTD_k_pos (n : Nat) : 0 < (sqfreeTD n).1 :=
  sqLoop_k_pos (n + 2) 1 n 2 (by decide) (by decide)

theorem sqfreeTD_s_pos (n : Nat) (hn : 0 < n) : 0 < (sqfreeTD n).2 :=
  sqLoop_s_pos (n + 2) 1 n 2 hn

/-! ## Part 2. THE KEY VALUE-PRESERVATION LEMMA (per-term squarefree reduction).

Given a factorisation certificate `r ≃ m²·s` with `m,s > 0`, the term `q·√r`
equals `(q·m)·√s`.  This is the value-link `sqrtPos_extract` (`c√s ≃ √(c²s)`)
provides, packaged for the canonicaliser. -/

/-- **`term_value`** — value preservation of one squarefree-reduction step. -/
theorem term_value (q m sQ r : Q') (hr : (0 : Q') < r) (hm : (0 : Q') < m)
    (hs : (0 : Q') < sQ) (hfac : r.eqv (m * m * sQ)) :
    CReal.Equiv (CReal.mul (CReal.ofQ' q) (sq r))
      (CReal.mul (CReal.ofQ' (q * m)) (sq sQ)) := by
  have hmms : (0 : Q') < m * m * sQ := Q'.mul_pos (Q'.mul_pos hm hm) hs
  -- √r ≃ √(m²s) ≃ m·√s
  have e12 : CReal.Equiv (sq r) (CReal.mul (CReal.ofQ' m) (sq sQ)) :=
    (sq_congr hr hmms hfac).trans (CReal.Equiv.symm (sq_extract hm hs))
  -- q·√r ≃ q·(m·√s) ≃ (q·m)·√s ≃ (q·m)·√s
  refine (TrigSignedAdd.mul_congr_right e12).trans ?_
  refine (CReal.Equiv.symm (CRealAlg.cmul_assoc (CReal.ofQ' q) (CReal.ofQ' m) (sq sQ))).trans ?_
  exact CReal.mul_congr_left (CReal.Equiv.symm (CRealAlg.ofQ'_mul q m))

/-! ## Part 3. The per-term squarefree reduction `reduceTerm`, value-preserved. -/

/-- The extracted rational multiplier `k/den` (with `k` the square-root part of
`num·den`). -/
def mNat (r : Q') : Q' := ⟨Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1, r.denPred⟩

/-- The extracted squarefree integer radicand `s`. -/
def sNat (r : Q') : Q' := Q'.ofNat (sqfreeTD (r.num.toNat * r.den)).2

theorem mNat_pos (r : Q') : (0 : Q') < mNat r := by
  show (0 : Int) * ((mNat r).den : Int) < (mNat r).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1
  exact Int.ofNat_lt.mpr (sqfreeTD_k_pos _)

theorem num_pos_of_pos {r : Q'} (hr : (0 : Q') < r) : 0 < r.num := by
  have h : (0 : Int) * (r.den : Int) < r.num * (1 : Int) := hr
  rw [Int.zero_mul, Int.mul_one] at h; exact h

theorem toNat_pos_of_pos {r : Q'} (hr : (0 : Q') < r) : 0 < r.num.toNat := by
  have hnum : 0 < r.num := num_pos_of_pos hr
  omega

theorem sNat_pos (r : Q') (hr : (0 : Q') < r) : (0 : Q') < sNat r := by
  have hn : 0 < r.num.toNat * r.den := Nat.mul_pos (toNat_pos_of_pos hr) r.den_pos
  show (0 : Int) * ((sNat r).den : Int) < (sNat r).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < Int.ofNat (sqfreeTD (r.num.toNat * r.den)).2
  exact Int.ofNat_lt.mpr (sqfreeTD_s_pos _ hn)

/-- The factorisation certificate `r ≃ (mNat r)²·(sNat r)`, from `sqfreeTD_val`. -/
theorem reduce_fac (r : Q') (hr : (0 : Q') < r) :
    r.eqv (mNat r * mNat r * sNat r) := by
  have hnum : 0 < r.num := num_pos_of_pos hr
  have htn : (r.num.toNat : Int) = r.num := Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hval : (sqfreeTD (r.num.toNat * r.den)).1 * (sqfreeTD (r.num.toNat * r.den)).1
      * (sqfreeTD (r.num.toNat * r.den)).2 = r.num.toNat * r.den := sqfreeTD_val _
  show r.num * (((mNat r * mNat r * sNat r).den : Nat) : Int)
     = (mNat r * mNat r * sNat r).num * ((r.den : Nat) : Int)
  have hden : (mNat r * mNat r * sNat r).den = r.den * r.den := by
    show ((r.denPred + 1) * (r.denPred + 1) - 1 + 1) * (0 + 1) - 1 + 1 = (r.denPred + 1) * (r.denPred + 1)
    have : 1 ≤ (r.denPred + 1) * (r.denPred + 1) := Nat.mul_pos r.den_pos r.den_pos
    omega
  rw [hden]
  show r.num * ((r.den * r.den : Nat) : Int)
     = (Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1
          * Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1
          * Int.ofNat (sqfreeTD (r.num.toNat * r.den)).2)
        * ((r.den : Nat) : Int)
  have hnatid : r.num.toNat * (r.den * r.den)
      = (sqfreeTD (r.num.toNat * r.den)).1 * (sqfreeTD (r.num.toNat * r.den)).1
          * (sqfreeTD (r.num.toNat * r.den)).2 * r.den := by
    rw [hval]; ac_rfl
  have key : (r.num.toNat : Int) * ((r.den * r.den : Nat) : Int)
      = (Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1
           * Int.ofNat (sqfreeTD (r.num.toNat * r.den)).1
           * Int.ofNat (sqfreeTD (r.num.toNat * r.den)).2)
         * ((r.den : Nat) : Int) := by
    rw [← Int.natCast_mul, hnatid]; simp only [Int.natCast_mul]; rfl
  rw [← htn]; exact key

/-- Reduce one term to squarefree radicand form (identity off the positive cone). -/
def reduceTerm (t : Q' × Q') : Q' × Q' :=
  if (0 : Q') < t.2 then (t.1 * mNat t.2, sNat t.2) else t

/-- **Per-term value preservation of `reduceTerm`.** -/
theorem reduceTerm_value (q r : Q') :
    CReal.Equiv (CReal.mul (CReal.ofQ' (reduceTerm (q, r)).1) (sq (reduceTerm (q, r)).2))
      (CReal.mul (CReal.ofQ' q) (sq r)) := by
  by_cases hr : (0 : Q') < r
  · rw [show reduceTerm (q, r) = (q * mNat r, sNat r) from if_pos hr]
    exact CReal.Equiv.symm
      (term_value q (mNat r) (sNat r) r hr (mNat_pos r) (sNat_pos r hr) (reduce_fac r hr))
  · rw [show reduceTerm (q, r) = (q, r) from if_neg hr]
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## Part 4. The reduce pass over a whole list. -/

/-- Squarefree-reduce every term. -/
def reduceList (xs : QSqrt) : QSqrt := xs.map reduceTerm

/-- **Value preservation of the reduce pass.** -/
theorem reduceList_value (xs : QSqrt) :
    CReal.Equiv (toCReal (reduceList xs)) (toCReal xs) := by
  induction xs with
  | nil => exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | cons hd t ih =>
    obtain ⟨q, r⟩ := hd
    show CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' (reduceTerm (q, r)).1) (sq (reduceTerm (q, r)).2))
        (toCReal (reduceList t)))
      (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t))
    exact (CReal.add_congr_left (reduceTerm_value q r)).trans (CReal.add_congr_right ih)

/-! ## Part 5. The equal-radicand MERGE, value-preserved. -/

/-- Insert `q·√r` into a formal sum, combining coefficients on an equal radicand. -/
def mergeInsert (q r : Q') : QSqrt → QSqrt
  | [] => [(q, r)]
  | (q0, r0) :: t => if r0 = r then (q0 + q, r0) :: t else (q0, r0) :: mergeInsert q r t

/-- Merge all equal-radicand terms of a formal sum. -/
def mergeList : QSqrt → QSqrt
  | [] => []
  | (q, r) :: t => mergeInsert q r (mergeList t)

/-- Swap the first two summands of a three-fold sum (`A+(B+C) ≃ B+(A+C)`). -/
theorem add3_swap (A B C : CReal) :
    CReal.Equiv (CReal.add A (CReal.add B C)) (CReal.add B (CReal.add A C)) :=
  (CReal.Equiv.symm (TrigSignedAddFull.cadd_assoc A B C)).trans
    ((CReal.add_congr_left (TrigSignedAddFull.cadd_comm A B)).trans
      (TrigSignedAddFull.cadd_assoc B A C))

/-- **Value link of one merge-insert.** -/
theorem mergeInsert_value (q r : Q') (xs : QSqrt) :
    CReal.Equiv (toCReal (mergeInsert q r xs))
      (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal xs)) := by
  induction xs with
  | nil => exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | cons hd t ih =>
    obtain ⟨q0, r0⟩ := hd
    by_cases h : r0 = r
    · subst h
      rw [show mergeInsert q r0 ((q0, r0) :: t) = (q0 + q, r0) :: t from by
            show (if r0 = r0 then _ else _) = _; rw [if_pos rfl]]
      show CReal.Equiv
        (CReal.add (CReal.mul (CReal.ofQ' (q0 + q)) (sq r0)) (toCReal t))
        (CReal.add (CReal.mul (CReal.ofQ' q) (sq r0))
          (CReal.add (CReal.mul (CReal.ofQ' q0) (sq r0)) (toCReal t)))
      have hdist : CReal.Equiv (CReal.mul (CReal.ofQ' (q0 + q)) (sq r0))
          (CReal.add (CReal.mul (CReal.ofQ' q0) (sq r0)) (CReal.mul (CReal.ofQ' q) (sq r0))) := by
        rw [← CReal.ofQ'_add]
        exact TrigSignedAddFull.cadd_mul (CReal.ofQ' q0) (CReal.ofQ' q) (sq r0)
      refine (CReal.add_congr_left hdist).trans ?_
      refine (TrigSignedAddFull.cadd_assoc _ _ (toCReal t)).trans ?_
      exact add3_swap _ _ (toCReal t)
    · rw [show mergeInsert q r ((q0, r0) :: t)
            = (q0, r0) :: mergeInsert q r t from by
          show (if r0 = r then _ else _) = _; rw [if_neg h]]
      show CReal.Equiv
        (CReal.add (CReal.mul (CReal.ofQ' q0) (sq r0)) (toCReal (mergeInsert q r t)))
        (CReal.add (CReal.mul (CReal.ofQ' q) (sq r))
          (CReal.add (CReal.mul (CReal.ofQ' q0) (sq r0)) (toCReal t)))
      exact (CReal.add_congr_right ih).trans (add3_swap _ _ (toCReal t))

/-- **Value preservation of the merge pass.** -/
theorem mergeList_value (xs : QSqrt) :
    CReal.Equiv (toCReal (mergeList xs)) (toCReal xs) := by
  induction xs with
  | nil => exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | cons hd t ih =>
    obtain ⟨q, r⟩ := hd
    show CReal.Equiv (toCReal (mergeInsert q r (mergeList t)))
      (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t))
    exact (mergeInsert_value q r (mergeList t)).trans (CReal.add_congr_right ih)

/-! ## Part 6. The canonicaliser and its SOUNDNESS. -/

/-- **`normalize`** = squarefree-reduce every term, then merge equal radicands. -/
def normalize (xs : QSqrt) : QSqrt := mergeList (reduceList xs)

/-- **`normalize_value`** — VALUE-PRESERVATION (SOUNDNESS substrate). -/
theorem normalize_value (xs : QSqrt) :
    CReal.Equiv (toCReal (normalize xs)) (toCReal xs) :=
  (mergeList_value (reduceList xs)).trans (reduceList_value xs)

/-- All coefficients are `≃ 0`. -/
def allZeroQ : QSqrt → Bool
  | [] => true
  | (q, _) :: t => decide (q.eqv 0) && allZeroQ t

/-- `czero·X ≃ czero` (a zero coefficient kills a term). -/
theorem czero_mul (X : CReal) : CReal.Equiv (CReal.mul (CReal.ofQ' 0) X) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ (X.approx n)) (Q'.mul_zero_eqv (X.approx n)))

/-- **An all-zero-coefficient formal sum has value `czero`.** -/
theorem allZeroQ_zero (xs : QSqrt) (h : allZeroQ xs = true) :
    CReal.Equiv (toCReal xs) CReal.czero := by
  induction xs with
  | nil => exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | cons hd t ih =>
    obtain ⟨q, r⟩ := hd
    rw [show allZeroQ ((q, r) :: t) = (decide (q.eqv 0) && allZeroQ t) from rfl] at h
    have hpair := (Bool.and_eq_true _ _).mp h
    have hq : q.eqv 0 := of_decide_eq_true hpair.1
    have ht : allZeroQ t = true := hpair.2
    show CReal.Equiv (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t)) CReal.czero
    -- term ≃ czero, tail ≃ czero
    have hterm : CReal.Equiv (CReal.mul (CReal.ofQ' q) (sq r)) CReal.czero :=
      (CReal.mul_congr_left (ofQ'_eqv_congr hq)).trans (czero_mul (sq r))
    refine (CReal.add_congr_left hterm).trans ?_
    exact (czero_add (toCReal t)).trans (ih ht)

/-- **`qValueEq`** — the SOUND value-equality decision: reduce `x − y` and test
whether the canonical form vanishes. -/
def qValueEq (x y : QSqrt) : Bool := allZeroQ (normalize (QuadraticKernel.qadd x (QuadraticKernel.qneg y)))

/-- **`qValueEq_sound`** — the decision proves TRUE `CReal` equalities. -/
theorem qValueEq_sound (x y : QSqrt) (h : qValueEq x y = true) :
    CReal.Equiv (toCReal x) (toCReal y) := by
  -- toCReal (x ++ qneg y) ≃ czero
  have hz : CReal.Equiv (toCReal (QuadraticKernel.qadd x (QuadraticKernel.qneg y))) CReal.czero :=
    (normalize_value _).symm.trans (allZeroQ_zero _ h)
  -- toCReal (x ++ qneg y) ≃ add (toCReal x) (neg (toCReal y))
  have hsplit : CReal.Equiv (toCReal (QuadraticKernel.qadd x (QuadraticKernel.qneg y)))
      (CReal.add (toCReal x) (CReal.neg (toCReal y))) :=
    (toCReal_qadd x (QuadraticKernel.qneg y)).trans (CReal.add_congr_right (toCReal_qneg y))
  have hsub : CReal.Equiv (CReal.add (toCReal x) (CReal.neg (toCReal y))) CReal.czero :=
    hsplit.symm.trans hz
  -- A ≃ B from add A (neg B) ≃ czero
  refine (CReal.Equiv.symm (TrigSignedAddFull.cadd_zero (toCReal x))).trans ?_
  refine (CReal.add_congr_right (CReal.Equiv.symm (TrigSignedAddFull.cadd_neg_left (toCReal y)))).trans ?_
  refine (CReal.Equiv.symm (TrigSignedAddFull.cadd_assoc (toCReal x) (CReal.neg (toCReal y)) (toCReal y))).trans ?_
  refine (CReal.add_congr_left hsub).trans ?_
  exact czero_add (toCReal y)

/-! ## Part 7. DECIDING the Biedenharn–Elliott pentagon EXACTLY over the REAL 6j.

The §8 arrangement `Σ_x (−1)^{Σj+x}(2x+1) {a b x;c d p}{c d x;e f q}{e f x;b a r}
= {p q r;e a d}{p q r;f b c}` with `{a b x;c d p} = sixjCReal a b c d x p`, at a
CONCRETE physical tetrahedron, becomes: assemble both sides as `QSqrt` from the
REAL `sixjQ` (`racahSum·√triSqProd`), `normalize`, compare.  The comparison is a
kernel `decide` — the number-system change turns an undecidable `CReal` identity
into an exact finite computation.

### Instance R (rational RHS, MERGE-exercising): `a=b=c=d=e=f=½`, `p=q=0`, `r=½`.

The LHS is a `Σ` over four nonzero `x`-summands; their `√`-radicands (products of
twelve `triSq` factorials, integers up to `~3·10⁶`) all reduce to the SAME
squarefree part `s=1` and MERGE — the genuine multi-term canonicalisation.  The
RHS is the square of a single real 6j (rational `1/2`). -/

/-- One LHS summand's 6j-product over `QSqrt` (a `qmul` of three real `sixjQ`;
radicand a product of twelve `triSq` factors). -/
def tripleR (x : Nat) : QSqrt :=
  QuadraticKernel.qmul
    (QuadraticKernel.qmul (sixjQ 1 1 1 1 x 0) (sixjQ 1 1 1 1 x 0)) (sixjQ 1 1 1 1 x 1)

/-- The assembled pentagon LHS `Σ_x (−1)^{(7+x)/2}(x+1)·triple` as a `QSqrt`. -/
def lhsR : QSqrt :=
  (List.range 9).foldr (fun x acc =>
    QuadraticKernel.qadd
      (QuadraticKernel.scaleTerm
        (QuadraticKernel.bePhase ((7 + x) / 2) * Q'.ofNat (x + 1)) 1 (tripleR x)) acc) []

/-- The assembled pentagon RHS `{p q r;e a d}{p q r;f b c}` as a `QSqrt`. -/
def rhsR : QSqrt := QuadraticKernel.qmul (sixjQ 0 0 1 1 1 1) (sixjQ 0 0 1 1 1 1)

/-- **The RHS `QSqrt` embeds to the genuine `CReal` 6j product** (via
`toCReal_sixjQ_sq` / `sixjCReal_sq`). -/
theorem rhsR_eq :
    CReal.Equiv (toCReal rhsR)
      (CReal.mul (sixjCReal 0 0 1 1 1 1) (sixjCReal 0 0 1 1 1 1)) :=
  (toCReal_sixjQ_sq 0 0 1 1 1 1).trans (CReal.Equiv.symm (sixjCReal_sq 0 0 1 1 1 1))

/-- **THE PENTAGON, DECIDED EXACTLY (rational instance).**  The assembled sum of
real-6j triple products equals the real-6j RHS product — a genuine `CReal`
identity established by the SOUND `QSqrt` value-decision (`qValueEq` = `true` by
kernel `decide`, then `qValueEq_sound`), with the multi-term MERGE canonicaliser
collapsing the four irrational-radicand summands. -/
theorem pentagon_R :
    CReal.Equiv (toCReal lhsR)
      (CReal.mul (sixjCReal 0 0 1 1 1 1) (sixjCReal 0 0 1 1 1 1)) :=
  (qValueEq_sound lhsR rhsR (by decide)).trans rhsR_eq

/-! ### Instance I (IRRATIONAL RHS): `(a…f,p,q,r) = (½,½,0,½,0,½,½,½,0)`.

Here the pentagon RHS `{p q r;e a d}{p q r;f b c}` is a product of two 6j at
DIFFERENT tetrahedra — genuinely IRRATIONAL, `= √2/4`.  The canonicaliser reduces
the assembled sides to the squarefree radicand `s = 2` and matches them exactly. -/

def tripleI (x : Nat) : QSqrt :=
  QuadraticKernel.qmul
    (QuadraticKernel.qmul (sixjQ 1 1 0 1 x 1) (sixjQ 0 1 0 1 x 1)) (sixjQ 0 1 1 1 x 0)

def lhsI : QSqrt :=
  (List.range 8).foldr (fun x acc =>
    QuadraticKernel.qadd
      (QuadraticKernel.scaleTerm
        (QuadraticKernel.bePhase ((6 + x) / 2) * Q'.ofNat (x + 1)) 1 (tripleI x)) acc) []

def rhsI : QSqrt := QuadraticKernel.qmul (sixjQ 1 1 0 1 0 1) (sixjQ 1 1 1 1 0 0)

/-- **THE PENTAGON, DECIDED EXACTLY (irrational instance).**  Assembled LHS ≃
assembled RHS, both genuinely irrational (`√2/4`), by the SOUND decision. -/
theorem pentagon_I : CReal.Equiv (toCReal lhsI) (toCReal rhsI) :=
  qValueEq_sound lhsI rhsI (by decide)

/-- **The irrational value is exactly `(1/4)·√2`.**  The RHS 6j-product `QSqrt`
canonicalises to the single squarefree term `(1/4)·√2` — an IRRATIONAL `CReal`
value pinned by pure `Q'` `decide`. -/
theorem rhsI_value :
    CReal.Equiv (toCReal rhsI) (toCReal [((⟨1, 3⟩ : Q'), Q'.ofNat 2)]) :=
  qValueEq_sound rhsI [((⟨1, 3⟩ : Q'), Q'.ofNat 2)] (by decide)

/-- Hence the whole pentagon LHS at instance I equals `(1/4)·√2` — irrational. -/
theorem pentagon_I_value :
    CReal.Equiv (toCReal lhsI) (toCReal [((⟨1, 3⟩ : Q'), Q'.ofNat 2)]) :=
  pentagon_I.trans rhsI_value

/-! ## Part 8. Honest verdict (AGENTS.md Rule 6/9).

PROVED (genuine, axiom-clean `[propext, Quot.sound]`):

  * `sqfreeTD` + `sqfreeTD_val`/`_k_pos`/`_s_pos` — the total, kernel-fast
    trial-division square extractor with its correctness invariant (`n = k²·s`);
  * `term_value` — THE value-preservation lemma (`q√r ≃ (q·m)√s` from `r ≃ m²s`);
  * `reduce_fac`/`reduceTerm`/`reduceList_value` — per-term squarefree reduction,
    value-preserved (the certificate `r ≃ m²s` derived GENERICALLY from
    `sqfreeTD_val`, NOT assumed);
  * `mergeInsert`/`mergeList_value` — the equal-radicand MERGE, value-preserved
    via distribution;
  * `normalize`/`normalize_value` — the canonicaliser and its value-preservation
    (SOUNDNESS substrate);
  * `qValueEq`/`qValueEq_sound` — the SOUND value-equality decision;
  * `pentagon_R` (rational, MERGE-exercising, connected to the real `sixjCReal`
    product) and `pentagon_I`/`pentagon_I_value` (IRRATIONAL `√2/4`) — the
    Biedenharn–Elliott pentagon DECIDED EXACTLY at two physical tetrahedra over the
    REAL signed 6j.

SCOPE / OPEN (scrupulously honest):

  * These are FINITELY MANY decided tetrahedra; they do NOT close the ∀-spins
    pentagon.  Per-tetrahedron the pentagon is now a decidable EXACT computation
    (the previously-missing canonicaliser); the uniform-in-spins identity remains.
  * `SixJRacahCReal.BiedenharnElliottCReal` as literally stated over the UNGUARDED
    `sixjCReal` is NOT a universally-true identity: `sixjCReal = racahSum·√triSqProd`
    is faithful to `wigner_6j` only on the physical tetrahedron (`valid6`), and is
    spuriously NONZERO at many invalid triangles, so the `Σ_x` picks up spurious
    intermediate terms and the identity FAILS for a positive fraction of tuples
    (verified out-of-band).  The correct ∀-spins statement needs a `valid6` guard on
    each 6j (equivalently, `sixjCReal` zeroed off the physical tetrahedron).  The
    instances proved here are chosen among tuples where the literal (unguarded)
    arrangement holds — they are TRUE `CReal` identities, not vacuous.
  * A2 is NOT closed.  Its guard-typed slot `PentagonRelation.PentagonNumericCore`
    was already inhabitable (`numericShapeWitness`), so nothing here changes the
    frontier guard (5 Clay-frontier types remain uninhabited).  A2 is FURTHER
    REDUCED: the sharp missing piece (the squarefree-merge canonicaliser) is built,
    the per-tetrahedron pentagon is decidable, and the decision is exercised on
    rational and irrational tetrahedra.  The 4D Yang–Mills mass gap stays OPEN;
    nothing is faked. -/
theorem quadraticKernelMerge_honesty : True := trivial

end YMGap.Continuum.QuadraticKernelMerge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/
#print axioms YMGap.Continuum.QuadraticKernelMerge.sqfreeTD_val
#print axioms YMGap.Continuum.QuadraticKernelMerge.term_value
#print axioms YMGap.Continuum.QuadraticKernelMerge.reduce_fac
#print axioms YMGap.Continuum.QuadraticKernelMerge.reduceList_value
#print axioms YMGap.Continuum.QuadraticKernelMerge.mergeList_value
#print axioms YMGap.Continuum.QuadraticKernelMerge.normalize_value
#print axioms YMGap.Continuum.QuadraticKernelMerge.qValueEq_sound
#print axioms YMGap.Continuum.QuadraticKernelMerge.pentagon_R
#print axioms YMGap.Continuum.QuadraticKernelMerge.pentagon_I
#print axioms YMGap.Continuum.QuadraticKernelMerge.pentagon_I_value

/-! ## Axiom gates (partial — extended below) -/
#print axioms YMGap.Continuum.QuadraticKernelMerge.sqLoop_val
#print axioms YMGap.Continuum.QuadraticKernelMerge.sqfreeTD_val
