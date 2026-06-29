/-
The polynomial SOS-factorization identity for the SU(2) heat-kernel **3×3**
Gram energy, at the `CReal` level.

With the single base `a = e^{−t/4}` and the moments `m_k = (k+1)·a^{k(k+2)}`
(`Pivot3Moments`), the scaled energy `P·form3` (with `P = 3a⁴+2a²+1`) is a
manifest sum of three nonnegatively-weighted squares:

    P·form3 = P·M₀² + 1·M₁² + big·M₂²,

    M₀ = c₀ + m₁c₁ + m₂c₂,
    M₁ = (1−a²)·(P·c₁ + S₁₂'·c₂),     S₁₂' = 2a³(a²+1)²(2a⁴+1),
    M₂ = (1−a²)²(a²+1)·c₂,
    big = 15a¹⁶+24a¹⁴+36a¹²+36a¹⁰+32a⁸+20a⁶+12a⁴+4a²+1   (positive coeffs).

This file fixes the explicit `CReal` building blocks (everything as a polynomial
in the base `a = base t ht`), proves the moment-substitution
`form3 ≃ form3Base`, and discharges the (degree-32) polynomial identity
`P·form3Base ≃ sos3` by reducing it — coefficient-by-coefficient in the six
`c`-monomials `c₀², c₁², c₂², c₀c₁, c₀c₂, c₁c₂` — to univariate `Q'` polynomial
identities in `q = a.approx n`, each discharged by the reflective `QPoly` ring
(`decide` on coefficient lists).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot3Defs
import YMGap.Continuum.Pivot3Moments
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.Pivot3

open YMGap.Constructive

/-! ## Moment substitution: `form3 ≃ form3Base`

Each moment `m_k = (k+1)·a^{k(k+2)}` is `≃ (k+1)·rawPowC a (k(k+2))`, the nested
power of the base.  We re-express `form3` entirely in `rawPowC base`. -/

/-- `m₁ ≃ 2·rawPowC a 3`. -/
theorem m1_base (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m1 t ht) (smul 2 (rawPowC (base t ht) 3)) :=
  mul_congr_right (A := C 2) (apow_eq_rawPow t ht 3).symm

/-- `m₂ ≃ 3·rawPowC a 8`. -/
theorem m2_base (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m2 t ht) (smul 3 (rawPowC (base t ht) 8)) :=
  mul_congr_right (A := C 3) (apow_eq_rawPow t ht 8).symm

/-- `m₃ ≃ 4·rawPowC a 15`. -/
theorem m3_base (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m3 t ht) (smul 4 (rawPowC (base t ht) 15)) :=
  mul_congr_right (A := C 4) (apow_eq_rawPow t ht 15).symm

/-- `m₄ ≃ 5·rawPowC a 24`. -/
theorem m4_base (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m4 t ht) (smul 5 (rawPowC (base t ht) 24)) :=
  mul_congr_right (A := C 5) (apow_eq_rawPow t ht 24).symm

/-! ## The symmetric quadratic form `qform`

`qform A B Cc D E F c₀ c₁ c₂ = A·c₀² + B·c₁² + Cc·c₂² + D·(2c₀c₁) + E·(2c₀c₂)
+ F·(2c₁c₂)`, with `CReal` matrix entries `A,…,F` and rational arguments
`c₀,c₁,c₂`.  `form3` is `qform` of the Gram entries (definitionally), and the
SOS side is `qform` of explicit base-polynomial entries; matching the six
entries (univariate `QPoly` identities in the base) proves the energy identity. -/
def qform (A B Cc D E F : CReal) (c0 c1 c2 : Q') : CReal :=
  CReal.add
    (CReal.add
      (CReal.add (CReal.mul (CReal.ofQ' (c0 * c0)) A)
                 (CReal.mul (CReal.ofQ' (c1 * c1)) B))
      (CReal.add (CReal.mul (CReal.ofQ' (c2 * c2)) Cc)
                 (CReal.mul (CReal.ofQ' (2 * (c0 * c1))) D)))
    (CReal.add (CReal.mul (CReal.ofQ' (2 * (c0 * c2))) E)
               (CReal.mul (CReal.ofQ' (2 * (c1 * c2))) F))

/-- `form3` is `qform` of the (moment) Gram entries — definitionally. -/
theorem form3_eq_qform (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    form3 t ht c0 c1 c2
      = qform G00 (G11 t ht) (G22 t ht) (G01 t ht) (G02 t ht) (G12 t ht) c0 c1 c2 :=
  rfl

/-- `qform` is an `Equiv`-congruence in all six matrix entries. -/
theorem qform_congr {A B Cc D E F A' B' Cc' D' E' F' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') (hC : CReal.Equiv Cc Cc')
    (hD : CReal.Equiv D D') (hE : CReal.Equiv E E') (hF : CReal.Equiv F F')
    (c0 c1 c2 : Q') :
    CReal.Equiv (qform A B Cc D E F c0 c1 c2) (qform A' B' Cc' D' E' F' c0 c1 c2) :=
  add_congr
    (add_congr
      (add_congr (mul_congr_right (A := CReal.ofQ' (c0 * c0)) hA)
                 (mul_congr_right (A := CReal.ofQ' (c1 * c1)) hB))
      (add_congr (mul_congr_right (A := CReal.ofQ' (c2 * c2)) hC)
                 (mul_congr_right (A := CReal.ofQ' (2 * (c0 * c1))) hD)))
    (add_congr (mul_congr_right (A := CReal.ofQ' (2 * (c0 * c2))) hE)
               (mul_congr_right (A := CReal.ofQ' (2 * (c1 * c2))) hF))

/-! ## `CReal` ring helpers (via pointwise reduction)

None live in the substrate; each reduces a `CReal.Equiv` to the corresponding
`Q'` identity through `Equiv_of_approx_eqv`. -/

/-- `a·(b+c) ≃ a·b + a·c`. -/
theorem mul_add_equiv (a b c : CReal) :
    CReal.Equiv (CReal.mul a (CReal.add b c))
      (CReal.add (CReal.mul a b) (CReal.mul a c)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv (a.approx n) (b.approx n) (c.approx n))

/-- `p·(C 0) ≃ C 0` (the zero CReal absorbs). -/
theorem mul_C0_eqv (p : CReal) : CReal.Equiv (CReal.mul p (C 0)) (C 0) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show (p.approx n * Q'.ofNat 0).eqv (Q'.ofNat 0)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (p.approx n) (Q'.ofNat 0) 0 (by decide))
      (Q'.eqv_trans _ _ _ (QPoly.q_mul_zero (p.approx n)) (by decide)))

/-- `(a·b)·c ≃ a·(b·c)`. -/
theorem mul_assoc_equiv (a b c : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul a b) c) (CReal.mul a (CReal.mul b c)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv (a.approx n) (b.approx n) (c.approx n))

/-- `p·(ofQ' m · X) ≃ ofQ' m · (p·X)` — pull the rational weight outside. -/
theorem mul_ofQ'_swap (p : CReal) (m : Q') (X : CReal) :
    CReal.Equiv (CReal.mul p (CReal.mul (CReal.ofQ' m) X))
      (CReal.mul (CReal.ofQ' m) (CReal.mul p X)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show (p.approx n * (m * X.approx n)).eqv (m * (p.approx n * X.approx n))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (p.approx n) m (X.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (p.approx n * m) (m * p.approx n) (X.approx n)
        (Q'.mul_comm_eqv (p.approx n) m)) ?_
    exact Q'.mul_assoc_eqv m (p.approx n) (X.approx n))

/-- **Scale a `qform` by a `CReal` weight `p`:** `p·qform(A..F) ≃
qform(p·A, …, p·F)`.  Distributes `p` over the six terms and pulls it past
each rational coefficient. -/
theorem qform_scale (p A B Cc D E F : CReal) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul p (qform A B Cc D E F c0 c1 c2))
      (qform (CReal.mul p A) (CReal.mul p B) (CReal.mul p Cc)
             (CReal.mul p D) (CReal.mul p E) (CReal.mul p F) c0 c1 c2) := by
  unfold qform
  -- distribute p over the top-level (… + …)
  refine equiv_trans (mul_add_equiv p _ _) ?_
  refine add_congr ?_ ?_
  · refine equiv_trans (mul_add_equiv p _ _) ?_
    refine add_congr ?_ ?_
    · refine equiv_trans (mul_add_equiv p _ _) ?_
      exact add_congr (mul_ofQ'_swap p (c0 * c0) A) (mul_ofQ'_swap p (c1 * c1) B)
    · refine equiv_trans (mul_add_equiv p _ _) ?_
      exact add_congr (mul_ofQ'_swap p (c2 * c2) Cc) (mul_ofQ'_swap p (2 * (c0 * c1)) D)
  · refine equiv_trans (mul_add_equiv p _ _) ?_
    exact add_congr (mul_ofQ'_swap p (2 * (c0 * c2)) E) (mul_ofQ'_swap p (2 * (c1 * c2)) F)

/-- Pointwise distribute a rational coefficient over a sum of two `CReal`
matrix entries: `ofQ' m·(A+A') ≃ ofQ' m·A + ofQ' m·A'`. -/
theorem ofQ'_mul_add (m : Q') (A A' : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' m) (CReal.add A A'))
      (CReal.add (CReal.mul (CReal.ofQ' m) A) (CReal.mul (CReal.ofQ' m) A')) :=
  mul_add_equiv (CReal.ofQ' m) A A'

/-- Regroup `(p+p')+(q+q') ≃ (p+q)+(p'+q')` for `CReal`s (pointwise). -/
theorem add_interchange (p p' q q' : CReal) :
    CReal.Equiv (CReal.add (CReal.add p p') (CReal.add q q'))
      (CReal.add (CReal.add p q) (CReal.add p' q')) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_interchange (p.approx n) (p'.approx n) (q.approx n) (q'.approx n))

/-- **Add two `qform`s entrywise:** `qform(A..F) + qform(A'..F') ≃
qform(A+A', …, F+F')`. -/
theorem qform_add (A B Cc D E F A' B' Cc' D' E' F' : CReal) (c0 c1 c2 : Q') :
    CReal.Equiv
      (CReal.add (qform A B Cc D E F c0 c1 c2) (qform A' B' Cc' D' E' F' c0 c1 c2))
      (qform (CReal.add A A') (CReal.add B B') (CReal.add Cc Cc')
             (CReal.add D D') (CReal.add E E') (CReal.add F F') c0 c1 c2) := by
  unfold qform
  -- Group the two 3-level trees into matching summands, then fuse each
  -- `ofQ' m·X + ofQ' m·X' ≃ ofQ' m·(X+X')`.
  refine equiv_trans (add_interchange _ _ _ _) ?_
  -- after interchange the two `(…+…)` subtrees pair up; recurse with add_interchange
  refine add_congr ?_ ?_
  · refine equiv_trans (add_interchange _ _ _ _) ?_
    refine add_congr ?_ ?_
    · refine equiv_trans (add_interchange _ _ _ _) ?_
      exact add_congr (ofQ'_mul_add (c0*c0) A A').symm (ofQ'_mul_add (c1*c1) B B').symm
    · refine equiv_trans (add_interchange _ _ _ _) ?_
      exact add_congr (ofQ'_mul_add (c2*c2) Cc Cc').symm
        (ofQ'_mul_add (2*(c0*c1)) D D').symm
  · refine equiv_trans (add_interchange _ _ _ _) ?_
    exact add_congr (ofQ'_mul_add (2*(c0*c2)) E E').symm
      (ofQ'_mul_add (2*(c1*c2)) F F').symm

/-! ## Square expansion of a three-term linear form

The genuinely multivariate (but fixed-size) algebra: the square of
`c₀ + c₁·U + c₂·V` is the six-term `qform 1 U² V² U V (U·V)`.  Proved once
as a raw `Q'` identity, then lifted to the three SOS linear forms by
specialization. -/

/-- Congruence for `*` on both `Q'` arguments. -/
theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- `a + a ≃ (2:Q')·a` (replicating the substrate-free `Pivot2` proof). -/
theorem add_self_two (a : Q') : ((a + a)).eqv (2 * a) := by
  show ((a + a)).num * ((2 * a).den : Int) = ((2 * a)).num * ((a + a).den : Int)
  have hnum2 : ((2 : Q') * a).num = 2 * a.num := rfl
  have hnumaa : ((a + a)).num = a.num * (a.den : Int) + a.num * (a.den : Int) := rfl
  have hden2a : (((2 : Q') * a).den : Int) = a.den := by
    rw [Q'.mul_den_cast (2 : Q') a]
    show ((1 : Int)) * (a.den : Int) = (a.den : Int)
    rw [Int.one_mul]
  rw [hnum2, hnumaa, hden2a, Q'.add_den_cast a a]
  calc (a.num * (a.den : Int) + a.num * (a.den : Int)) * (a.den : Int)
      = (2 * (a.num * (a.den : Int))) * (a.den : Int) := by rw [← Int.two_mul]
    _ = 2 * a.num * ((a.den : Int) * (a.den : Int)) := by
        rw [Int.mul_assoc 2 (a.num * (a.den : Int)) (a.den : Int),
            Int.mul_assoc a.num (a.den : Int) (a.den : Int),
            Int.mul_assoc 2 a.num ((a.den : Int) * (a.den : Int))]

/-- `(2:Q')·a ≃ a + a`. -/
theorem two_mul_eqv (a : Q') : ((2 : Q') * a).eqv (a + a) := (add_self_two a).symm

/-- `(c1·U)·(c1·U) ≃ (c1·c1)·(U·U)`. -/
theorem prodsq (c U : Q') : ((c * U) * (c * U)).eqv ((c * c) * (U * U)) := by
  -- (cU)(cU) ≃ c(U(cU)) ≃ c((Uc)U) ≃ c((cU)U) ≃ c(c(UU)) ≃ (cc)(UU)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c U (c * U)) ?_
  have inner : (U * (c * U)).eqv (c * (U * U)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv U c U)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (U * c) (c * U) U (Q'.mul_comm_eqv U c)) ?_
    exact Q'.mul_assoc_eqv c U U
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ inner)
    (Q'.eqv_symm (Q'.mul_assoc_eqv c c (U * U)))

/-- `c0·(c1·U) ≃ (c0·c1)·U`. -/
theorem cross_assoc (c0 c1 U : Q') : (c0 * (c1 * U)).eqv ((c0 * c1) * U) :=
  (Q'.mul_assoc_eqv c0 c1 U).symm

/-- `(c1·U)·c0 ≃ (c0·c1)·U`. -/
theorem cross_assoc' (c0 c1 U : Q') : ((c1 * U) * c0).eqv ((c0 * c1) * U) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (c1 * U) c0) (cross_assoc c0 c1 U)

/-- The mixed cross term: `c0·(c1·U) + (c1·U)·c0 ≃ (2·(c0·c1))·U`. -/
theorem cross_pair (c0 c1 U : Q') :
    (c0 * (c1 * U) + (c1 * U) * c0).eqv ((2 * (c0 * c1)) * U) := by
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr (cross_assoc c0 c1 U) (cross_assoc' c0 c1 U)) ?_
  -- (c0c1)U + (c0c1)U ≃ ((c0c1)+(c0c1))U ≃ (2(c0c1))U
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_add_mul (c0 * c1) (c0 * c1) U)) ?_
  exact Q'.mul_eqv_congr_right _ _ U (add_self_two (c0 * c1))

/-- The mixed cross term for `(c1U)(c2V)`: `(c1·U)·(c2·V) + (c2·V)·(c1·U)
≃ (2·(c1·c2))·(U·V)`. -/
theorem cross_pair2 (c1 c2 U V : Q') :
    ((c1 * U) * (c2 * V) + (c2 * V) * (c1 * U)).eqv ((2 * (c1 * c2)) * (U * V)) := by
  have hbase : ((c1 * U) * (c2 * V)).eqv ((c1 * c2) * (U * V)) := by
    -- (c1U)(c2V) ≃ c1(U(c2V)) ≃ c1((c2)(UV))? do step by step
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c1 U (c2 * V)) ?_
    have inner : (U * (c2 * V)).eqv (c2 * (U * V)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv U c2 V)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (U * c2) (c2 * U) V (Q'.mul_comm_eqv U c2)) ?_
      exact Q'.mul_assoc_eqv c2 U V
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c1 _ _ inner) ?_
    exact (Q'.mul_assoc_eqv c1 c2 (U * V)).symm
  have hbase' : ((c2 * V) * (c1 * U)).eqv ((c1 * c2) * (U * V)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (c2 * V) (c1 * U)) hbase
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr hbase hbase') ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_add_mul (c1 * c2) (c1 * c2) (U * V))) ?_
  exact Q'.mul_eqv_congr_right _ _ (U * V) (add_self_two (c1 * c2))

/-- `c0·c0 ≃ (c0·c0)·1`. -/
theorem mul_one_symm (a : Q') : a.eqv (a * Q'.ofNat 1) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv a))
    (Q'.mul_eqv_congr_left a 1 (Q'.ofNat 1) (by decide))

/-! ### Additive nine-atom collection

We collect the nine product atoms of the expanded square into the canonical
six-term `qform` shape purely by `+`-associativity/commutativity congruence and
the three cross-pair merges.  To keep the rearrangement honest and short we
route everything through one **abelian-monoid normaliser on a fixed list of
atoms** (`addNF`), the only place a long additive computation occurs. -/

/-- Right-nested sum of a list of `Q'` atoms. -/
def addNF : List Q' → Q'
  | [] => 0
  | (a :: as) => a + addNF as

/-- `addNF (as ++ bs) ≃ addNF as + addNF bs`. -/
theorem addNF_append : ∀ (as bs : List Q'),
    (addNF (as ++ bs)).eqv (addNF as + addNF bs)
  | [], bs => Q'.eqv_symm (QPoly.q_zero_add_eqv (addNF bs))
  | (a :: as), bs => by
      show (a + addNF (as ++ bs)).eqv ((a + addNF as) + addNF bs)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (addNF_append as bs)) ?_
      exact (Q'.add_assoc_eqv a (addNF as) (addNF bs)).symm

/-- Adjacent-swap inside `addNF`: `addNF (a :: b :: as) ≃ addNF (b :: a :: as)`. -/
theorem addNF_swap (a b : Q') (as : List Q') :
    (addNF (a :: b :: as)).eqv (addNF (b :: a :: as)) := by
  show (a + (b + addNF as)).eqv (b + (a + addNF as))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (addNF as)).symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv a b)) ?_
  exact Q'.add_assoc_eqv b a (addNF as)

/-- **`addNF` is permutation-invariant** (abelian-monoid sum).  Proved by
recursion on `List.Perm`: the four constructors map to reflexivity, tail
congruence, the adjacent swap, and transitivity. -/
theorem addNF_perm : ∀ {as bs : List Q'}, as.Perm bs → (addNF as).eqv (addNF bs)
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons a h => Q'.add_eqv_congr_left a _ _ (addNF_perm h)
  | _, _, List.Perm.swap a b l => by
      -- bs has head b::a::l, as has a::b::l ; addNF_swap gives the swap
      exact addNF_swap b a l
  | _, _, List.Perm.trans h1 h2 => Q'.eqv_trans _ _ _ (addNF_perm h1) (addNF_perm h2)

/-- `addNF`-congruence: replace the head atom by an `.eqv` one. -/
theorem addNF_head (a a' : Q') (as : List Q') (h : a.eqv a') :
    (addNF (a :: as)).eqv (addNF (a' :: as)) :=
  Q'.add_eqv_congr_right a a' (addNF as) h

/-- `addNF`-congruence: replace the tail. -/
theorem addNF_tail (a : Q') (as bs : List Q') (h : (addNF as).eqv (addNF bs)) :
    (addNF (a :: as)).eqv (addNF (a :: bs)) :=
  Q'.add_eqv_congr_left a (addNF as) (addNF bs) h

/-- `(a+b)+c ≃ addNF [a,b,c]`. -/
theorem tri_addNF (a b c : Q') : ((a + b) + c).eqv (addNF [a, b, c]) := by
  show ((a + b) + c).eqv (a + (b + (c + 0)))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b c) ?_
  exact Q'.add_eqv_congr_left a (b + c) (b + (c + 0))
    (Q'.add_eqv_congr_left b c (c + 0) (QPoly.q_add_zero_eqv c).symm)

/-- Merge the first two atoms: `addNF (a :: b :: as) ≃ (a + b) + addNF as`,
i.e. fold the head pair. -/
theorem addNF_fold2 (a b : Q') (as : List Q') :
    (addNF (a :: b :: as)).eqv ((a + b) + addNF as) := by
  show (a + (b + addNF as)).eqv ((a + b) + addNF as)
  exact (Q'.add_assoc_eqv a b (addNF as)).symm

/-- Move the head atom to the 3rd position: `a::b::c::r ≃ b::c::a::r`
(two adjacent swaps). -/
theorem addNF_rot3 (a b c : Q') (r : List Q') :
    (addNF (a :: b :: c :: r)).eqv (addNF (b :: c :: a :: r)) :=
  Q'.eqv_trans _ _ _ (addNF_swap a b (c :: r))
    (addNF_tail b _ _ (addNF_swap a c r))

/-- `addNF [a,b] ≃ a + b`. -/
theorem addNF_pair (a b : Q') : (addNF [a, b]).eqv (a + b) := by
  show (a + (b + 0)).eqv (a + b)
  exact Q'.add_eqv_congr_left a (b + 0) b (QPoly.q_add_zero_eqv b)

/-- `addNF [a,b,c] ≃ a + (b + c)`. -/
theorem addNF_triR (a b c : Q') : (addNF [a, b, c]).eqv (a + (b + c)) := by
  show (a + (b + (c + 0))).eqv (a + (b + c))
  exact Q'.add_eqv_congr_left a _ _ (Q'.add_eqv_congr_left b (c + 0) c (QPoly.q_add_zero_eqv c))

/-- Fold the nine-atom diagonals-then-pairs list into a six-term tree:
`addNF [d0,d1,d2,p,p',q,q',r,r'] ≃ d0+(d1+(d2+((p+p')+((q+q')+(r+r')))))`. -/
theorem addNF_fold_pairs (d0 d1 d2 p p' q q' r r' : Q') :
    (addNF [d0,d1,d2,p,p',q,q',r,r']).eqv
      (d0 + (d1 + (d2 + ((p + p') + ((q + q') + (r + r')))))) := by
  -- split [d0,d1,d2] ++ [p,p',q,q',r,r']
  refine Q'.eqv_trans _ _ _
    (addNF_append [d0,d1,d2] [p,p',q,q',r,r']) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (addNF_triR d0 d1 d2)
      (Q'.eqv_trans _ _ _ (addNF_append [p,p'] [q,q',r,r'])
        (QPoly.q_add_congr (addNF_pair p p')
          (Q'.eqv_trans _ _ _ (addNF_append [q,q'] [r,r'])
            (QPoly.q_add_congr (addNF_pair q q') (addNF_pair r r')))))) ?_
  -- (d0+(d1+d2)) + ((p+p') + ((q+q')+(r+r'))) ≃ d0+(d1+(d2+((p+p')+((q+q')+(r+r')))))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv d0 (d1 + d2) _) ?_
  exact Q'.add_eqv_congr_left d0 _ _ (Q'.add_assoc_eqv d1 d2 _)

/-- The 9-atom reordering (E-order → diagonals-then-pairs) over abstract atoms,
built from 14 adjacent swaps.  The target list is
`[a0,a4,a8, a3,a1, a6,a2, a7,a5]`. -/
theorem addNF_reorder (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Q') :
    (addNF [a0,a1,a2,a3,a4,a5,a6,a7,a8]).eqv
      (addNF [a0,a4,a8,a3,a1,a6,a2,a7,a5]) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ (addNF_tail a0 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_swap a3 a4 [a5, a6, a7, a8])))) (addNF_tail a0 _ _ (addNF_tail a1 _ _ (addNF_swap a2 a4 [a3, a5, a6, a7, a8])))) (addNF_tail a0 _ _ (addNF_swap a1 a4 [a2, a3, a5, a6, a7, a8]))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_tail a3 _ _ (addNF_tail a5 _ _ (addNF_tail a6 _ _ (addNF_swap a7 a8 []))))))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_tail a3 _ _ (addNF_tail a5 _ _ (addNF_swap a6 a8 [a7])))))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_tail a3 _ _ (addNF_swap a5 a8 [a6, a7]))))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_swap a3 a8 [a5, a6, a7])))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a1 _ _ (addNF_swap a2 a8 [a3, a5, a6, a7]))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_swap a1 a8 [a2, a3, a5, a6, a7])))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a8 _ _ (addNF_tail a1 _ _ (addNF_swap a2 a3 [a5, a6, a7])))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a8 _ _ (addNF_swap a1 a3 [a2, a5, a6, a7]))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a8 _ _ (addNF_tail a3 _ _ (addNF_tail a1 _ _ (addNF_tail a2 _ _ (addNF_swap a5 a6 [a7])))))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a8 _ _ (addNF_tail a3 _ _ (addNF_tail a1 _ _ (addNF_swap a2 a6 [a5, a7]))))))) (addNF_tail a0 _ _ (addNF_tail a4 _ _ (addNF_tail a8 _ _ (addNF_tail a3 _ _ (addNF_tail a1 _ _ (addNF_tail a6 _ _ (addNF_tail a2 _ _ (addNF_swap a5 a7 []))))))))

/-- Re-associate the right-nested six-term sum to the `qform` target tree:
`d0+(d1+(d2+(x+(y+z)))) ≃ ((d0+d1)+(d2+x))+(y+z)`. -/
theorem reassoc_to_T (d0 d1 d2 x y z : Q') :
    (d0 + (d1 + (d2 + (x + (y + z))))).eqv
      (((d0 + d1) + (d2 + x)) + (y + z)) := by
  -- d0+(d1+(d2+(x+(y+z)))) ≃ d0+(d1+((d2+x)+(y+z)))      [assoc inside]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left d0 _ _
      (Q'.add_eqv_congr_left d1 _ _ (Q'.add_assoc_eqv d2 x (y + z)).symm)) ?_
  -- d0+(d1+((d2+x)+(y+z))) ≃ d0+((d1+(d2+x))+(y+z))       [assoc]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left d0 _ _ (Q'.add_assoc_eqv d1 (d2 + x) (y + z)).symm) ?_
  -- d0+((d1+(d2+x))+(y+z)) ≃ (d0+(d1+(d2+x)))+(y+z)        [assoc]
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv d0 (d1 + (d2 + x)) (y + z)).symm ?_
  -- (d0+(d1+(d2+x)))+(y+z) ≃ ((d0+d1)+(d2+x))+(y+z)        [assoc on left]
  exact Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv d0 d1 (d2 + x)).symm

/-- **Collect the nine-atom expansion (in `addNF` E-order) into the canonical
six-term `qform` shape.**  Permute to diagonals-then-pairs, fold the three
adjacent cross pairs, normalise the diagonals and merge the pairs, then
re-associate to the target tree. -/
theorem sq3_collect (c0 c1 c2 U V : Q') :
    (addNF [c0*c0, (c1*U)*c0, (c2*V)*c0, c0*(c1*U), (c1*U)*(c1*U), (c2*V)*(c1*U),
            c0*(c2*V), (c1*U)*(c2*V), (c2*V)*(c2*V)]).eqv
      ((((c0 * c0) * Q'.ofNat 1 + (c1 * c1) * (U * U))
          + ((c2 * c2) * (V * V) + (2 * (c0 * c1)) * U))
        + ((2 * (c0 * c2)) * V + (2 * (c1 * c2)) * (U * V))) := by
  -- Permute to Lp = [c0c0, (c1U)(c1U), (c2V)(c2V), c0(c1U),(c1U)c0, c0(c2V),(c2V)c0,
  --                  (c1U)(c2V),(c2V)(c1U)]  (diagonals, then the three adjacent pairs).
  refine Q'.eqv_trans _ _ _
    (addNF_reorder (c0*c0) ((c1*U)*c0) ((c2*V)*c0) (c0*(c1*U)) ((c1*U)*(c1*U))
      ((c2*V)*(c1*U)) (c0*(c2*V)) ((c1*U)*(c2*V)) ((c2*V)*(c2*V))) ?_
  -- Fold the three trailing pairs.
  refine Q'.eqv_trans _ _ _
    (addNF_fold_pairs (c0*c0) ((c1*U)*(c1*U)) ((c2*V)*(c2*V))
      (c0*(c1*U)) ((c1*U)*c0) (c0*(c2*V)) ((c2*V)*c0)
      ((c1*U)*(c2*V)) ((c2*V)*(c1*U))) ?_
  -- Now: d0 + (d1 + (d2 + (x01 + (x02 + x12)))) with
  --   d0=c0c0, d1=(c1U)(c1U), d2=(c2V)(c2V),
  --   x01=c0(c1U)+(c1U)c0, x02=c0(c2V)+(c2V)c0, x12=(c1U)(c2V)+(c2V)(c1U).
  -- Normalise all six atoms in place (right-nested tree preserved).
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (mul_one_symm (c0*c0))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((c0*c0) * Q'.ofNat 1) _ _
      (Q'.add_eqv_congr_right _ _ _ (prodsq c1 U))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((c0*c0) * Q'.ofNat 1) _ _
      (Q'.add_eqv_congr_left ((c1*c1)*(U*U)) _ _
        (Q'.add_eqv_congr_right _ _ _ (prodsq c2 V)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((c0*c0) * Q'.ofNat 1) _ _
      (Q'.add_eqv_congr_left ((c1*c1)*(U*U)) _ _
        (Q'.add_eqv_congr_left ((c2*c2)*(V*V)) _ _
          (QPoly.q_add_congr (cross_pair c0 c1 U)
            (QPoly.q_add_congr (cross_pair c0 c2 V) (cross_pair2 c1 c2 U V)))))) ?_
  -- Now have d0'+(d1'+(d2'+(x01'+(x02'+x12')))).  Re-associate to T's tree
  --   ((d0'+d1')+(d2'+x01')) + (x02'+x12').
  exact reassoc_to_T ((c0*c0) * Q'.ofNat 1) ((c1*c1)*(U*U)) ((c2*c2)*(V*V))
    ((2*(c0*c1))*U) ((2*(c0*c2))*V) ((2*(c1*c2))*(U*V))

/-- **Raw three-term square** collected into the six-term `qform` shape.
`((c₀ + c₁·U) + c₂·V)² ≃ ((c₀c₀·1 + c₁c₁·U²) + (c₂c₂·V² + 2c₀c₁·U))
+ (2c₀c₂·V + 2c₁c₂·(U·V))`. -/
theorem sq3_raw (c0 c1 c2 U V : Q') :
    (((c0 + c1 * U) + c2 * V) * ((c0 + c1 * U) + c2 * V)).eqv
      ((((c0 * c0) * Q'.ofNat 1 + (c1 * c1) * (U * U))
          + ((c2 * c2) * (V * V) + (2 * (c0 * c1)) * U))
        + ((2 * (c0 * c2)) * V + (2 * (c1 * c2)) * (U * V))) := by
  -- Step 1: full distribution of s*s into the nine-atom tree.
  have e_c0 : ((((c0 + c1*U) + c2*V)) * c0).eqv
      ((c0 * c0 + (c1*U) * c0) + (c2*V) * c0) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_mul ((c0 + c1*U)) (c2*V) c0)
      (Q'.add_eqv_congr_right _ _ _ (QPoly.q_add_mul c0 (c1*U) c0))
  have e_b : ((((c0 + c1*U) + c2*V)) * (c1*U)).eqv
      ((c0 * (c1*U) + (c1*U) * (c1*U)) + (c2*V) * (c1*U)) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_mul ((c0 + c1*U)) (c2*V) (c1*U))
      (Q'.add_eqv_congr_right _ _ _ (QPoly.q_add_mul c0 (c1*U) (c1*U)))
  have e_cc : ((((c0 + c1*U) + c2*V)) * (c2*V)).eqv
      ((c0 * (c2*V) + (c1*U) * (c2*V)) + (c2*V) * (c2*V)) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_mul ((c0 + c1*U)) (c2*V) (c2*V))
      (Q'.add_eqv_congr_right _ _ _ (QPoly.q_add_mul c0 (c1*U) (c2*V)))
  have hExpand : (((c0 + c1 * U) + c2 * V) * ((c0 + c1 * U) + c2 * V)).eqv
      (((c0 * c0 + (c1*U) * c0) + (c2*V) * c0)
        + (((c0 * (c1*U) + (c1*U) * (c1*U)) + (c2*V) * (c1*U))
          + ((c0 * (c2*V) + (c1*U) * (c2*V)) + (c2*V) * (c2*V)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (((c0 + c1*U) + c2*V)) (c0 + c1*U) (c2*V)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv (((c0 + c1*U) + c2*V)) c0 (c1*U))) ?_
    -- ( s*c0 + s*(c1U) ) + s*(c2V)  →  expand each, and re-associate to right-nest
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr (QPoly.q_add_congr e_c0 e_b) e_cc) ?_
    exact Q'.add_assoc_eqv _ _ _
  -- Step 2: flatten the nine-atom tree to `addNF` (E-order), then collect into T.
  refine Q'.eqv_trans _ _ _ hExpand (Q'.eqv_trans _ _ _ ?_ (sq3_collect c0 c1 c2 U V))
  -- flatten E-tree → addNF L9
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (tri_addNF (c0*c0) ((c1*U)*c0) ((c2*V)*c0)))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (addNF [c0*c0, (c1*U)*c0, (c2*V)*c0]) _ _
        (Q'.eqv_trans _ _ _
          (QPoly.q_add_congr
            (tri_addNF (c0*(c1*U)) ((c1*U)*(c1*U)) ((c2*V)*(c1*U)))
            (tri_addNF (c0*(c2*V)) ((c1*U)*(c2*V)) ((c2*V)*(c2*V))))
          (addNF_append [c0*(c1*U), (c1*U)*(c1*U), (c2*V)*(c1*U)]
            [c0*(c2*V), (c1*U)*(c2*V), (c2*V)*(c2*V)]).symm))
      (addNF_append [c0*c0, (c1*U)*c0, (c2*V)*c0]
        ([c0*(c1*U), (c1*U)*(c1*U), (c2*V)*(c1*U)]
          ++ [c0*(c2*V), (c1*U)*(c2*V), (c2*V)*(c2*V)])).symm)

/-! ## CReal linear forms and their squares as `qform`s -/

/-- `lin3 U V c₀ c₁ c₂ = c₀ + c₁·U + c₂·V` as a `CReal`. -/
def lin3 (U V : CReal) (c0 c1 c2 : Q') : CReal :=
  CReal.add (CReal.add (CReal.ofQ' c0) (CReal.mul (CReal.ofQ' c1) U))
            (CReal.mul (CReal.ofQ' c2) V)

/-- `x·0 ≃ 0`, `0·x ≃ 0`, and `a + 0 ≃ a` glue lemmas used to kill the
vanishing `qform` entries of the two- and one-term forms. -/
theorem mul_zero_q (a : Q') : (a * 0).eqv 0 := QPoly.q_mul_zero a

/-- **Raw two-term square** in the `qform 0 α² β² 0 0 (αβ)` shape (constant slot
absent).  `(c₁·α + c₂·β)² ≃ ((c₀c₀·0 + c₁c₁·α²) + (c₂c₂·β² + 2c₀c₁·0))
+ (2c₀c₂·0 + 2c₁c₂·(α·β))`. -/
theorem sq2_raw (c0 c1 c2 al be : Q') :
    ((c1 * al + c2 * be) * (c1 * al + c2 * be)).eqv
      ((((c0 * c0) * 0 + (c1 * c1) * (al * al))
          + ((c2 * c2) * (be * be) + (2 * (c0 * c1)) * 0))
        + ((2 * (c0 * c2)) * 0 + (2 * (c1 * c2)) * (al * be))) := by
  -- Start from sq3_raw with constant slot 0: ((0 + c1·al) + c2·be)².
  have h0 : (((0 + c1 * al) + c2 * be) * ((0 + c1 * al) + c2 * be)).eqv
      ((((0 * 0) * Q'.ofNat 1 + (c1 * c1) * (al * al))
          + ((c2 * c2) * (be * be) + (2 * (0 * c1)) * al))
        + ((2 * (0 * c2)) * be + (2 * (c1 * c2)) * (al * be))) :=
    sq3_raw 0 c1 c2 al be
  -- LHS: (0 + c1al) ≃ c1al, so the whole square reduces.
  have hlhs : (((0 + c1 * al) + c2 * be) * ((0 + c1 * al) + c2 * be)).eqv
      ((c1 * al + c2 * be) * (c1 * al + c2 * be)) := by
    have hin : ((0 + c1 * al) + c2 * be).eqv (c1 * al + c2 * be) :=
      Q'.add_eqv_congr_right _ _ _ (QPoly.q_zero_add_eqv (c1 * al))
    exact q_mul_congr hin hin
  refine Q'.eqv_trans _ _ _ hlhs.symm (Q'.eqv_trans _ _ _ h0 ?_)
  -- RHS of h0 → RHS target: rewrite the vanishing atoms.
  -- (0*0)*1 ≃ (c0c0)*0   [both ≃ 0];  (2*(0c1))*al ≃ (2(c0c1))*0  [both ≃0];
  -- (2*(0c2))*be ≃ (2(c0c2))*0  [both ≃ 0].
  have z1 : ((0 * 0 : Q') * Q'.ofNat 1).eqv ((c0 * c0) * 0) := by
    -- (0*0)*1 ≃ 0*1 ≃ 0 ;  (c0c0)*0 ≃ 0
    refine Q'.eqv_trans _ _ _ ?_ (mul_zero_q (c0 * c0)).symm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (0 * 0) 0 (Q'.ofNat 1) (QPoly.q_mul_zero 0)) ?_
    exact QPoly.q_zero_mul (Q'.ofNat 1)
  have z2 : ((2 * (0 * c1) : Q') * al).eqv ((2 * (c0 * c1)) * 0) := by
    refine Q'.eqv_trans _ _ _ ?_ (mul_zero_q (2 * (c0 * c1))).symm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (2 * (0 * c1)) 0 al ?_) (QPoly.q_zero_mul al)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 (0 * c1) 0 (QPoly.q_zero_mul c1))
      (QPoly.q_mul_zero 2)
  have z3 : ((2 * (0 * c2) : Q') * be).eqv ((2 * (c0 * c2)) * 0) := by
    refine Q'.eqv_trans _ _ _ ?_ (mul_zero_q (2 * (c0 * c2))).symm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (2 * (0 * c2)) 0 be ?_) (QPoly.q_zero_mul be)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 (0 * c2) 0 (QPoly.q_zero_mul c2))
      (QPoly.q_mul_zero 2)
  exact QPoly.q_add_congr
    (QPoly.q_add_congr (Q'.add_eqv_congr_right _ _ _ z1)
      (Q'.add_eqv_congr_left _ _ _ z2))
    (Q'.add_eqv_congr_right _ _ _ z3)

/-- **Square of `lin3` is the six-term `qform`** with entries
`1, U², V², U, V, U·V`.  Lifts `sq3_raw` pointwise. -/
theorem lin3_sq (U V : CReal) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (lin3 U V c0 c1 c2) (lin3 U V c0 c1 c2))
      (qform (C 1) (CReal.mul U U) (CReal.mul V V) U V (CReal.mul U V) c0 c1 c2) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    -- pointwise: ((c0 + c1*U_n) + c2*V_n)² ≃ qform-entries form.
    show (((c0 + c1 * U.approx n) + c2 * V.approx n)
            * ((c0 + c1 * U.approx n) + c2 * V.approx n)).eqv
      ((((c0 * c0) * (Q'.ofNat 1) + (c1 * c1) * (U.approx n * U.approx n))
          + ((c2 * c2) * (V.approx n * V.approx n) + (2 * (c0 * c1)) * U.approx n))
        + ((2 * (c0 * c2)) * V.approx n + (2 * (c1 * c2)) * (U.approx n * V.approx n)))
    exact sq3_raw c0 c1 c2 (U.approx n) (V.approx n))

/-- `lin2 α β c₁ c₂ = c₁·α + c₂·β` (no constant term). -/
def lin2 (al be : CReal) (c1 c2 : Q') : CReal :=
  CReal.add (CReal.mul (CReal.ofQ' c1) al) (CReal.mul (CReal.ofQ' c2) be)

/-- **Square of `lin2`** is `qform 0 α² β² 0 0 (α·β)`. -/
theorem lin2_sq (al be : CReal) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (lin2 al be c1 c2) (lin2 al be c1 c2))
      (qform (C 0) (CReal.mul al al) (CReal.mul be be) (C 0) (C 0) (CReal.mul al be)
        c0 c1 c2) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show ((c1 * al.approx n + c2 * be.approx n)
            * (c1 * al.approx n + c2 * be.approx n)).eqv
      ((((c0 * c0) * 0 + (c1 * c1) * (al.approx n * al.approx n))
          + ((c2 * c2) * (be.approx n * be.approx n) + (2 * (c0 * c1)) * 0))
        + ((2 * (c0 * c2)) * 0 + (2 * (c1 * c2)) * (al.approx n * be.approx n)))
    exact sq2_raw c0 c1 c2 (al.approx n) (be.approx n))

/-- **Square of a one-term form** `c₂·γ` is `qform 0 0 γ² 0 0 0`. -/
theorem lin1_sq (ga : CReal) (c0 c1 c2 : Q') :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' c2) ga) (CReal.mul (CReal.ofQ' c2) ga))
      (qform (C 0) (C 0) (CReal.mul ga ga) (C 0) (C 0) (C 0) c0 c1 c2) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show ((c2 * ga.approx n) * (c2 * ga.approx n)).eqv
      ((((c0 * c0) * 0 + (c1 * c1) * 0)
          + ((c2 * c2) * (ga.approx n * ga.approx n) + (2 * (c0 * c1)) * 0))
        + ((2 * (c0 * c2)) * 0 + (2 * (c1 * c2)) * 0))
    -- (c2·γ)(c2·γ) ≃ (c2c2)(γγ); all other atoms ≃ 0.
    have hmain : ((c2 * ga.approx n) * (c2 * ga.approx n)).eqv
        ((c2 * c2) * (ga.approx n * ga.approx n)) := prodsq c2 (ga.approx n)
    refine Q'.eqv_trans _ _ _ hmain ?_
    -- (c2c2)(γγ) ≃ target.  Build target backwards: all the `·0` atoms are 0.
    refine Q'.eqv_symm ?_
    -- target ≃ (c2c2)(γγ)
    have e00 : ((c0 * c0) * (0:Q')).eqv 0 := mul_zero_q (c0 * c0)
    have e11 : ((c1 * c1) * (0:Q')).eqv 0 := mul_zero_q (c1 * c1)
    have e01 : ((2 * (c0 * c1)) * (0:Q')).eqv 0 := mul_zero_q (2 * (c0 * c1))
    have e02 : ((2 * (c0 * c2)) * (0:Q')).eqv 0 := mul_zero_q (2 * (c0 * c2))
    have e12 : ((2 * (c1 * c2)) * (0:Q')).eqv 0 := mul_zero_q (2 * (c1 * c2))
    -- (((0+0)+((c2c2)(γγ)+0))+(0+0)) ≃ (c2c2)(γγ)
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr
        (QPoly.q_add_congr (QPoly.q_add_congr e00 e11)
          (Q'.add_eqv_congr_left _ _ 0 e01))
        (QPoly.q_add_congr e02 e12)) ?_
    -- ((0+0)+((c2c2)(γγ)+0))+(0+0)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _ (QPoly.q_zero_add_eqv 0))) ?_
    -- (0 + ((c2c2)(γγ)+0)) + (0+0)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (QPoly.q_zero_add_eqv ((c2*c2)*(ga.approx n * ga.approx n) + 0))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (QPoly.q_add_zero_eqv _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 (QPoly.q_zero_add_eqv 0)) ?_
    exact QPoly.q_add_zero_eqv _)

/-! ## Reflective base-polynomials `evalC`

`evalC t p` is the Horner evaluation of the coefficient list `p` at the base
`a = base t ht`, as a `CReal`.  Its `n`-th approximation is *definitionally*
`QPoly.eval p (a.approx n)`, so a `CReal`-`Equiv` between two `evalC`s reduces
(via `Equiv_of_approx_eqv`) to a `QPoly.poly_eqv` `decide`. -/

/-- Horner evaluation of a `Q'` coefficient list at the base `a`, as a `CReal`. -/
def evalC (t : Q') (ht : (0 : Q') ≤ t) : QPoly.Poly → CReal
  | [] => C 0
  | (c :: cs) => CReal.add (CReal.ofQ' c) (CReal.mul (base t ht) (evalC t ht cs))

/-- `(evalC t p).approx n = QPoly.eval p (a.approx n)` — definitional. -/
theorem evalC_approx (t : Q') (ht : (0 : Q') ≤ t) :
    ∀ (p : QPoly.Poly) (n : Nat),
      (evalC t ht p).approx n = QPoly.eval p ((base t ht).approx n)
  | [], _ => rfl
  | (c :: cs), n => by
      show c + (base t ht).approx n * (evalC t ht cs).approx n
        = c + (base t ht).approx n * QPoly.eval cs ((base t ht).approx n)
      rw [evalC_approx t ht cs n]

/-- **Two `evalC`s are `Equiv` when their coefficient lists are `QPoly`-equal.** -/
theorem evalC_eqv (t : Q') (ht : (0 : Q') ≤ t) (p q : QPoly.Poly)
    (h : QPoly.allZero (QPoly.psub p q)) :
    CReal.Equiv (evalC t ht p) (evalC t ht q) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht p n, evalC_approx t ht q n]
    exact QPoly.poly_eqv p q ((base t ht).approx n) h)

/-- `evalC p · evalC q ≃ evalC (pmul p q)` (the product ring-hom bridge). -/
theorem evalC_mul (t : Q') (ht : (0 : Q') ≤ t) (p q : QPoly.Poly) :
    CReal.Equiv (CReal.mul (evalC t ht p) (evalC t ht q)) (evalC t ht (QPoly.pmul p q)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht (QPoly.pmul p q) n]
    show ((evalC t ht p).approx n * (evalC t ht q).approx n).eqv _
    rw [evalC_approx t ht p n, evalC_approx t ht q n]
    exact (QPoly.eval_pmul p q ((base t ht).approx n)).symm)

/-- `evalC p + evalC q ≃ evalC (padd p q)` (the sum ring-hom bridge). -/
theorem evalC_add (t : Q') (ht : (0 : Q') ≤ t) (p q : QPoly.Poly) :
    CReal.Equiv (CReal.add (evalC t ht p) (evalC t ht q)) (evalC t ht (QPoly.padd p q)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht (QPoly.padd p q) n]
    show ((evalC t ht p).approx n + (evalC t ht q).approx n).eqv _
    rw [evalC_approx t ht p n, evalC_approx t ht q n]
    exact (QPoly.eval_padd p q ((base t ht).approx n)).symm)

/-- The pointwise nested power `(rawPowC x j).approx n` as a `Q'` function:
`rawPowQ q 0 = 1`, `rawPowQ q (j+1) = q · rawPowQ q j`. -/
def rawPowQ (q : Q') : Nat → Q'
  | 0 => Q'.ofNat 1
  | (j + 1) => q * rawPowQ q j

/-- `(rawPowC x j).approx n = rawPowQ (x.approx n) j` — definitional. -/
theorem rawPowC_approx (x : CReal) : ∀ (j : Nat) (n : Nat),
    (rawPowC x j).approx n = rawPowQ (x.approx n) j
  | 0, _ => rfl
  | (j + 1), n => by
      show x.approx n * (rawPowC x j).approx n = x.approx n * rawPowQ (x.approx n) j
      rw [rawPowC_approx x j n]

/-- The monomial coefficient list `x^j = [0,…,0,1]` (`j` zeros, then `1`). -/
def xmon (j : Nat) : QPoly.Poly := List.replicate j 0 ++ [1]

/-- `rawPowQ q j ≃ eval (xmon j) q` — the nested power reified to Horner. -/
theorem rawPow_eval (q : Q') : ∀ j,
    (rawPowQ q j).eqv (QPoly.eval (xmon j) q)
  | 0 => by
      show (Q'.ofNat 1).eqv (1 + q * 0)
      exact Q'.eqv_trans _ _ _ (by decide : (Q'.ofNat 1).eqv (1 : Q'))
        (QPoly.q_add_zero_eqv 1).symm |> fun h =>
        Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr_left 1 0 (q * 0) (QPoly.q_mul_zero q).symm)
  | (j + 1) => by
      show (q * rawPowQ q j).eqv (0 + q * QPoly.eval (xmon j) q)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ (rawPow_eval q j)) ?_
      exact (QPoly.q_zero_add_eqv (q * QPoly.eval (xmon j) q)).symm

/-- `rawPowC a j ≃ evalC (xmon j)`. -/
theorem rawPowC_evalC (t : Q') (ht : (0 : Q') ≤ t) (j : Nat) :
    CReal.Equiv (rawPowC (base t ht) j) (evalC t ht (xmon j)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht (xmon j) n, rawPowC_approx (base t ht) j n]
    exact rawPow_eval ((base t ht).approx n) j)

/-- `C c ≃ evalC [c]`. -/
theorem C_evalC (t : Q') (ht : (0 : Q') ≤ t) (c : Nat) :
    CReal.Equiv (C c) (evalC t ht [Q'.ofNat c]) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht [Q'.ofNat c] n]
    show (Q'.ofNat c).eqv (Q'.ofNat c + (base t ht).approx n * 0)
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv (Q'.ofNat c)).symm
      (Q'.add_eqv_congr_left (Q'.ofNat c) 0 _ (QPoly.q_mul_zero ((base t ht).approx n)).symm))

/-- `smul k (evalC p) ≃ evalC (pscale (ofNat k) p)`. -/
theorem smul_evalC (t : Q') (ht : (0 : Q') ≤ t) (k : Nat) (p : QPoly.Poly) :
    CReal.Equiv (smul k (evalC t ht p)) (evalC t ht (QPoly.pscale (Q'.ofNat k) p)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [evalC_approx t ht (QPoly.pscale (Q'.ofNat k) p) n]
    show ((C k).approx n * (evalC t ht p).approx n).eqv _
    rw [evalC_approx t ht p n]
    show ((Q'.ofNat k) * QPoly.eval p ((base t ht).approx n)).eqv _
    exact (QPoly.eval_pscale (Q'.ofNat k) p ((base t ht).approx n)).symm)

/-- A moment `m_k = (k+1)·a^{exp}` as `evalC` of the scaled monomial. -/
theorem moment_evalC (t : Q') (ht : (0 : Q') ≤ t) (k exp : Nat) :
    CReal.Equiv (smul k (rawPowC (base t ht) exp))
      (evalC t ht (QPoly.pscale (Q'.ofNat k) (xmon exp))) :=
  equiv_trans (mul_congr_right (A := C k) (rawPowC_evalC t ht exp))
    (smul_evalC t ht k (xmon exp))

/-! ## The Gram entries as `evalC` base-polynomials

Each entry is rewritten to `evalC` of an explicit coefficient list, so the
final identity match is a `QPoly` `decide`.  The coefficient lists encode
`m₁=2a³, m₂=3a⁸, m₃=4a¹⁵, m₄=5a²⁴`. -/

/-- `m₁ ≃ evalC [0,0,0,2]`. -/
theorem m1_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m1 t ht) (evalC t ht [0,0,0,Q'.ofNat 2]) :=
  equiv_trans (m1_base t ht)
    (equiv_trans (moment_evalC t ht 2 3)
      (evalC_eqv t ht _ [0,0,0,Q'.ofNat 2] (by decide)))

/-- `m₂ ≃ evalC [0,0,0,0,0,0,0,0,3]`. -/
theorem m2_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m2 t ht) (evalC t ht [0,0,0,0,0,0,0,0,Q'.ofNat 3]) :=
  equiv_trans (m2_base t ht)
    (equiv_trans (moment_evalC t ht 3 8)
      (evalC_eqv t ht _ [0,0,0,0,0,0,0,0,Q'.ofNat 3] (by decide)))

/-- `m₃ ≃ evalC [0,…,0,4]` (degree 15). -/
theorem m3_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m3 t ht)
      (evalC t ht [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 4]) :=
  equiv_trans (m3_base t ht)
    (equiv_trans (moment_evalC t ht 4 15)
      (evalC_eqv t ht _ [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 4] (by decide)))

/-- `m₄ ≃ evalC [0,…,0,5]` (degree 24). -/
theorem m4_evalC (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m4 t ht)
      (evalC t ht [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 5]) :=
  equiv_trans (m4_base t ht)
    (equiv_trans (moment_evalC t ht 5 24)
      (evalC_eqv t ht _ [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,Q'.ofNat 5]
        (by decide)))

end YMGap.Continuum.Pivot3

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot3.add_interchange
#print axioms YMGap.Continuum.Pivot3.add_self_two
#print axioms YMGap.Continuum.Pivot3.addNF_append
#print axioms YMGap.Continuum.Pivot3.addNF_fold_pairs
#print axioms YMGap.Continuum.Pivot3.addNF_fold2
#print axioms YMGap.Continuum.Pivot3.addNF_head
#print axioms YMGap.Continuum.Pivot3.addNF_pair
#print axioms YMGap.Continuum.Pivot3.addNF_perm
#print axioms YMGap.Continuum.Pivot3.addNF_reorder
#print axioms YMGap.Continuum.Pivot3.addNF_rot3
#print axioms YMGap.Continuum.Pivot3.addNF_swap
#print axioms YMGap.Continuum.Pivot3.addNF_tail
#print axioms YMGap.Continuum.Pivot3.addNF_triR
#print axioms YMGap.Continuum.Pivot3.C_evalC
#print axioms YMGap.Continuum.Pivot3.cross_assoc
#print axioms YMGap.Continuum.Pivot3.cross_assoc'
#print axioms YMGap.Continuum.Pivot3.cross_pair
#print axioms YMGap.Continuum.Pivot3.cross_pair2
#print axioms YMGap.Continuum.Pivot3.evalC_add
#print axioms YMGap.Continuum.Pivot3.evalC_approx
#print axioms YMGap.Continuum.Pivot3.evalC_eqv
#print axioms YMGap.Continuum.Pivot3.evalC_mul
#print axioms YMGap.Continuum.Pivot3.form3_eq_qform
#print axioms YMGap.Continuum.Pivot3.lin1_sq
#print axioms YMGap.Continuum.Pivot3.lin2_sq
#print axioms YMGap.Continuum.Pivot3.lin3_sq
#print axioms YMGap.Continuum.Pivot3.m1_base
#print axioms YMGap.Continuum.Pivot3.m1_evalC
#print axioms YMGap.Continuum.Pivot3.m2_base
#print axioms YMGap.Continuum.Pivot3.m2_evalC
#print axioms YMGap.Continuum.Pivot3.m3_base
#print axioms YMGap.Continuum.Pivot3.m3_evalC
#print axioms YMGap.Continuum.Pivot3.m4_base
#print axioms YMGap.Continuum.Pivot3.m4_evalC
#print axioms YMGap.Continuum.Pivot3.moment_evalC
#print axioms YMGap.Continuum.Pivot3.mul_add_equiv
#print axioms YMGap.Continuum.Pivot3.mul_assoc_equiv
#print axioms YMGap.Continuum.Pivot3.mul_C0_eqv
#print axioms YMGap.Continuum.Pivot3.mul_ofQ'_swap
#print axioms YMGap.Continuum.Pivot3.mul_one_symm
#print axioms YMGap.Continuum.Pivot3.mul_zero_q
#print axioms YMGap.Continuum.Pivot3.ofQ'_mul_add
#print axioms YMGap.Continuum.Pivot3.prodsq
#print axioms YMGap.Continuum.Pivot3.q_mul_congr
#print axioms YMGap.Continuum.Pivot3.qform_add
#print axioms YMGap.Continuum.Pivot3.qform_congr
#print axioms YMGap.Continuum.Pivot3.qform_scale
#print axioms YMGap.Continuum.Pivot3.rawPow_eval
#print axioms YMGap.Continuum.Pivot3.rawPowC_approx
#print axioms YMGap.Continuum.Pivot3.rawPowC_evalC
#print axioms YMGap.Continuum.Pivot3.reassoc_to_T
#print axioms YMGap.Continuum.Pivot3.smul_evalC
#print axioms YMGap.Continuum.Pivot3.sq2_raw
#print axioms YMGap.Continuum.Pivot3.sq3_collect
#print axioms YMGap.Continuum.Pivot3.sq3_raw
#print axioms YMGap.Continuum.Pivot3.tri_addNF
#print axioms YMGap.Continuum.Pivot3.two_mul_eqv
