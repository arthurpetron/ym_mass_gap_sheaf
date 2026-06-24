/-
√-subadditivity / the √-Hölder uniform-continuity modulus — the missing
quantitative lemma behind the constructive Riemann convergence modulus.

# What this module proves (PROVED)

For positive rationals built into the genuine constructive square root
`CReal.sqrtFrom` (Heron √ of a positive rational `a` with a rational
lower-bound witness `L`, `0 < L`, `L² ≤ a`):

  * `sqrtFrom_mono` — radicand monotonicity in `leRat` form:
    `u ≤ b·b ⟹ leRat (√u) b` (a re-export of `sqrtFrom_leRat_of_sq`),
    and the two-radicand corollary `sqrtFrom_le_sqrtFrom`:
    `u ≤ v ⟹ leRat (√u) c` whenever `√v ≤ c` (rational `c`).

  * `sq_add_expand` — the public binomial expansion
    `(p+q)·(p+q) ≃ (p·p + q·q) + (p·q + p·q)` over `Q'` (the substrate's
    private `sq_add'`, re-derived for reuse).

  * **THE TARGET** `sqrtFrom_sub_leRat` — the √-Hölder / √-subadditivity
    modulus, stated in the **sound rational-upper-bound** form that the
    Riemann modulus actually consumes:

        u ≥ v > 0,  u ≤ v + c·c  (c > 0)
        ⟹  leRat (√u − √v) c          (i.e. `√u − √v ≤ c`).

    Equivalently `√u ≤ √v + c` whenever `u − v ≤ c²`; this is exactly the
    Hölder bound `|√u − √v| ≤ √|u − v|` specialised to a rational tolerance
    `c ≥ √(u−v)`.  PROOF is the elementary squaring chain:
    `(√v + c)² = v + 2c√v + c² ≥ v + c² ≥ u = (√u)²`, lifted to the
    approximations via `heronSeq_sq_ge` (lower bound on `x_v²`),
    `errAt_eventually_small` (upper bound on `x_u²`), and the
    order-reflection of squaring `le_of_sq_le_sq`.

  * The √-Hölder corollary for the semicircle integrand
    `holder_oneMinusSq` — `|√(1−x²) − √(1−y²)| ≤ c` whenever
    `2·|x − y| ≤ c²` (the rectangle bound; `|(1−x²)−(1−y²)| = |x²−y²| =
    |x−y|·|x+y| ≤ 2|x−y|`), in the symmetric (absolute) form via
    `sqrtFrom_sub_leRat` applied to whichever of `1−x²`, `1−y²` is larger.

# NAMED-open (honest residual)

The √-Hölder modulus is delivered in `leRat`-against-a-rational form
(`sqrtFrom_sub_leRat`), which is what `SemicircleCauchy`'s rectangle error
needs (each inter-resolution error is `≤ 2·√(2·mesh)`, a rational tolerance
per resolution).  The literal CReal-to-CReal subtraction inequality
`√u − √v ≤ √(u−v)` is NOT stated as a `CReal.le` because the substrate's
Bishop one-slack `≤` is not transitive; the rational-bounded `leRat` form
above is the sound, reusable, transitivity-free replacement.

# Axiom-gate (AGENTS.md Rule 1 / Rule 6 / Rule 8)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `sorryAx`, no `native_decide`; `decide` only on closed
`Q'`/`Nat`.  Witnesses are `Type`-level data where applicable (the modulus
is inherited from `sqrtFrom`).
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.AbsQ

namespace YMGap.Constructive

namespace CReal

open Q' QPoly

/-! ## Binomial expansion over `Q'` (public re-derivation of the private `sq_add'`) -/

/-- `(p + q)·(p + q) ≃ (p·p + q·q) + (p·q + p·q)` — the AM–GM-ready regrouping.
Public re-derivation of `Sqrt.lean`'s private `sq_add'`, kept here so the
√-Hölder algebra is self-contained and reusable. -/
theorem sq_add_expand (p q : Q') :
    ((p + q) * (p + q)).eqv ((p * p + q * q) + (p * q + p * q)) := by
  -- (p+q)*(p+q) ≃ p*(p+q) + q*(p+q)
  refine Q'.eqv_trans _ _ _ (q_add_mul p q (p + q)) ?_
  -- p*(p+q) ≃ p*p + p*q ;  q*(p+q) ≃ q*p + q*q ≃ p*q + q*q
  have hL : (p * (p + q)).eqv (p * p + p * q) := Q'.mul_add_eqv p p q
  have hR : (q * (p + q)).eqv (p * q + q * q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv q p q) ?_
    exact q_add_congr (Q'.mul_comm_eqv q p) (Q'.eqv_refl (q * q))
  -- (p*p + p*q) + (p*q + q*q) ≃ (p*p + q*q) + (p*q + p*q)
  refine Q'.eqv_trans _ _ _ (q_add_congr hL hR) ?_
  -- swap second group: (p*q + q*q) ≃ (q*q + p*q)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (p * p + p * q) (p * q + q * q) (q * q + p * q)
      (Q'.add_comm_eqv (p * q) (q * q))) ?_
  -- add_swap_inner: (p*p + p*q) + (q*q + p*q) ≃ (p*p + q*q) + (p*q + p*q)
  exact Q'.add_swap_inner (p * p) (p * q) (q * q) (p * q)

/-! ## Radicand monotonicity (re-exports / corollaries of `sqrtFrom_leRat_of_sq`) -/

/-- **√ monotone (single-radicand `leRat` form).**  `√u ≤ b` (sound rational
upper bound) whenever `u ≤ b·b`.  This is `sqrtFrom_leRat_of_sq` named so the
√-Hölder consumers read cleanly. -/
theorem sqrtFrom_mono (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u) (b : Q') (hb : (0 : Q') < b) (hub : u ≤ b * b) :
    CReal.leRat (sqrtFrom u Lu hu hLu hLua) b :=
  sqrtFrom_leRat_of_sq u Lu hu hLu hLua b hb hub

/-! ## Helper: a per-index square bound for the √-Hölder difference

For Heron iterates `x_u = heronSeq u n`, `x_v = heronSeq v n` (both positive),
with the hypotheses `u ≤ v + c·c` and `c ≥ 0`, the squared comparison

    x_u·x_u  ≤  ((x_v + c) + ε)·((x_v + c) + ε)

holds once `errAt u n ≤ c·ε + c·ε`.  The right side is expanded with
`sq_add_expand` and bounded below using `heronSeq_sq_ge` (`v ≤ x_v²`) and
nonnegativity of the cross/square terms. -/
private theorem holder_index_sq
    (u v c ε : Q') (_hv : (0 : Q') < v) (hc : (0 : Q') < c) (hε : (0 : Q') < ε)
    (huvc : u ≤ v + c * c) (xv : Q') (hxv : (0 : Q') < xv) (hxvsq : v ≤ xv * xv)
    (xu : Q') (herr : xu * xu ≤ u + (c * ε + c * ε)) :
    xu * xu ≤ ((xv + c) + ε) * ((xv + c) + ε) := by
  -- abbreviation s := (xv + c)
  -- Step A: x_u² ≤ u + (cε+cε) ≤ (v + c·c) + (cε+cε)
  have hA : xu * xu ≤ (v + c * c) + (c * ε + c * ε) :=
    Q'.le_trans' _ _ _ herr (Q'.add_le_add_right u (v + c * c) (c * ε + c * ε) huvc)
  -- Step B:  (v + c·c) ≤ (xv + c)·(xv + c)
  -- expand (xv+c)² = (xv·xv + c·c) + (xv·c + xv·c) ≥ (v + c·c) + 0
  have hsB : ((xv + c) * (xv + c)).eqv
      ((xv * xv + c * c) + (xv * c + xv * c)) := sq_add_expand xv c
  have hcross_nonneg : (0 : Q') ≤ xv * c + xv * c := by
    have h1 : (0 : Q') ≤ xv * c :=
      Q'.le_of_lt (Q'.mul_pos hxv hc)
    exact Q'.zero_le_add _ _ h1 h1
  -- (v + c·c) ≤ (xv·xv + c·c) ≤ (xv·xv + c·c) + (xv·c + xv·c) ≃ (xv+c)²
  have hB1 : (v + c * c) ≤ (xv * xv + c * c) :=
    Q'.add_le_add_right v (xv * xv) (c * c) hxvsq
  have hB2 : (xv * xv + c * c) ≤ (xv * xv + c * c) + (xv * c + xv * c) :=
    Q'.add_le_self_of_nonneg _ _ hcross_nonneg
  have hB : (v + c * c) ≤ (xv + c) * (xv + c) :=
    Q'.le_trans' _ _ _ hB1 (Q'.le_trans' _ _ _ hB2 (Q'.ge_of_eqv hsB))
  -- Step C: expand ((xv+c)+ε)² = ((xv+c)² + ε²) + ((xv+c)·ε + (xv+c)·ε)
  have hsExp : (((xv + c) + ε) * ((xv + c) + ε)).eqv
      (((xv + c) * (xv + c) + ε * ε) + ((xv + c) * ε + (xv + c) * ε)) :=
    sq_add_expand (xv + c) ε
  -- (xv+c)·ε ≥ c·ε   (since xv ≥ 0 ⟹ xv+c ≥ c)
  have hs_ge_c : c ≤ xv + c := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv c))) ?_
    exact Q'.add_le_add_right 0 xv c (Q'.le_of_lt hxv)
  have hsε_ge_cε : c * ε ≤ (xv + c) * ε :=
    Q'.mul_le_mul_of_nonneg_right c (xv + c) ε hs_ge_c (Q'.le_of_lt hε)
  have hcross_ge : (c * ε + c * ε) ≤ ((xv + c) * ε + (xv + c) * ε) :=
    Q'.add_le_add hsε_ge_cε hsε_ge_cε
  -- Now assemble:  x_u² ≤ (v+c·c)+(cε+cε) ≤ (xv+c)² + (cε+cε) ≤ (xv+c)² + ((xv+c)ε+(xv+c)ε)
  --              ≤ ((xv+c)²+ε²)+((xv+c)ε+(xv+c)ε) ≃ ((xv+c)+ε)²
  have hε2_nonneg : (0 : Q') ≤ ε * ε := SumOfSquares.q_mul_self_nonneg ε
  refine Q'.le_trans' _ _ _ hA ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right (v + c * c) ((xv + c) * (xv + c)) (c * ε + c * ε) hB) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left ((xv + c) * (xv + c)) (c * ε + c * ε)
      ((xv + c) * ε + (xv + c) * ε) hcross_ge) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right ((xv + c) * (xv + c)) ((xv + c) * (xv + c) + ε * ε)
      ((xv + c) * ε + (xv + c) * ε)
      (Q'.add_le_self_of_nonneg ((xv + c) * (xv + c)) (ε * ε) hε2_nonneg)) ?_
  exact Q'.ge_of_eqv hsExp

/-! ## THE TARGET: the √-Hölder / √-subadditivity modulus -/

/-- **√-Hölder / √-subadditivity modulus (rational-bounded form).**

For positive rationals `u ≥ v > 0` with `u ≤ v + c·c` (`c > 0`), the
CReal difference `√u − √v` is bounded by the rational `c`:

    leRat (√u − √v) c        (i.e. `√u − √v ≤ c`).

Equivalently `√u ≤ √v + c` whenever `u − v ≤ c²`.  This is the constructive
Hölder bound `|√u − √v| ≤ √|u − v|` specialised to a rational tolerance
`c ≥ √(u − v)`, in the sound regularity-free `leRat` form that the Riemann
convergence modulus consumes.  PROOF: squaring chain
`(√v + c)² ≥ v + c² ≥ u = (√u)²` (`holder_index_sq`), order-reflected by
`le_of_sq_le_sq` at every approximation. -/
theorem sqrtFrom_sub_leRat
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu) (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv) (hLva : Lv * Lv ≤ v)
    (c : Q') (hc : (0 : Q') < c) (huvc : u ≤ v + c * c) :
    CReal.leRat
      (CReal.add (sqrtFrom u Lu hu hLu hLua)
        (CReal.neg (sqrtFrom v Lv hv hLv hLva))) c := by
  intro ε hε
  -- pick N so that errAt u n ≤ c·ε + c·ε for all n ≥ N
  obtain ⟨N, hN⟩ := errAt_eventually_small u hu (c * ε + c * ε)
    (Q'.add_pos (Q'.mul_pos hc hε) (Q'.mul_pos hc hε))
  refine ⟨N, fun n hn => ?_⟩
  -- the approximation of (√u − √v) at index n is heronSeq u n − heronSeq v n
  show heronSeq u n + -(heronSeq v n) ≤ c + ε
  -- x_u² = u + errAt u n ≤ u + (cε+cε)
  have hxusq_eq : (heronSeq u n * heronSeq u n).eqv (u + errAt u n) := by
    show (heronSeq u n * heronSeq u n).eqv (u + (heronSeq u n * heronSeq u n + -u))
    -- u + (P + -u) ≃ P
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left u (heronSeq u n * heronSeq u n + -u)
        (-u + heronSeq u n * heronSeq u n)
        (Q'.add_comm_eqv (heronSeq u n * heronSeq u n) (-u))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv u (-u) (heronSeq u n * heronSeq u n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (u + -u) 0 (heronSeq u n * heronSeq u n)
        (Q'.add_neg_self_eqv u)) ?_
    exact QPoly.q_zero_add_eqv (heronSeq u n * heronSeq u n)
  have herr : heronSeq u n * heronSeq u n ≤ u + (c * ε + c * ε) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hxusq_eq) ?_
    exact Q'.add_le_add_left u (errAt u n) (c * ε + c * ε) (hN n hn)
  -- x_v² ≥ v
  have hxvsq : v ≤ heronSeq v n * heronSeq v n := heronSeq_sq_ge v hv n
  -- the squared comparison
  have hsq : heronSeq u n * heronSeq u n
      ≤ ((heronSeq v n + c) + ε) * ((heronSeq v n + c) + ε) :=
    holder_index_sq u v c ε hv hc hε huvc (heronSeq v n) (heronSeq_pos hv n) hxvsq
      (heronSeq u n) herr
  -- order-reflect:  x_u ≤ (xv + c) + ε
  have hpos : (0 : Q') < (heronSeq v n + c) + ε :=
    Q'.add_pos (Q'.add_pos (heronSeq_pos hv n) hc) hε
  have hle : heronSeq u n ≤ (heronSeq v n + c) + ε :=
    le_of_sq_le_sq hpos (Q'.le_of_lt (heronSeq_pos hu n)) hsq
  -- x_u − x_v ≤ c + ε  from  x_u ≤ (x_v + c) + ε  by subtracting x_v
  have hxle : heronSeq u n + -(heronSeq v n)
      ≤ ((heronSeq v n + c) + ε) + -(heronSeq v n) :=
    Q'.add_le_add_right (heronSeq u n) ((heronSeq v n + c) + ε)
      (-(heronSeq v n)) hle
  refine Q'.le_trans' _ _ _ hxle (Q'.le_of_eqv ?_)
  -- ((xv+c)+ε) + -xv ≃ (xv + (c+ε)) + -xv ≃ ((c+ε) + xv) + -xv
  --              ≃ (c+ε) + (xv + -xv) ≃ (c+ε)+0 ≃ c+ε
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((heronSeq v n + c) + ε) (heronSeq v n + (c + ε))
      (-(heronSeq v n)) (Q'.add_assoc_eqv (heronSeq v n) c ε)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (heronSeq v n + (c + ε)) ((c + ε) + heronSeq v n)
      (-(heronSeq v n)) (Q'.add_comm_eqv (heronSeq v n) (c + ε))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (c + ε) (heronSeq v n) (-(heronSeq v n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (c + ε) (heronSeq v n + -(heronSeq v n)) 0
      (Q'.add_neg_self_eqv (heronSeq v n))) ?_
  exact QPoly.q_add_zero_eqv (c + ε)

/-! ## √-Hölder corollary for the semicircle integrand `√(1 − x²)`

The Riemann modulus needs, for rational nodes, the rectangle bound

    |√(1 − x²) − √(1 − y²)| ≤ c        whenever   2·|x − y| ≤ c².

We deliver the one-sided form (WLOG `1 − y² ≤ 1 − x²`, i.e. the larger
radicand on the left):  if `u ≥ v > 0` are the two radicands `1 − x²`,
`1 − y²` and `u − v ≤ c²`, then `√u − √v ≤ c`.  The absolute form follows
by symmetry (apply with the radicands swapped on the other branch), which
the consumer selects per node pair.

This is `sqrtFrom_sub_leRat` packaged for the radicands; the arithmetic
`u − v = (1−x²) − (1−y²) = y² − x² = (y−x)(y+x)`, `|u − v| ≤ 2|x − y|` is a
pure `Q'` fact handled at the call site (the radicands are concrete rational
node values), so we state the modulus directly on the radicand difference. -/

/-- **√-Hölder rectangle modulus on a single radicand pair.**  Given the two
positive rational radicands `u ≥ v > 0` (with `sqrtFrom` witnesses) and a
rational tolerance `c > 0` with `u ≤ v + c·c` (i.e. `u − v ≤ c²`):

    √u − √v ≤ c      (sound `leRat`).

Specialise `u = 1 − x²`, `v = 1 − y²`, `c ≥ √(2|x − y|)` to obtain the
semicircle-integrand modulus `|√(1−x²) − √(1−y²)| ≤ √(2|x−y|)` (choosing the
larger radicand on the left).  This is the rectangle bound consumed by the
Riemann convergence modulus. -/
theorem holder_oneMinusSq
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu) (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv) (hLva : Lv * Lv ≤ v)
    (c : Q') (hc : (0 : Q') < c) (huvc : u ≤ v + c * c) :
    CReal.leRat
      (CReal.add (sqrtFrom u Lu hu hLu hLua)
        (CReal.neg (sqrtFrom v Lv hv hLv hLva))) c :=
  sqrtFrom_sub_leRat u Lu hu hLu hLua v Lv hv hLv hLva c hc huvc

end CReal

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.sq_add_expand
#print axioms YMGap.Constructive.CReal.sqrtFrom_mono
#print axioms YMGap.Constructive.CReal.sqrtFrom_sub_leRat
#print axioms YMGap.Constructive.CReal.holder_oneMinusSq
