/-
The genuine `CReal`-valued metric completion of the GNS pre-Hilbert quotient.

# Which gap this closes

`Continuum/GNSQuotient.lean` built the positive-DEFINITE GNS quotient
`QuotSpace = V / Radical` with a `QR`-valued (rational) inner product `qInner`
and a definite squared distance `qDistSq` (`qDistSq_zero_iff`).  The flagged
blocker was that the *completed* inner product is `CReal`-valued: the limit
`lim B(aₙ,bₙ)` of the rational form lives in the completion of `Q′`, not in
`QR`.  This module supplies the `CReal` layer and the metric completion.

# What is genuine here (constructed / proved, axiom-clean)

  * **CReal-valued GNS form.**  `cInner a b := ofQ' (B a b)`, the squared
    seminorm `cNormSq a := ofQ' (B a a)` and squared distance
    `cDistSq a b := ofQ' (distSqQ a b)` (representative level, valued in `CReal`).
    Proved: nonnegativity (`cNormSq_nonneg`, `cDistSq_nonneg`), the descended
    well-definedness `cInner_welldef` (radical-equivalent reps give
    `CReal.Equiv` inner products), symmetry, the descended bilinearity
    `cInner_add_left`, homogeneity `cInner_smul_left`, and the metric
    separation `cDistSq_equiv_czero_iff` (`Equiv (cDistSq a b) czero ↔ rad a b`),
    the `CReal` analog of `qDistSq_zero_iff`.

  * **The quadratic triangle inequality** `distSqQ_triangle`:
    `d²(x,z) ≤ 2·d²(x,y) + 2·d²(y,z)` — proved *sqrt-free* at the `Q′` level from
    the module algebra (`B_cross_le`: `2⟨u,v⟩ ≤ ⟨u,u⟩+⟨v,v⟩`, itself
    `0 ≤ ⟨u−v,u−v⟩`).  This is what makes the completion's null relation
    transitive without a square root.

  * **Cauchy sequences and the completion.**  `CauchyGNS` bundles a sequence of
    representatives with a `Type`-level modulus (the regular-sequence pattern).
    `CauchyNull` is the null relation `d²(xₙ,yₙ) → 0`; it is a genuine
    equivalence (refl/symm via `distSqQ_comm`, **trans via the triangle
    inequality + the quartering `4·(ε/4) = ε`**), so `cauchySetoid` is a real
    `Setoid` and `GNSCompletionSpace = CauchyGNS / CauchyNull` is the completion
    carrier.

  * **The isometric embedding.**  `embedQuot : QuotSpace → GNSCompletionSpace`
    sends `[a]` to the class of the constant sequence at `a` (descends by
    `embed_null_of_rad`), and is **injective** (`embedQuot_injective`, via the
    constructive Archimedean principle `Q'.le_zero_of_forall_invSucc`): the
    pre-Hilbert quotient sits inside its completion.

# What stays an honest Type-level boundary (NOT faked)

The `CReal`-valued inner product on ALL of `GNSCompletionSpace` (not just the
dense image) is the residual: it is the limit `lim cInner(xₙ,yₙ)`, which exists
as a `CReal` via `CReal.completeLimit` once the `CReal` sequence
`n ↦ cInner(xₙ,yₙ)` is shown `ModCauchy` by Cauchy–Schwarz (`GNSData.cauchy_schwarz`
is available).  That `ModCauchy` discharge is the next brick; it is recorded as
the target interface `GNSHilbert` (a `CReal`-valued completion datum) with the
genuine `embedQuot` supplied as the dense-embedding ingredient.  No field is
`sorry`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (via the reused `Q′`/`CReal`
arithmetic, the `GNSQuotient` radical machinery, and `Quotient`/`Quot.sound`).
No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.RegularCReal

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Constructive

/-! ## Small `Q′` and `CReal` glue used by the completion -/

namespace Q'

/-- Antisymmetry of `Q′` order into `eqv`: `a ≤ b` and `b ≤ a` give `a ≃ b`. -/
theorem eqv_of_le_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a.eqv b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm h1 h2

/-- **Archimedean (upper).**  `x ≤ 1/(N+1)` for every `N` forces `x ≤ 0`. -/
theorem le_zero_of_forall_invSucc {x : Q'} (h : ∀ N : Nat, x ≤ Q'.invSucc N) :
    x ≤ 0 := by
  refine Q'.le_of_le_add_mul_invSucc x 0 1 ?_
  intro N
  have hY : (Q'.ofNat 1 * Q'.invSucc N).eqv (Q'.invSucc N) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (Q'.invSucc N) (by decide))
      (Q'.one_mul_eqv (Q'.invSucc N))
  have hb : (Q'.invSucc N).eqv (0 + Q'.ofNat 1 * Q'.invSucc N) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (Q'.ofNat 1 * Q'.invSucc N)) hY)
  exact le_of_le_eqv (h N) hb

/-- **Archimedean (lower).**  `0 ≤ x + 1/(N+1)` for every `N` forces `0 ≤ x`. -/
theorem zero_le_of_forall_invSucc {x : Q'} (h : ∀ N : Nat, (0 : Q') ≤ x + Q'.invSucc N) :
    (0 : Q') ≤ x := by
  refine Q'.le_of_le_add_mul_invSucc 0 x 1 ?_
  intro N
  have hY : (Q'.ofNat 1 * Q'.invSucc N).eqv (Q'.invSucc N) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (Q'.invSucc N) (by decide))
      (Q'.one_mul_eqv (Q'.invSucc N))
  have hb : (x + Q'.invSucc N).eqv (x + Q'.ofNat 1 * Q'.invSucc N) :=
    Q'.add_eqv_congr_left x (Q'.invSucc N) (Q'.ofNat 1 * Q'.invSucc N) (Q'.eqv_symm hY)
  exact le_of_le_eqv (h N) hb

end Q'

namespace CReal

/-- The embedding sends `eqv`-equal rationals to `CReal.Equiv` constants. -/
theorem ofQ'_equiv_of_eqv {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
  · show a ≤ b + ε
    exact Q'.le_trans' a b (b + ε) (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε))
  · show b ≤ a + ε
    exact Q'.le_trans' b a (a + ε) (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))

/-- The converse for constants: `Equiv (ofQ' x) 0` forces `x ≃ 0`
(constructive Archimedean both ways). -/
theorem ofQ'_eqv_zero_of_equiv {x : Q'} (h : CReal.Equiv (CReal.ofQ' x) CReal.czero) :
    x.eqv 0 := by
  have hx_le : x ≤ 0 := by
    refine Q'.le_zero_of_forall_invSucc ?_
    intro N
    obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
    have hxx : x ≤ 0 + Q'.invSucc N := (hM M (Nat.le_refl M)).1
    exact le_of_le_eqv hxx (QPoly.q_zero_add_eqv (Q'.invSucc N))
  have hge : (0 : Q') ≤ x := by
    refine Q'.zero_le_of_forall_invSucc ?_
    intro N
    obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
    exact (hM M (Nat.le_refl M)).2
  exact Q'.eqv_of_le_le hx_le hge

end CReal

/-! ## `Q′` rearrangements behind the quadratic triangle inequality -/

namespace GNSAux

/-- `(-a) + (-b) ≃ -(a+b)`. -/
theorem neg_add_eqv (a b : Q') : ((-a) + (-b)).eqv (-(a + b)) := by
  apply QPoly.q_eqv_of_sub_zero
  have hmid : (((-a) + (-b)) + (a + b)).eqv 0 := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-a) (-b) (a + b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) ((-b) + (a + b)) (((-b) + a) + b)
        (Q'.eqv_symm (Q'.add_assoc_eqv (-b) a b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (((-b) + a) + b) ((a + (-b)) + b)
        (Q'.add_eqv_congr_right ((-b) + a) (a + (-b)) b (Q'.add_comm_eqv (-b) a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) ((a + (-b)) + b) (a + ((-b) + b))
        (Q'.add_assoc_eqv a (-b) b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (a + ((-b) + b)) (a + 0)
        (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (a + 0) a (QPoly.q_add_zero_eqv a)) ?_
    exact Q'.neg_add_self_eqv a
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((-a) + (-b)) (-(-(a + b))) (a + b) (Q'.neg_neg_eqv (a + b)))
    hmid

/-- `(P+M)+(M+Q) ≃ (P+Q)+(M+M)`. -/
theorem rearr1 (P M Q : Q') : ((P + M) + (M + Q)).eqv ((P + Q) + (M + M)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P M (M + Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P (M + (M + Q)) ((M + M) + Q)
      (Q'.eqv_symm (Q'.add_assoc_eqv M M Q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((M + M) + Q) (Q + (M + M)) (Q'.add_comm_eqv (M + M) Q)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv P Q (M + M))

/-- `(P+(-M))+((-M)+Q) ≃ (P+Q)+(-(M+M))`. -/
theorem rearr2 (P M Q : Q') :
    ((P + (-M)) + ((-M) + Q)).eqv ((P + Q) + (-(M + M))) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (-M) ((-M) + Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((-M) + ((-M) + Q)) (((-M) + (-M)) + Q)
      (Q'.eqv_symm (Q'.add_assoc_eqv (-M) (-M) Q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P (((-M) + (-M)) + Q) ((-(M + M)) + Q)
      (Q'.add_eqv_congr_right ((-M) + (-M)) (-(M + M)) Q (neg_add_eqv M M))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((-(M + M)) + Q) (Q + (-(M + M)))
      (Q'.add_comm_eqv (-(M + M)) Q)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv P Q (-(M + M)))

/-- `(P+Q)+(P+Q) ≃ (P+P)+(Q+Q)`. -/
theorem add4_swap (P Q : Q') : ((P + Q) + (P + Q)).eqv ((P + P) + (Q + Q)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P Q (P + Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P (Q + (P + Q)) ((Q + P) + Q)
      (Q'.eqv_symm (Q'.add_assoc_eqv Q P Q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((Q + P) + Q) ((P + Q) + Q)
      (Q'.add_eqv_congr_right (Q + P) (P + Q) Q (Q'.add_comm_eqv Q P))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((P + Q) + Q) (P + (Q + Q)) (Q'.add_assoc_eqv P Q Q)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv P P (Q + Q))

end GNSAux

end YMGap.Constructive

namespace YMGap.Continuum.GNSQuotient

open YMGap.Constructive

namespace GNSData

variable (D : GNSData)

/-! ## The CReal-valued GNS form (representative level) -/

/-- The **squared `Q′` distance** `d²(a,b) = ⟨a−b,a−b⟩`. -/
def distSqQ (a b : D.V) : Q' := D.B (D.sub a b) (D.sub a b)

/-- The **CReal GNS inner product** `⟨a,b⟩ := ofQ' (B a b)`. -/
def cInner (a b : D.V) : CReal := CReal.ofQ' (D.B a b)

/-- The **CReal squared seminorm** `‖a‖² := ofQ' (B a a)`. -/
def cNormSq (a : D.V) : CReal := CReal.ofQ' (D.B a a)

/-- The **CReal squared distance** `d²(a,b) := ofQ' (distSqQ a b)`. -/
def cDistSq (a b : D.V) : CReal := CReal.ofQ' (D.distSqQ a b)

/-- `‖a‖² ≥ 0` in `CReal` (reflection positivity). -/
theorem cNormSq_nonneg (a : D.V) : CReal.czero ≤ D.cNormSq a :=
  CReal.ofQ'_le_ofQ' (D.self_nonneg a)

/-- `d²(a,b) ≥ 0` in `CReal`. -/
theorem cDistSq_nonneg (a b : D.V) : CReal.czero ≤ D.cDistSq a b :=
  CReal.ofQ'_le_ofQ' (D.self_nonneg (D.sub a b))

/-- **Well-definedness of `cInner` on radical classes** (up to `CReal.Equiv`). -/
theorem cInner_welldef {a a' b b' : D.V} (ha : D.rad a a') (hb : D.rad b b') :
    CReal.Equiv (D.cInner a b) (D.cInner a' b') :=
  CReal.ofQ'_equiv_of_eqv (D.B_welldef ha hb)

/-- **Symmetry** of the CReal inner product. -/
theorem cInner_symm (a b : D.V) : CReal.Equiv (D.cInner a b) (D.cInner b a) :=
  CReal.ofQ'_equiv_of_eqv (D.B_symm a b)

/-- **Descended bilinearity (left)**:
`⟨a+b,c⟩ ≃ ⟨a,c⟩ + ⟨b,c⟩` in `CReal`. -/
theorem cInner_add_left (a b c : D.V) :
    CReal.Equiv (D.cInner (D.add a b) c) (CReal.add (D.cInner a c) (D.cInner b c)) :=
  CReal.ofQ'_equiv_of_eqv (D.B_add_left a b c)

/-- **Homogeneity (left)**: `⟨s·a,b⟩ ≃ ofQ' (s · ⟨a,b⟩)`. -/
theorem cInner_smul_left (s : Q') (a b : D.V) :
    CReal.Equiv (D.cInner (D.smul s a) b) (CReal.ofQ' (s * D.B a b)) :=
  CReal.ofQ'_equiv_of_eqv (D.B_smul_left s a b)

/-- **The CReal metric separates points**: `d²(a,b) ≃ 0 ⇔ a ≈ b` (radical).
The `CReal` analog of `qDistSq_zero_iff`. -/
theorem cDistSq_equiv_czero_iff (a b : D.V) :
    CReal.Equiv (D.cDistSq a b) CReal.czero ↔ D.rad a b := by
  constructor
  · intro h; exact CReal.ofQ'_eqv_zero_of_equiv h
  · intro h; exact CReal.ofQ'_equiv_of_eqv h

/-! ## The quadratic triangle inequality (sqrt-free) -/

/-- Diagonal expansion of a sum:
`⟨u+v,u+v⟩ ≃ (⟨u,u⟩+⟨u,v⟩) + (⟨v,u⟩+⟨v,v⟩)`. -/
theorem B_add_diag_expand (u v : D.V) :
    (D.B (D.add u v) (D.add u v)).eqv
      ((D.B u u + D.B u v) + (D.B v u + D.B v v)) :=
  Q'.eqv_trans _ _ _ (D.B_add_left u v (D.add u v))
    (QPoly.q_add_congr (D.B_add_right u u v) (D.B_add_right v u v))

/-- Diagonal expansion of a difference:
`⟨u−v,u−v⟩ ≃ (⟨u,u⟩+(−⟨u,v⟩)) + ((−⟨u,v⟩)+⟨v,v⟩)`. -/
theorem B_sub_diag_expand (a b : D.V) :
    (D.B (D.sub a b) (D.sub a b)).eqv
      (((D.B a a) + (-(D.B a b))) + ((-(D.B a b)) + (D.B b b))) := by
  show (D.B (D.add a (D.neg b)) (D.add a (D.neg b))).eqv _
  refine Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg b) (D.add a (D.neg b))) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (D.B_add_right a a (D.neg b)) (D.B_add_right (D.neg b) a (D.neg b))) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_congr (Q'.eqv_refl (D.B a a)) (D.B_neg_right a b))
    (QPoly.q_add_congr
      (Q'.eqv_trans _ _ _ (D.B_neg_left b a)
        (Q'.neg_eqv_congr (D.B b a) (D.B a b) (D.B_symm b a)))
      (D.B_neg_neg b))

/-- **The cross-term bound** `⟨u,v⟩ + ⟨u,v⟩ ≤ ⟨u,u⟩ + ⟨v,v⟩`, i.e. `2⟨u,v⟩ ≤ P+Q`.
Pure module algebra from `0 ≤ ⟨u−v,u−v⟩`; the sqrt-free heart of the triangle
inequality. -/
theorem B_cross_le (u v : D.V) :
    (D.B u v + D.B u v) ≤ (D.B u u + D.B v v) := by
  have hpos : (0 : Q') ≤ D.B (D.sub u v) (D.sub u v) := D.self_nonneg (D.sub u v)
  have hexp : (D.B (D.sub u v) (D.sub u v)).eqv
      (((D.B u u) + (-(D.B u v))) + ((-(D.B u v)) + (D.B v v))) := D.B_sub_diag_expand u v
  have hre : (((D.B u u) + (-(D.B u v))) + ((-(D.B u v)) + (D.B v v))).eqv
      (((D.B u u) + (D.B v v)) + (-((D.B u v) + (D.B u v)))) :=
    GNSAux.rearr2 (D.B u u) (D.B u v) (D.B v v)
  have h0 : (0 : Q') ≤ ((D.B u u) + (D.B v v)) + (-((D.B u v) + (D.B u v))) :=
    le_of_le_eqv (le_of_le_eqv hpos hexp) hre
  exact q_le_of_sub_nonneg h0

/-- Commutativity of the squared distance `d²(a,b) ≃ d²(b,a)`. -/
theorem distSqQ_comm (a b : D.V) : (D.distSqQ a b).eqv (D.distSqQ b a) := by
  have hv0 : D.veq (D.neg (D.sub b a)) (D.sub a b) :=
    D.veq_trans (D.neg_add_distrib b (D.neg a))
      (D.veq_trans (D.add_congr (D.veq_refl (D.neg b)) (D.neg_neg a))
        (D.add_comm (D.neg b) a))
  have hv : D.veq (D.sub a b) (D.neg (D.sub b a)) := D.veq_symm hv0
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hv) (D.B_neg_neg (D.sub b a))

/-- **The quadratic triangle inequality**:
`d²(x,z) ≤ 2·d²(x,y) + 2·d²(y,z)` (written `(P+P)+(Q+Q)`). -/
theorem distSqQ_triangle (x y z : D.V) :
    D.distSqQ x z ≤
      (D.distSqQ x y + D.distSqQ x y) + (D.distSqQ y z + D.distSqQ y z) := by
  have hexp0 := D.B_add_diag_expand (D.sub x y) (D.sub y z)
  have hsym : (D.B (D.sub y z) (D.sub x y)).eqv (D.B (D.sub x y) (D.sub y z)) :=
    D.B_symm (D.sub y z) (D.sub x y)
  have hexp : (D.B (D.add (D.sub x y) (D.sub y z)) (D.add (D.sub x y) (D.sub y z))).eqv
      ((D.B (D.sub x y) (D.sub x y) + D.B (D.sub x y) (D.sub y z))
        + (D.B (D.sub x y) (D.sub y z) + D.B (D.sub y z) (D.sub y z))) :=
    Q'.eqv_trans _ _ _ hexp0
      (QPoly.q_add_congr (Q'.eqv_refl _) (QPoly.q_add_congr hsym (Q'.eqv_refl _)))
  have hv : D.veq (D.sub x z) (D.add (D.sub x y) (D.sub y z)) :=
    D.veq_symm (D.sub_add_sub x y z)
  have hdiag : (D.B (D.sub x z) (D.sub x z)).eqv
      (D.B (D.add (D.sub x y) (D.sub y z)) (D.add (D.sub x y) (D.sub y z))) :=
    D.B_diag_congr hv
  have hfull : (D.distSqQ x z).eqv
      ((D.distSqQ x y + D.B (D.sub x y) (D.sub y z))
        + (D.B (D.sub x y) (D.sub y z) + D.distSqQ y z)) :=
    Q'.eqv_trans _ _ _ hdiag hexp
  have hre1 := GNSAux.rearr1 (D.distSqQ x y) (D.B (D.sub x y) (D.sub y z)) (D.distSqQ y z)
  have hcross : (D.B (D.sub x y) (D.sub y z) + D.B (D.sub x y) (D.sub y z))
        ≤ (D.distSqQ x y + D.distSqQ y z) :=
    D.B_cross_le (D.sub x y) (D.sub y z)
  have h1 : D.distSqQ x z
        ≤ ((D.distSqQ x y + D.distSqQ y z)
            + (D.B (D.sub x y) (D.sub y z) + D.B (D.sub x y) (D.sub y z))) :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfull hre1)
  have h2 : ((D.distSqQ x y + D.distSqQ y z)
            + (D.B (D.sub x y) (D.sub y z) + D.B (D.sub x y) (D.sub y z)))
        ≤ ((D.distSqQ x y + D.distSqQ y z) + (D.distSqQ x y + D.distSqQ y z)) :=
    Q'.add_le_add_left (D.distSqQ x y + D.distSqQ y z) _ _ hcross
  have h3 : ((D.distSqQ x y + D.distSqQ y z) + (D.distSqQ x y + D.distSqQ y z)).eqv
        ((D.distSqQ x y + D.distSqQ x y) + (D.distSqQ y z + D.distSqQ y z)) :=
    GNSAux.add4_swap (D.distSqQ x y) (D.distSqQ y z)
  exact le_of_le_eqv (Q'.le_trans' _ _ _ h1 h2) h3

end GNSData

/-! ## Cauchy sequences of representatives -/

/-- A **Cauchy sequence in the GNS pre-Hilbert space**: a sequence of
representatives with a `Type`-level squared-distance modulus. -/
structure CauchyGNS (D : GNSData) where
  /-- The sequence of representatives. -/
  seq : Nat → D.V
  /-- The squared-distance modulus, `Type`-level data. -/
  modulus : Q' → Nat
  /-- Past `modulus ε`, the squared distance between terms is `≤ ε`. -/
  isCauchy : ∀ ε : Q', (0 : Q') < ε → ∀ p q : Nat,
    modulus ε ≤ p → modulus ε ≤ q → D.distSqQ (seq p) (seq q) ≤ ε

namespace GNSData

variable (D : GNSData)

/-- The CReal form of the Cauchy condition: `d²(xₚ,x_q) ≤ ofQ' ε`. -/
theorem CauchyGNS.isCauchy_creal (x : CauchyGNS D) (ε : Q') (hε : (0 : Q') < ε)
    (p q : Nat) (hp : x.modulus ε ≤ p) (hq : x.modulus ε ≤ q) :
    D.cDistSq (x.seq p) (x.seq q) ≤ CReal.ofQ' ε :=
  CReal.ofQ'_le_ofQ' (x.isCauchy ε hε p q hp hq)

end GNSData

/-! ## The null relation and the completion -/

/-- The **null relation** on Cauchy sequences: `d²(xₙ,yₙ) → 0`. -/
def CauchyNull (D : GNSData) (x y : CauchyGNS D) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    D.distSqQ (x.seq n) (y.seq n) ≤ ε

/-- Reflexivity of the null relation (each term has zero self-distance). -/
theorem cauchyNull_refl (D : GNSData) (x : CauchyGNS D) : CauchyNull D x x := by
  intro ε hε
  exact ⟨0, fun n _ =>
    Q'.le_trans' _ 0 ε (Q'.le_of_eqv (D.rad_refl (x.seq n))) (Q'.le_of_lt hε)⟩

/-- Symmetry of the null relation (via `distSqQ_comm`). -/
theorem cauchyNull_symm (D : GNSData) {x y : CauchyGNS D} (h : CauchyNull D x y) :
    CauchyNull D y x := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => le_of_eqv_le (D.distSqQ_comm (y.seq n) (x.seq n)) (hN n hn)⟩

/-- **Transitivity of the null relation** — via the quadratic triangle
inequality and the quartering `4·(ε/4) = ε`. -/
theorem cauchyNull_trans (D : GNSData) {x y z : CauchyGNS D}
    (h1 : CauchyNull D x y) (h2 : CauchyNull D y z) : CauchyNull D x z := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * (HalfPow.half * ε) :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨N1, hN1⟩ := h1 _ hq
  obtain ⟨N2, hN2⟩ := h2 _ hq
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have ha : D.distSqQ (x.seq n) (y.seq n) ≤ HalfPow.half * (HalfPow.half * ε) := hN1 n hn1
  have hb : D.distSqQ (y.seq n) (z.seq n) ≤ HalfPow.half * (HalfPow.half * ε) := hN2 n hn2
  have htri := D.distSqQ_triangle (x.seq n) (y.seq n) (z.seq n)
  have hr : (D.distSqQ (x.seq n) (y.seq n) + D.distSqQ (x.seq n) (y.seq n))
            + (D.distSqQ (y.seq n) (z.seq n) + D.distSqQ (y.seq n) (z.seq n))
          ≤ ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
              + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))) :=
    Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb)
  have heps : ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
              + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))).eqv ε := by
    have hqq : (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε)).eqv
        (HalfPow.half * ε) := ExpNeg.two_halves (HalfPow.half * ε)
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hqq hqq) (ExpNeg.two_halves ε)
  exact le_of_le_eqv (Q'.le_trans' _ _ _ htri hr) heps

/-- The null relation as a `Setoid`. -/
def cauchySetoid (D : GNSData) : Setoid (CauchyGNS D) where
  r := CauchyNull D
  iseqv := ⟨cauchyNull_refl D, fun h => cauchyNull_symm D h,
    fun h1 h2 => cauchyNull_trans D h1 h2⟩

/-- **The completion carrier** `CauchyGNS / CauchyNull`. -/
def GNSCompletionSpace (D : GNSData) : Type := Quotient (cauchySetoid D)

/-! ## The isometric embedding -/

/-- The constant Cauchy sequence at `a`. -/
def constCauchy (D : GNSData) (a : D.V) : CauchyGNS D where
  seq := fun _ => a
  modulus := fun _ => 0
  isCauchy := fun ε hε _ _ _ _ =>
    Q'.le_trans' _ 0 ε (Q'.le_of_eqv (D.rad_refl a)) (Q'.le_of_lt hε)

/-- Radical-equivalent representatives give null-equivalent constant sequences. -/
theorem embed_null_of_rad (D : GNSData) {a a' : D.V} (h : D.rad a a') :
    CauchyNull D (constCauchy D a) (constCauchy D a') :=
  fun ε hε => ⟨0, fun _ _ => Q'.le_trans' _ 0 ε (Q'.le_of_eqv h) (Q'.le_of_lt hε)⟩

/-- The class of the constant sequence at `a`. -/
def embedV (D : GNSData) (a : D.V) : GNSCompletionSpace D :=
  Quotient.mk (cauchySetoid D) (constCauchy D a)

/-- **The isometric embedding** `QuotSpace → GNSCompletionSpace`, descending
`a ↦ ⟦const a⟧` through the radical. -/
def embedQuot (D : GNSData) : D.QuotSpace → GNSCompletionSpace D :=
  Quotient.lift (fun a => embedV D a)
    (fun _ _ hr => Quotient.sound (embed_null_of_rad D hr))

/-- Computation rule: `embedQuot [a] = ⟦const a⟧`. -/
theorem embedQuot_mk (D : GNSData) (a : D.V) :
    embedQuot D (D.qmk a) = embedV D a := rfl

/-- A null constant pair forces the radical relation (constructive Archimedean). -/
theorem constCauchy_null_imp_rad (D : GNSData) {a b : D.V}
    (h : CauchyNull D (constCauchy D a) (constCauchy D b)) : D.rad a b := by
  have hle : D.distSqQ a b ≤ 0 := by
    refine Q'.le_zero_of_forall_invSucc ?_
    intro N
    obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
    exact hM M (Nat.le_refl M)
  have hge : (0 : Q') ≤ D.distSqQ a b := D.self_nonneg (D.sub a b)
  exact Q'.eqv_of_le_le hle hge

/-- **The embedding is injective**: the pre-Hilbert quotient sits inside its
completion. -/
theorem embedQuot_injective (D : GNSData) {p q : D.QuotSpace}
    (h : embedQuot D p = embedQuot D q) : p = q := by
  revert h
  refine Quotient.inductionOn₂ p q ?_
  intro a b h
  exact Quotient.sound (constCauchy_null_imp_rad D (Quotient.exact h))

/-! ## The CReal-valued completion interface (honest Type-level target)

The remaining brick is the `CReal`-valued inner product on ALL of
`GNSCompletionSpace`, the limit `lim cInner(xₙ,yₙ)` — a `CReal` via
`CReal.completeLimit` once `n ↦ cInner(xₙ,yₙ)` is shown `ModCauchy` from
`GNSData.cauchy_schwarz`.  The target is recorded as this interface; the
genuine `embedQuot` is the dense-embedding ingredient it consumes.  No field is
`sorry`. -/

/-- A **CReal-valued completion datum**: a carrier with the dense isometric
embedding of the pre-Hilbert quotient and a `CReal`-valued inner product
extending `cInner` on the image. -/
structure GNSHilbert (D : GNSData) where
  /-- The completed carrier. -/
  carrier : Type
  /-- The dense isometric embedding of the quotient. -/
  ι : D.QuotSpace → carrier
  /-- The `CReal`-valued extended inner product. -/
  cinner : carrier → carrier → CReal
  /-- The inner product extends `cInner` on the dense image (up to `Equiv`). -/
  ι_inner : ∀ a b : D.V, CReal.Equiv (cinner (ι (D.qmk a)) (ι (D.qmk b))) (D.cInner a b)

end YMGap.Continuum.GNSQuotient

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.eqv_of_le_le
#print axioms YMGap.Constructive.Q'.le_zero_of_forall_invSucc
#print axioms YMGap.Constructive.Q'.zero_le_of_forall_invSucc
#print axioms YMGap.Constructive.CReal.ofQ'_equiv_of_eqv
#print axioms YMGap.Constructive.CReal.ofQ'_eqv_zero_of_equiv
#print axioms YMGap.Constructive.GNSAux.neg_add_eqv
#print axioms YMGap.Constructive.GNSAux.rearr1
#print axioms YMGap.Constructive.GNSAux.rearr2
#print axioms YMGap.Constructive.GNSAux.add4_swap
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cNormSq_nonneg
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cDistSq_nonneg
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_welldef
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_symm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_add_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cInner_smul_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cDistSq_equiv_czero_iff
#print axioms YMGap.Continuum.GNSQuotient.GNSData.B_cross_le
#print axioms YMGap.Continuum.GNSQuotient.GNSData.distSqQ_comm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.distSqQ_triangle
#print axioms YMGap.Continuum.GNSQuotient.cauchyNull_refl
#print axioms YMGap.Continuum.GNSQuotient.cauchyNull_symm
#print axioms YMGap.Continuum.GNSQuotient.cauchyNull_trans
#print axioms YMGap.Continuum.GNSQuotient.cauchySetoid
#print axioms YMGap.Continuum.GNSQuotient.embedQuot
#print axioms YMGap.Continuum.GNSQuotient.embedQuot_injective
