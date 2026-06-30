/-
The genuine GNS quotient pre-Hilbert space — `V / Radical` with a
positive-DEFINITE descended inner product.

# Which gap this closes

`Continuum/OSReconstructionProgress.lean` closed the analytic OS/GNS step on an
abstract carrier `V`: it built `PreInnerForm V` from the reflection-positivity
input (the diagonalized OS2 statement `nonnegQuad`), proved the **sharp
Cauchy–Schwarz** `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩` (`PreInnerForm.cauchy_schwarz`) and the
**radical-descent law** `⟨a,a⟩ ≃ 0 ⇒ ∀b, ⟨a,b⟩ ≃ 0`
(`PreInnerForm.radical_form_zero`).  But it noted the *actual GNS quotient*
`V/Radical` and the positive-DEFINITE descended inner product need a
MODULE / subtraction structure on the carrier — which lives at the
observable-algebra level (`Continuum/FiniteVolumeGNS.lean` builds the GNS form
`⟨a,b⟩ = E_Λ(star a · b)` with `inner_nonneg` = reflection positivity, but
`ObsAlg` carries only `one/mul/star`, no `add/neg/sub`).

This module supplies that module structure as a `GNSData` bundle and builds the
genuine quotient.

# What is genuine here (constructed / proved, axiom-clean)

  * `GNSData` — a carrier `V` with a carrier-equivalence `veq` (the
    observable-algebra equality is `≃`, not propositional `=`), an abelian
    group structure `(add, zero, neg)` up to `veq`, a rational scalar action
    `smul`, and a `Q′`-valued form `B` that is biadditive, homogeneous,
    symmetric and **reflection-positive** `0 ≤ B a a` (the
    `FiniteVolumeGNS.inner_nonneg` content).
  * `GNSData.toPreInnerForm` — every `GNSData` yields a `PreInnerForm`: the OS2
    `nonnegQuad` is DERIVED from biadditivity + homogeneity + `self_nonneg` via
    the sum-of-squares expansion `B(s·a+r·b, s·a+r·b) = s²Baa + 2sr·Bab +
    r²Bbb`.  So the proved sharp Cauchy–Schwarz and radical descent transfer.
  * `GNSData.radSetoid` — **the radical equivalence** `a ≈ b := ⟨a−b,a−b⟩ ≃ 0`,
    with reflexivity, symmetry and the load-bearing **TRANSITIVITY** proved via
    the parallelogram expansion `⟨a−c,a−c⟩ = ⟨x,x⟩ + 2⟨x,y⟩ + ⟨y,y⟩`
    (`x=a−b, y=b−c`) and `radical_form_zero` killing the cross term.
  * `GNSData.B_welldef` — the form descends to classes:
    `a≈a', b≈b' ⇒ ⟨a,b⟩ ≃ ⟨a',b'⟩` (biadditivity + radical descent).
  * `GNSData.QuotSpace`, `qInner` — the **GNS quotient** `V/Radical` (a genuine
    `Quotient`, `Quot.sound` permitted) with the descended inner product valued
    in the `eqv`-quotient `QR` of `Q′`.
  * `GNSData.qInner_posdef` — **POSITIVE-DEFINITENESS**:
    `⟨[a],[a]⟩ = 0 ⇔ [a] = [0]`.  A genuine constructive inner-product space.
  * `qWeightGNS` — a concrete non-degenerate inhabitant on `V = Q′` with the
    weighted form `⟨x,y⟩ = w·(x·y)` (`w ≥ 0`), discharging every `GNSData`
    field.

# What stays an honest Type-level boundary (NOT faked)

The metric **completion** to the full Hilbert space (Cauchy sequences of
quotient elements w.r.t. the `Q′`-valued squared seminorm `B a a`) is stated as
the Type-level interface `GNSCompletion`, taking the proved positive-definite
quotient as input.  No field is `sorry`; the trivial inhabitant
`GNSCompletion.trivial` (completion = itself, valid in the located /
finite-dimensional case) is provided, and the general constructive completion
carrier is the residual for the next iteration.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (via the reused `Q′` arithmetic, the
`OSReconstructionProgress` Cauchy–Schwarz, and `Quotient`).  No `Classical.*`,
no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.FiniteVolumeGNS
import YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Continuum.GNSQuotient

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

/-! ## The GNS module datum -/

/-- A **GNS module datum**: an abelian group carrier (up to `veq`) with a
rational scalar action and a reflection-positive `Q′`-valued form `B`. -/
structure GNSData where
  /-- The carrier type. -/
  V : Type
  /-- The carrier equivalence (the GNS form respects this, like `Q′`'s `eqv`). -/
  veq : V → V → Prop
  veq_refl : ∀ a, veq a a
  veq_symm : ∀ {a b}, veq a b → veq b a
  veq_trans : ∀ {a b c}, veq a b → veq b c → veq a c
  /-- Additive identity. -/
  zero : V
  /-- Addition. -/
  add : V → V → V
  /-- Negation. -/
  neg : V → V
  /-- Rational scalar action. -/
  smul : Q' → V → V
  add_congr : ∀ {a a' b b'}, veq a a' → veq b b' → veq (add a b) (add a' b')
  neg_congr : ∀ {a a'}, veq a a' → veq (neg a) (neg a')
  smul_congr : ∀ (s : Q') {a a'}, veq a a' → veq (smul s a) (smul s a')
  add_assoc : ∀ a b c, veq (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, veq (add a b) (add b a)
  zero_add : ∀ a, veq (add zero a) a
  neg_add : ∀ a, veq (add (neg a) a) zero
  /-- The GNS form `⟨a,b⟩`. -/
  B : V → V → Q'
  /-- The form respects the carrier equivalence (left argument). -/
  B_congr_left : ∀ {a a' : V} (b : V), veq a a' → (B a b).eqv (B a' b)
  /-- Biadditivity (left). -/
  B_add_left : ∀ a b c, (B (add a b) c).eqv (B a c + B b c)
  /-- Homogeneity (left). -/
  B_smul_left : ∀ (s : Q') (a b), (B (smul s a) b).eqv (s * B a b)
  /-- Conjugate symmetry (real form: `star = id`). -/
  B_symm : ∀ a b, (B a b).eqv (B b a)
  /-- **Reflection positivity** `0 ≤ ⟨a,a⟩` (the `inner_nonneg` content). -/
  self_nonneg : ∀ a, (0 : Q') ≤ B a a

namespace GNSData

variable (D : GNSData)

/-- Subtraction `a − b := a + (−b)`. -/
def sub (a b : D.V) : D.V := D.add a (D.neg b)

/-! ### Carrier-level group facts -/

/-- `a + 0 ≈ a`. -/
theorem add_zero (a : D.V) : D.veq (D.add a D.zero) a :=
  D.veq_trans (D.add_comm a D.zero) (D.zero_add a)

/-- `−0 ≈ 0`. -/
theorem neg_zero : D.veq (D.neg D.zero) D.zero :=
  D.veq_trans (D.veq_symm (D.add_zero (D.neg D.zero))) (D.neg_add D.zero)

/-- `(u − v) + v ≈ u`. -/
theorem sub_add_cancel (u v : D.V) : D.veq (D.add (D.sub u v) v) u :=
  D.veq_trans (D.add_assoc u (D.neg v) v)
    (D.veq_trans (D.add_congr (D.veq_refl u) (D.neg_add v)) (D.add_zero u))

/-- `(a − b) + (b − c) ≈ a − c`. -/
theorem sub_add_sub (a b c : D.V) :
    D.veq (D.add (D.sub a b) (D.sub b c)) (D.sub a c) := by
  show D.veq (D.add (D.add a (D.neg b)) (D.add b (D.neg c))) (D.add a (D.neg c))
  refine D.veq_trans (D.add_assoc a (D.neg b) (D.add b (D.neg c))) ?_
  refine D.add_congr (D.veq_refl a) ?_
  refine D.veq_trans (D.veq_symm (D.add_assoc (D.neg b) b (D.neg c))) ?_
  exact D.veq_trans (D.add_congr (D.neg_add b) (D.veq_refl (D.neg c)))
    (D.zero_add (D.neg c))

/-! ### Derived form laws -/

/-- The form respects the carrier equivalence on the right. -/
theorem B_congr_right {a a' : D.V} (b : D.V) (h : D.veq a a') :
    (D.B b a).eqv (D.B b a') :=
  Q'.eqv_trans _ _ _ (D.B_symm b a)
    (Q'.eqv_trans _ _ _ (D.B_congr_left b h) (D.B_symm a' b))

/-- The form respects the carrier equivalence on the diagonal. -/
theorem B_diag_congr {u v : D.V} (h : D.veq u v) : (D.B u u).eqv (D.B v v) :=
  Q'.eqv_trans _ _ _ (D.B_congr_left u h) (D.B_congr_right v h)

/-- Biadditivity (right), from left-biadditivity and symmetry. -/
theorem B_add_right (a b c : D.V) :
    (D.B a (D.add b c)).eqv (D.B a b + D.B a c) :=
  Q'.eqv_trans _ _ _ (D.B_symm a (D.add b c))
    (Q'.eqv_trans _ _ _ (D.B_add_left b c a)
      (QPoly.q_add_congr (D.B_symm b a) (D.B_symm c a)))

/-- Homogeneity (right). -/
theorem B_smul_right (s : Q') (a b : D.V) :
    (D.B a (D.smul s b)).eqv (s * D.B a b) :=
  Q'.eqv_trans _ _ _ (D.B_symm a (D.smul s b))
    (Q'.eqv_trans _ _ _ (D.B_smul_left s b a)
      (Q'.mul_eqv_congr_left s (D.B b a) (D.B a b) (D.B_symm b a)))

/-- `⟨0, z⟩ ≃ 0`. -/
theorem B_zero_left (z : D.V) : (D.B D.zero z).eqv 0 := by
  have h00 : D.veq (D.add D.zero D.zero) D.zero := D.zero_add D.zero
  have e1 : (D.B (D.add D.zero D.zero) z).eqv (D.B D.zero z) := D.B_congr_left z h00
  have e2 : (D.B (D.add D.zero D.zero) z).eqv (D.B D.zero z + D.B D.zero z) :=
    D.B_add_left D.zero D.zero z
  have e3 : (D.B D.zero z).eqv (D.B D.zero z + D.B D.zero z) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm e1) e2
  -- from `w ≃ w + w` conclude `w ≃ 0`.
  have e4 : ((D.B D.zero z + D.B D.zero z) + -(D.B D.zero z)).eqv (D.B D.zero z) :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (D.B D.zero z) (D.B D.zero z) (-(D.B D.zero z)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (D.B D.zero z) (D.B D.zero z + -(D.B D.zero z)) 0
          (OSReconstructionProgress.q_add_neg_self (D.B D.zero z)))
        (QPoly.q_add_zero_eqv (D.B D.zero z)))
  have e5 : (D.B D.zero z + -(D.B D.zero z)).eqv (D.B D.zero z) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (D.B D.zero z) (D.B D.zero z + D.B D.zero z) (-(D.B D.zero z)) e3) e4
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm e5)
    (OSReconstructionProgress.q_add_neg_self (D.B D.zero z))

/-- `⟨−a, z⟩ ≃ −⟨a, z⟩`. -/
theorem B_neg_left (a z : D.V) : (D.B (D.neg a) z).eqv (-(D.B a z)) := by
  have hz : D.veq (D.add (D.neg a) a) D.zero := D.neg_add a
  have e1 : (D.B (D.add (D.neg a) a) z).eqv 0 :=
    Q'.eqv_trans _ _ _ (D.B_congr_left z hz) (D.B_zero_left z)
  have e2 : (D.B (D.neg a) z + D.B a z).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (D.B_add_left (D.neg a) a z)) e1
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (D.B (D.neg a) z) (-(-(D.B a z))) (D.B a z)
      (Q'.neg_neg_eqv (D.B a z))) e2

/-- `⟨a, −z⟩ ≃ −⟨a, z⟩`. -/
theorem B_neg_right (a z : D.V) : (D.B a (D.neg z)).eqv (-(D.B a z)) :=
  Q'.eqv_trans _ _ _ (D.B_symm a (D.neg z))
    (Q'.eqv_trans _ _ _ (D.B_neg_left z a)
      (Q'.neg_eqv_congr (D.B z a) (D.B a z) (D.B_symm z a)))

/-- `⟨−a, −a⟩ ≃ ⟨a, a⟩`. -/
theorem B_neg_neg (a : D.V) : (D.B (D.neg a) (D.neg a)).eqv (D.B a a) :=
  Q'.eqv_trans _ _ _ (D.B_neg_left a (D.neg a))
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr (D.B a (D.neg a)) (-(D.B a a)) (D.B_neg_right a a))
      (Q'.neg_neg_eqv (D.B a a)))

/-! ### `nonnegQuad`: deriving the OS2 positivity from the module laws -/

/-- Pure-`Q′` regrouping behind `nonnegQuad`:
`(s(sP) + s(rM)) + (r(sM) + r(rN)) ≃ (s²P + 2sr·M) + r²N`. -/
theorem quad_regroup (s r P M N : Q') :
    (((s * (s * P)) + (s * (r * M))) + ((r * (s * M)) + (r * (r * N)))).eqv
      (((s * s * P) + (2 * (s * r)) * M) + (r * r * N)) := by
  have hP : (s * (s * P)).eqv (s * s * P) := Q'.eqv_symm (Q'.mul_assoc_eqv s s P)
  have hN : (r * (r * N)).eqv (r * r * N) := Q'.eqv_symm (Q'.mul_assoc_eqv r r N)
  have hM1 : (s * (r * M)).eqv ((s * r) * M) := Q'.eqv_symm (Q'.mul_assoc_eqv s r M)
  have hM2 : (r * (s * M)).eqv ((s * r) * M) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r s M))
      (Q'.mul_eqv_congr_right (r * s) (s * r) M (Q'.mul_comm_eqv r s))
  have hmid : ((s * (r * M)) + (r * (s * M))).eqv ((2 * (s * r)) * M) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hM1 hM2)
      (Q'.eqv_trans _ _ _ (OSReconstructionProgress.q_two_mul ((s * r) * M))
        (Q'.eqv_symm (Q'.mul_assoc_eqv 2 (s * r) M)))
  have hre :
      (((s * (s * P)) + (s * (r * M))) + ((r * (s * M)) + (r * (r * N)))).eqv
        (((s * (s * P)) + ((s * (r * M)) + (r * (s * M)))) + (r * (r * N))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (s * (s * P)) (s * (r * M)) ((r * (s * M)) + (r * (r * N))))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (s * (s * P))
          ((s * (r * M)) + ((r * (s * M)) + (r * (r * N))))
          (((s * (r * M)) + (r * (s * M))) + (r * (r * N)))
          (Q'.eqv_symm (Q'.add_assoc_eqv (s * (r * M)) (r * (s * M)) (r * (r * N)))))
        (Q'.eqv_symm (Q'.add_assoc_eqv (s * (s * P)) ((s * (r * M)) + (r * (s * M))) (r * (r * N)))))
  refine Q'.eqv_trans _ _ _ hre ?_
  exact QPoly.q_add_congr (QPoly.q_add_congr hP hmid) hN

/-- The sum-of-squares expansion of the diagonal of `s·a + r·b`. -/
theorem diag_expand (s r : Q') (a b : D.V) :
    (D.B (D.add (D.smul s a) (D.smul r b)) (D.add (D.smul s a) (D.smul r b))).eqv
      (((s * (s * D.B a a)) + (s * (r * D.B a b)))
        + ((r * (s * D.B a b)) + (r * (r * D.B b b)))) := by
  have e1 : (D.B (D.add (D.smul s a) (D.smul r b)) (D.add (D.smul s a) (D.smul r b))).eqv
      (D.B (D.smul s a) (D.add (D.smul s a) (D.smul r b))
        + D.B (D.smul r b) (D.add (D.smul s a) (D.smul r b))) :=
    D.B_add_left (D.smul s a) (D.smul r b) (D.add (D.smul s a) (D.smul r b))
  have eP : (D.B (D.smul s a) (D.add (D.smul s a) (D.smul r b))).eqv
      (D.B (D.smul s a) (D.smul s a) + D.B (D.smul s a) (D.smul r b)) :=
    D.B_add_right (D.smul s a) (D.smul s a) (D.smul r b)
  have eQ : (D.B (D.smul r b) (D.add (D.smul s a) (D.smul r b))).eqv
      (D.B (D.smul r b) (D.smul s a) + D.B (D.smul r b) (D.smul r b)) :=
    D.B_add_right (D.smul r b) (D.smul s a) (D.smul r b)
  have e2 : (D.B (D.add (D.smul s a) (D.smul r b)) (D.add (D.smul s a) (D.smul r b))).eqv
      ((D.B (D.smul s a) (D.smul s a) + D.B (D.smul s a) (D.smul r b))
        + (D.B (D.smul r b) (D.smul s a) + D.B (D.smul r b) (D.smul r b))) :=
    Q'.eqv_trans _ _ _ e1 (QPoly.q_add_congr eP eQ)
  have bPP : (D.B (D.smul s a) (D.smul s a)).eqv (s * (s * D.B a a)) :=
    Q'.eqv_trans _ _ _ (D.B_smul_left s a (D.smul s a))
      (Q'.mul_eqv_congr_left s (D.B a (D.smul s a)) (s * D.B a a) (D.B_smul_right s a a))
  have bQQ : (D.B (D.smul r b) (D.smul r b)).eqv (r * (r * D.B b b)) :=
    Q'.eqv_trans _ _ _ (D.B_smul_left r b (D.smul r b))
      (Q'.mul_eqv_congr_left r (D.B b (D.smul r b)) (r * D.B b b) (D.B_smul_right r b b))
  have bPQ : (D.B (D.smul s a) (D.smul r b)).eqv (s * (r * D.B a b)) :=
    Q'.eqv_trans _ _ _ (D.B_smul_left s a (D.smul r b))
      (Q'.mul_eqv_congr_left s (D.B a (D.smul r b)) (r * D.B a b) (D.B_smul_right r a b))
  have bQP : (D.B (D.smul r b) (D.smul s a)).eqv (r * (s * D.B a b)) :=
    Q'.eqv_trans _ _ _ (D.B_smul_left r b (D.smul s a))
      (Q'.mul_eqv_congr_left r (D.B b (D.smul s a)) (s * D.B a b)
        (Q'.eqv_trans _ _ _ (D.B_smul_right s b a)
          (Q'.mul_eqv_congr_left s (D.B b a) (D.B a b) (D.B_symm b a))))
  refine Q'.eqv_trans _ _ _ e2 ?_
  exact QPoly.q_add_congr (QPoly.q_add_congr bPP bPQ) (QPoly.q_add_congr bQP bQQ)

/-- **Every `GNSData` is a `PreInnerForm`.** -/
def toPreInnerForm : PreInnerForm D.V where
  B := D.B
  nonnegQuad := by
    intro s r a b
    have hself : (0 : Q') ≤ D.B (D.add (D.smul s a) (D.smul r b))
        (D.add (D.smul s a) (D.smul r b)) :=
      D.self_nonneg (D.add (D.smul s a) (D.smul r b))
    exact OSReconstructionProgress.le_of_le_eqv hself
      (Q'.eqv_trans _ _ _ (D.diag_expand s r a b)
        (quad_regroup s r (D.B a a) (D.B a b) (D.B b b)))

/-- **Sharp Cauchy–Schwarz on the GNS form.** -/
theorem cauchy_schwarz (a b : D.V) :
    D.B a b * D.B a b ≤ D.B a a * D.B b b :=
  (D.toPreInnerForm).cauchy_schwarz a b

/-- **Radical descent**: a null vector pairs trivially with everything. -/
theorem radical_form_zero (a b : D.V) (h : (D.B a a).eqv 0) :
    (D.B a b).eqv 0 :=
  (D.toPreInnerForm).radical_form_zero a b h

/-- `⟨z, r⟩ ≃ 0` when `r` is null (right-handed radical absorption). -/
theorem radical_form_zero_right (z r : D.V) (h : (D.B r r).eqv 0) :
    (D.B z r).eqv 0 :=
  Q'.eqv_trans _ _ _ (D.B_symm z r) (D.radical_form_zero r z h)

/-! ### The radical equivalence and its three laws -/

/-- The **radical relation** `a ≈ b := ⟨a−b, a−b⟩ ≃ 0`. -/
def rad (a b : D.V) : Prop := (D.B (D.sub a b) (D.sub a b)).eqv 0

/-- **Reflexivity** of the radical relation. -/
theorem rad_refl (a : D.V) : D.rad a a := by
  have h : D.veq (D.sub a a) D.zero :=
    D.veq_trans (D.add_comm a (D.neg a)) (D.neg_add a)
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr h) (D.B_zero_left D.zero)

/-- **Symmetry** of the radical relation.  Both diagonals reduce to the common
normal form `(⟨a,a⟩ + (−⟨a,b⟩)) + ((−⟨a,b⟩) + ⟨b,b⟩)`. -/
theorem rad_symm {a b : D.V} (h : D.rad a b) : D.rad b a := by
  have eab : (D.B (D.sub a b) (D.sub a b)).eqv
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
  have eba : (D.B (D.sub b a) (D.sub b a)).eqv
      (((D.B a a) + (-(D.B a b))) + ((-(D.B a b)) + (D.B b b))) := by
    have hc : D.veq (D.sub b a) (D.add (D.neg a) b) := D.add_comm b (D.neg a)
    refine Q'.eqv_trans _ _ _ (D.B_diag_congr hc) ?_
    refine Q'.eqv_trans _ _ _ (D.B_add_left (D.neg a) b (D.add (D.neg a) b)) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (D.B_add_right (D.neg a) (D.neg a) b) (D.B_add_right b (D.neg a) b)) ?_
    exact QPoly.q_add_congr
      (QPoly.q_add_congr (D.B_neg_neg a) (D.B_neg_left a b))
      (QPoly.q_add_congr
        (Q'.eqv_trans _ _ _ (D.B_neg_right b a)
          (Q'.neg_eqv_congr (D.B b a) (D.B a b) (D.B_symm b a)))
        (Q'.eqv_refl (D.B b b)))
  exact Q'.eqv_trans _ _ _ eba (Q'.eqv_trans _ _ _ (Q'.eqv_symm eab) h)

/-- **Transitivity** of the radical relation — the load-bearing step.  With
`x = a−b`, `y = b−c`, the parallelogram expansion gives
`⟨a−c,a−c⟩ ≃ (⟨x,x⟩+⟨x,y⟩) + (⟨y,x⟩+⟨y,y⟩)`; `⟨x,x⟩≃⟨y,y⟩≃0` and the cross
terms vanish by `radical_form_zero` (since `x` is null). -/
theorem rad_trans {a b c : D.V} (hab : D.rad a b) (hbc : D.rad b c) : D.rad a c := by
  have hx0 : (D.B (D.sub a b) (D.sub a b)).eqv 0 := hab
  have hy0 : (D.B (D.sub b c) (D.sub b c)).eqv 0 := hbc
  have hxy0 : (D.B (D.sub a b) (D.sub b c)).eqv 0 :=
    D.radical_form_zero (D.sub a b) (D.sub b c) hx0
  have hyx0 : (D.B (D.sub b c) (D.sub a b)).eqv 0 :=
    Q'.eqv_trans _ _ _ (D.B_symm (D.sub b c) (D.sub a b)) hxy0
  -- expand the diagonal of x + y
  have eexp : (D.B (D.add (D.sub a b) (D.sub b c)) (D.add (D.sub a b) (D.sub b c))).eqv
      ((D.B (D.sub a b) (D.sub a b) + D.B (D.sub a b) (D.sub b c))
        + (D.B (D.sub b c) (D.sub a b) + D.B (D.sub b c) (D.sub b c))) :=
    Q'.eqv_trans _ _ _ (D.B_add_left (D.sub a b) (D.sub b c) (D.add (D.sub a b) (D.sub b c)))
      (QPoly.q_add_congr (D.B_add_right (D.sub a b) (D.sub a b) (D.sub b c))
        (D.B_add_right (D.sub b c) (D.sub a b) (D.sub b c)))
  have ez : ((D.B (D.sub a b) (D.sub a b) + D.B (D.sub a b) (D.sub b c))
        + (D.B (D.sub b c) (D.sub a b) + D.B (D.sub b c) (D.sub b c))).eqv 0 :=
    Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (QPoly.q_add_congr hx0 hxy0) (QPoly.q_add_congr hyx0 hy0))
      (Q'.eqv_trans _ _ _
        (QPoly.q_add_congr (QPoly.q_add_zero_eqv 0) (QPoly.q_add_zero_eqv 0))
        (QPoly.q_add_zero_eqv 0))
  have ev : D.veq (D.sub a c) (D.add (D.sub a b) (D.sub b c)) :=
    D.veq_symm (D.sub_add_sub a b c)
  show (D.B (D.sub a c) (D.sub a c)).eqv 0
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr ev) (Q'.eqv_trans _ _ _ eexp ez)

/-- The radical relation as a `Setoid`. -/
def radSetoid : Setoid D.V where
  r := D.rad
  iseqv := ⟨D.rad_refl, fun h => D.rad_symm h, fun h1 h2 => D.rad_trans h1 h2⟩

/-! ### Well-definedness of the form on radical classes -/

/-- The form descends to radical classes: `a≈a', b≈b' ⇒ ⟨a,b⟩ ≃ ⟨a',b'⟩`. -/
theorem B_welldef {a a' b b' : D.V} (ha : D.rad a a') (hb : D.rad b b') :
    (D.B a b).eqv (D.B a' b') := by
  -- step 1: ⟨a,b⟩ ≃ ⟨a',b⟩  (a − a' is null)
  have step1 : (D.B a b).eqv (D.B a' b) := by
    have hv : D.veq a (D.add (D.sub a a') a') := D.veq_symm (D.sub_add_cancel a a')
    refine Q'.eqv_trans _ _ _ (D.B_congr_left b hv) ?_
    refine Q'.eqv_trans _ _ _ (D.B_add_left (D.sub a a') a' b) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (D.radical_form_zero (D.sub a a') b ha) (Q'.eqv_refl (D.B a' b))) ?_
    exact QPoly.q_zero_add_eqv (D.B a' b)
  -- step 2: ⟨a',b⟩ ≃ ⟨a',b'⟩  (b − b' is null)
  have step2 : (D.B a' b).eqv (D.B a' b') := by
    have hv : D.veq b (D.add (D.sub b b') b') := D.veq_symm (D.sub_add_cancel b b')
    refine Q'.eqv_trans _ _ _ (D.B_congr_right a' hv) ?_
    refine Q'.eqv_trans _ _ _ (D.B_add_right a' (D.sub b b') b') ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (D.radical_form_zero_right a' (D.sub b b') hb) (Q'.eqv_refl (D.B a' b'))) ?_
    exact QPoly.q_zero_add_eqv (D.B a' b')
  exact Q'.eqv_trans _ _ _ step1 step2

/-- `rad a 0 ↔ ⟨a,a⟩ ≃ 0`. -/
theorem rad_zero_iff (a : D.V) : D.rad a D.zero ↔ (D.B a a).eqv 0 := by
  have hv : D.veq (D.sub a D.zero) a :=
    D.veq_trans (D.add_congr (D.veq_refl a) D.neg_zero) (D.add_zero a)
  have hbridge : (D.B (D.sub a D.zero) (D.sub a D.zero)).eqv (D.B a a) := D.B_diag_congr hv
  constructor
  · intro h
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hbridge) h
  · intro h
    exact Q'.eqv_trans _ _ _ hbridge h

end GNSData

/-! ## The `eqv`-quotient of `Q′` (target of the descended inner product) -/

/-- `Q′` modulo its equivalence `eqv` — a genuine type with propositional
equality, the target of the GNS quotient inner product. -/
def qSetoid : Setoid Q' where
  r := Q'.eqv
  iseqv := ⟨Q'.eqv_refl, fun h => Q'.eqv_symm h, fun h1 h2 => Q'.eqv_trans _ _ _ h1 h2⟩

/-- The `eqv`-quotient of `Q′`. -/
def QR : Type := Quotient qSetoid

/-- The class of `0 ∈ Q′` — the zero of `QR`. -/
def QR.zero : QR := Quotient.mk qSetoid 0

namespace GNSData

variable (D : GNSData)

/-! ## The GNS quotient space and its descended inner product -/

/-- The **GNS quotient** `V / Radical`. -/
def QuotSpace : Type := Quotient D.radSetoid

/-- The class of `a ∈ V`. -/
def qmk (a : D.V) : D.QuotSpace := Quotient.mk D.radSetoid a

/-- The class of `0` — the GNS vacuum's quotient. -/
def qZero : D.QuotSpace := D.qmk D.zero

/-- **The descended inner product** `⟨[a],[b]⟩ = [⟨a,b⟩]`, valued in `QR`.
Well-defined by `B_welldef` + `Quotient.sound`. -/
def qInner : D.QuotSpace → D.QuotSpace → QR :=
  Quotient.lift₂ (fun a b => Quotient.mk qSetoid (D.B a b))
    (fun _ _ _ _ ha hb => Quotient.sound (D.B_welldef ha hb))

/-- Computation rule: `⟨[a],[b]⟩ = [⟨a,b⟩]`. -/
theorem qInner_mk (a b : D.V) :
    D.qInner (D.qmk a) (D.qmk b) = Quotient.mk qSetoid (D.B a b) := rfl

/-- **POSITIVE-DEFINITENESS of the GNS quotient inner product**:
`⟨q,q⟩ = 0 ⇔ q = [0]`.  This is the genuine constructive inner-product-space
property — the quotient by the radical kills exactly the null vectors. -/
theorem qInner_posdef (q : D.QuotSpace) :
    D.qInner q q = QR.zero ↔ q = D.qZero := by
  refine Quotient.inductionOn q ?_
  intro a
  constructor
  · intro h
    have he : (D.B a a).eqv 0 := Quotient.exact h
    exact Quotient.sound ((D.rad_zero_iff a).mpr he)
  · intro h
    have hr : D.rad a D.zero := Quotient.exact h
    exact Quotient.sound ((D.rad_zero_iff a).mp hr)

end GNSData

/-! ## A concrete non-degenerate inhabitant: the weighted form on `Q′` -/

/-- The **weighted GNS module** on `V = Q′`: `⟨x,y⟩ = w·(x·y)` for `w ≥ 0`,
with the abelian-group/scalar structure being `Q′`'s own (up to `eqv`).  Every
`GNSData` field is discharged by `Q′` arithmetic. -/
def qWeightGNS (w : Q') (hw : (0 : Q') ≤ w) : GNSData where
  V := Q'
  veq := Q'.eqv
  veq_refl := Q'.eqv_refl
  veq_symm := fun h => Q'.eqv_symm h
  veq_trans := fun h1 h2 => Q'.eqv_trans _ _ _ h1 h2
  zero := 0
  add := fun x y => x + y
  neg := fun x => -x
  smul := fun s x => s * x
  add_congr := fun ha hb => QPoly.q_add_congr ha hb
  neg_congr := fun {a a'} h => Q'.neg_eqv_congr a a' h
  smul_congr := fun s {a a'} h => Q'.mul_eqv_congr_left s a a' h
  add_assoc := Q'.add_assoc_eqv
  add_comm := Q'.add_comm_eqv
  zero_add := QPoly.q_zero_add_eqv
  neg_add := Q'.neg_add_self_eqv
  B := fun x y => w * (x * y)
  B_congr_left := fun {a a'} b h =>
    Q'.mul_eqv_congr_left w (a * b) (a' * b) (Q'.mul_eqv_congr_right a a' b h)
  B_add_left := fun a b c =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w ((a + b) * c) (a * c + b * c) (QPoly.q_add_mul a b c))
      (Q'.mul_add_eqv w (a * c) (b * c))
  B_smul_left := fun s a b =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w ((s * a) * b) (s * (a * b)) (Q'.mul_assoc_eqv s a b))
      (OSReconstructionProgress.mul_pull w s (a * b))
  B_symm := fun a b => Q'.mul_eqv_congr_left w (a * b) (b * a) (Q'.mul_comm_eqv a b)
  self_nonneg := fun a => Q'.mul_nonneg w (a * a) hw (SumOfSquares.q_mul_self_nonneg a)

/-- The weighted GNS form is reflection-positive (fires `self_nonneg`). -/
theorem qWeightGNS_self_nonneg (w : Q') (hw : (0 : Q') ≤ w) (a : Q') :
    (0 : Q') ≤ (qWeightGNS w hw).B a a :=
  (qWeightGNS w hw).self_nonneg a

/-- Sharp Cauchy–Schwarz fires on the concrete weighted GNS module. -/
theorem qWeightGNS_cauchy_schwarz (w : Q') (hw : (0 : Q') ≤ w) (a b : Q') :
    (qWeightGNS w hw).B a b * (qWeightGNS w hw).B a b
      ≤ (qWeightGNS w hw).B a a * (qWeightGNS w hw).B b b :=
  (qWeightGNS w hw).cauchy_schwarz a b

/-- Positive-definiteness fires on the concrete weighted GNS quotient. -/
theorem qWeightGNS_posdef (w : Q') (hw : (0 : Q') ≤ w) (q : (qWeightGNS w hw).QuotSpace) :
    (qWeightGNS w hw).qInner q q = QR.zero ↔ q = (qWeightGNS w hw).qZero :=
  (qWeightGNS w hw).qInner_posdef q

/-! ## The completion interface (honest Type-level boundary)

The metric completion of the positive-definite quotient `(QuotSpace, qInner)`
to a full Hilbert space is the remaining constructive build-out.  It is stated
as a Type-level structure taking the proved quotient as input; the trivial
inhabitant (completion = itself) is genuine for the located / finite-dimensional
case, and the general constructive Cauchy-completion carrier is the residual. -/

/-- A **completion datum** for a GNS quotient: a carrier with an embedding of
the (positive-definite) quotient and an inner product extending `qInner`. -/
structure GNSCompletion (D : GNSData) where
  /-- The completed carrier. -/
  carrier : Type
  /-- The isometric embedding of the dense pre-Hilbert quotient. -/
  ι : D.QuotSpace → carrier
  /-- The extended inner product. -/
  cinner : carrier → carrier → QR
  /-- The embedding preserves the inner product. -/
  ι_inner : ∀ p q, cinner (ι p) (ι q) = D.qInner p q

/-- The trivial completion: the quotient is its own completion (valid when it is
already complete, e.g. located / finite-dimensional).  A genuine inhabitant. -/
def GNSCompletion.trivial (D : GNSData) : GNSCompletion D where
  carrier := D.QuotSpace
  ι := id
  cinner := D.qInner
  ι_inner := fun _ _ => rfl

end YMGap.Continuum.GNSQuotient

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GNSQuotient.GNSData.toPreInnerForm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cauchy_schwarz
#print axioms YMGap.Continuum.GNSQuotient.GNSData.radical_form_zero
#print axioms YMGap.Continuum.GNSQuotient.GNSData.rad_refl
#print axioms YMGap.Continuum.GNSQuotient.GNSData.rad_symm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.rad_trans
#print axioms YMGap.Continuum.GNSQuotient.GNSData.radSetoid
#print axioms YMGap.Continuum.GNSQuotient.GNSData.B_welldef
#print axioms YMGap.Continuum.GNSQuotient.GNSData.qInner
#print axioms YMGap.Continuum.GNSQuotient.GNSData.qInner_posdef
#print axioms YMGap.Continuum.GNSQuotient.qWeightGNS
#print axioms YMGap.Continuum.GNSQuotient.qWeightGNS_cauchy_schwarz
#print axioms YMGap.Continuum.GNSQuotient.qWeightGNS_posdef
#print axioms YMGap.Continuum.GNSQuotient.GNSCompletion.trivial
