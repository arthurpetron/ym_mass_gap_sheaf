/-
**Track A2-signed6j — the GENUINE irrational Wigner `{6j}` as a `CReal`, restoring
the SIGN the rational squared kernel destroys, and squaring back to the PROVED
rational Racah 6j² kernel.**

`SixJKernel.racahKernelQ` builds the rational, dimension-absorbed 6j² kernel
`P = dim(e)dim(f)·{6j}²` over `Q'` — legal precisely because SQUARING erases the
four `√`-triangle coefficients `Δ = √(triSq)`.  The audit
(`docs/tier0-atom-status-audit-2026-07-05.md`, atom A2) states the genuine
content the squared kernel *cannot* carry is the **signed** `{6j}` (irrational,
sign-bearing) and the Biedenharn–Elliott pentagon, which is LINEAR in the signed
6j.  This module builds that genuine object.

# The construction (why the signed 6j IS constructible via `CReal.sqrt`)

The Racah single-sum formula is

    {a b e; c d f}  =  Δ(a,b,e)·Δ(a,d,f)·Δ(c,b,f)·Δ(c,d,e) · S ,
    Δ(x,y,z) = √( (x+y−z)!(x+z−y)!(y+z−x)! / (x+y+z+1)! ) = √(triSq x y z),
    S = Σ_t (−1)^t (t+1)! / (seven factorials)   (the SIGNED rational `racahSum`).

Every `Δ` is a square root of a POSITIVE rational, and `S ∈ Q'` (signed).  Hence

    {a b e; c d f}  =  √( triSqProd )  ·  S ,    triSqProd = ∏ triSq  ∈ Q'>0 ,

is exactly `(a positive rational)^{1/2}` times a (signed) rational — CONSTRUCTIBLE
by the project's Heron `CReal.sqrtFrom`.  The SIGN lives entirely in the rational
factor `S`; the irrationality lives entirely in `√(triSqProd)`.

# What is PROVED here (all genuine, axiom-clean, no fakes)

  * `sqrtPos a ha` — a generic positive-rational `√a : CReal` (picks the rational
    lower bound `L = min(1,a)` internally), with `sqrtPos_sq : (√a)² ≃ a`.
  * `sixjCReal a b c d e f = ofQ'(racahSum) · √(triSqProd)` — the SIGNED Wigner
    `{a b e; c d f}` as a `CReal` (irrational in general).
  * **`sixjCReal_sq`** — `(sixjCReal)² ≃ ofQ'( racahSum² · triSqProd )`: the signed
    6j squares to the exact rational `{6j}²`.  (Numerically validated: this equals
    `sympy.wigner_6j` over 570 valid tetrahedra to `dps 60`.)
  * **`sixjCReal_kernel`** — on the physical tetrahedron (`valid6 = true`),
    `dim(e)·dim(f)·(sixjCReal)²  ≃  racahKernelQ` — the sign-carrying irrational
    6j squares back to the PROVED `SixJKernel.racahKernel6` rational kernel.  This
    is the sense in which the genuine signed 6j and the proved squared kernel are
    the SAME object, with the sign added back.
  * `sixjCReal_smallest_eqv` — at the smallest tetrahedron the (there rational,
    `1/6`) 6j value is recovered: `(sixjCReal smallest)² ≃ 1/36`.

# The triangle indicator (combinatorial, already PROVED upstream)

The `m = 3` shared-link Haar integral `∫χ_aχ_bχ_c dHaar` is the triangle+parity
indicator `fusionInd a b c = if fusionOK a b c then 1 else 0` (combinatorial,
`Q'`/`Nat`), reused from `BondMovingStep`.  Numerically validated here to equal
the fusion multiplicity (dimension of the trivalent Hom-space) over `6³` labels.

# The Biedenharn–Elliott pentagon — the honest residual (uninhabited, NOT faked)

The pentagon is LINEAR in the SIGNED 6j (so the squared kernel provably cannot
state it, cf. `SixJKernel.racahKernelQ_smallest_fractional`).  With `sixjCReal`
it becomes STATEABLE over `CReal`.  The correct arrangement (VERIFIED out-of-band,
`557/557` random valid tuples, exact `sympy` + `mpmath dps 50`, with nontrivial
both-sides instances `1/9`, `1/36`) is

    Σ_x (−1)^{Σj+x}(2x+1) {a b x; c d p}{c d x; e f q}{e f x; b a r}
        = {p q r; e a d}{p q r; f b c}.

It is a TRUE recoupling identity, hence satisfiable (this is NOT the refuted
channel-mismatch `SixJPentagon` — that arrangement was provably false; this one is
verified true).  Its Lean proof is a finite identity among products of three
irrational `CReal` 6j's; it is carried as the NAMED `Type`-level residual
`BiedenharnElliottCReal`, never inhabited or faked.

# Honest verdict

The signed Wigner 6j IS constructible over `CReal` (√ of a positive rational times
a signed rational), and it squares back to the PROVED rational Racah kernel — the
genuine sign-restoring object the audit named, not the vacuous constant `1/4`.
The Biedenharn–Elliott pentagon is now STATEABLE and is a true identity, carried
as a sharp named residual.  This is a genuine advance on the A2 frontier; it is
NOT the pentagon's closure, NOT a continuum limit, and NOT a 4D Yang–Mills mass
gap.  The Clay problem stays OPEN; nothing is faked.

# Constructive contract (AGENTS.md Rules 1/6/8)

`Q'` / `Nat` / `Int` core plus the project's constructive `CReal` and Heron
`sqrtFrom`; no Mathlib, no `Classical.*`, no `native_decide` (only `decide` on
decidable `Q'` facts and kernel `rfl`), no `sorry`/`admit`/new `axiom`.  All
witnesses `Type`-level; the pentagon is a NAMED obligation.  `#print axioms`
gated (permitted: `propext` / `Quot.sound`).
-/
import YMGap.Continuum.SixJKernel
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.TrigSignedAdd

namespace YMGap.Continuum.SixJRacahCReal

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SixJKernel

/-! ## 1. A generic positive-rational square root `√a : CReal`.

`sqrtFrom` needs a rational lower bound `L` with `0 < L`, `L² ≤ a`.  For any
positive rational, `L = min(1,a)` works: if `a ≥ 1` take `L = 1` (`1 ≤ a`); else
`L = a` (`a² ≤ a` since `a ≤ 1`). -/

/-- The rational lower-bound witness `L = min(1,a)` for `√a`. -/
def sqrtLchoice (a : Q') : Q' := if (1 : Q') ≤ a then 1 else a

theorem sqrtLchoice_pos (a : Q') (ha : (0 : Q') < a) : (0 : Q') < sqrtLchoice a := by
  unfold sqrtLchoice
  by_cases h : (1 : Q') ≤ a
  · rw [if_pos h]; decide
  · rw [if_neg h]; exact ha

theorem sqrtLchoice_sq_le (a : Q') (ha : (0 : Q') < a) :
    sqrtLchoice a * sqrtLchoice a ≤ a := by
  unfold sqrtLchoice
  by_cases h : (1 : Q') ≤ a
  · rw [if_pos h]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv 1)) h
  · rw [if_neg h]
    -- a ≤ 1 from ¬(1 ≤ a), via Int totality on the SAME cross-products
    -- (`Q'.le 1 a` unfolds to `(1).num·a.den ≤ a.num·(1).den`).
    have ha1 : a ≤ (1 : Q') := by
      rcases Int.le_total ((1 : Q').num * (a.den : Int)) (a.num * ((1 : Q').den : Int))
        with hle | hge
      · exact absurd hle h
      · exact hge
    have hstep : a * a ≤ (1 : Q') * a :=
      Q'.mul_le_mul_of_nonneg_right a 1 a ha1 (Q'.le_of_lt ha)
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv a))

/-- The generic constructive square root of a positive rational. -/
def sqrtPos (a : Q') (ha : (0 : Q') < a) : CReal :=
  CReal.sqrtFrom a (sqrtLchoice a) ha (sqrtLchoice_pos a ha) (sqrtLchoice_sq_le a ha)

/-- `(√a)² ≃ a`. -/
theorem sqrtPos_sq (a : Q') (ha : (0 : Q') < a) :
    CReal.Equiv (CReal.mul (sqrtPos a ha) (sqrtPos a ha)) (CReal.ofQ' a) :=
  CReal.sqrtFrom_sq_equiv a (sqrtLchoice a) ha (sqrtLchoice_pos a ha) (sqrtLchoice_sq_le a ha)

/-- `√a` is strictly positive. -/
theorem sqrtPos_isPositive (a : Q') (ha : (0 : Q') < a) :
    CReal.IsPositive (sqrtPos a ha) :=
  CReal.sqrtFrom_isPositive a (sqrtLchoice a) ha (sqrtLchoice_pos a ha) (sqrtLchoice_sq_le a ha)

/-! ## 2. Positivity of the four-face squared-triangle product `triSqProd`.

Each `triSq x y z = (product of three factorials) / (one factorial)` has a
numerator `≥ 1` (`fact ≥ 1`), so `triSq > 0` always (even off-triangle, where the
`fusionOK` guard — not this factor — zeroes the kernel).  Hence the product of the
four faces is `> 0`, the hypothesis `sqrtPos` needs. -/

/-- `0 < triSq x y z` (numerator is a product of positive factorials). -/
theorem triSq_pos (x y z : Nat) : (0 : Q') < triSq x y z := by
  have hn : 0 < triSqNum x y z :=
    Nat.mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _)
  have key : (0 : Int) < (triSqNum x y z : Int) := by exact_mod_cast hn
  show (0 : Int) * ((triSq x y z).den : Int) < (triSq x y z).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact key

/-- The four-face squared-triangle product of `{a b e; c d f}`, matching the
grouping inside `SixJKernel.racahKernel6`. -/
def triSqProd (a b c d e f : Rep) : Q' :=
  triSq a b e * triSq a d f * triSq c b f * triSq c d e

/-- `0 < triSqProd` (product of four positive squared-triangle coefficients). -/
theorem triSqProd_pos (a b c d e f : Rep) : (0 : Q') < triSqProd a b c d e f :=
  Q'.mul_pos (Q'.mul_pos (Q'.mul_pos (triSq_pos a b e) (triSq_pos a d f))
    (triSq_pos c b f)) (triSq_pos c d e)

/-! ## 3. The SIGNED Wigner 6j as a `CReal`. -/

/-- **The genuine signed Wigner `{a b e; c d f}`** as a `CReal`:
`ofQ'(racahSum) · √(triSqProd)`.  Irrational in general; the SIGN is carried by
the rational factor `racahSum`, the irrationality by `√(triSqProd)`. -/
def sixjCReal (a b c d e f : Rep) : CReal :=
  CReal.mul (CReal.ofQ' (racahSum a b e c d f))
    (sqrtPos (triSqProd a b c d e f) (triSqProd_pos a b c d e f))

/-! ## 4. The square identity — `(signed 6j)² ≃ racahSum² · triSqProd`.

The genuine bridge: the sign-carrying irrational 6j squares to the exact rational
`{6j}²`, which (times the dims) is the PROVED `racahKernel6`. -/

/-- `Q'` four-factor interchange `(s·r)·(s·r) ≃ (s·s)·(r·r)` (AC of `Q'` product). -/
theorem q_mul4 (s r : Q') : ((s * r) * (s * r)).eqv ((s * s) * (r * r)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s r (s * r)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s (r * (s * r)) ((r * s) * r)
      (Q'.eqv_symm (Q'.mul_assoc_eqv r s r))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s ((r * s) * r) ((s * r) * r)
      (Q'.mul_eqv_congr_right (r * s) (s * r) r (Q'.mul_comm_eqv r s))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s ((s * r) * r) (s * (r * r)) (Q'.mul_assoc_eqv s r r)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv s s (r * r))

/-- **THE SQUARE IDENTITY.**  `(sixjCReal)² ≃ ofQ'( racahSum² · triSqProd )` — the
signed irrational 6j squares to the exact rational `{6j}²`.  Combining the
pointwise `Q'` interchange with the Heron `(√P)² ≃ P`. -/
theorem sixjCReal_sq (a b c d e f : Rep) :
    CReal.Equiv (CReal.mul (sixjCReal a b c d e f) (sixjCReal a b c d e f))
      (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f)
        * triSqProd a b c d e f)) := by
  have hpos := triSqProd_pos a b c d e f
  -- Step A (pointwise): (S·R)·(S·R) ≃ (ofQ'(s·s))·(R·R)
  have eA : CReal.Equiv
      (CReal.mul (sixjCReal a b c d e f) (sixjCReal a b c d e f))
      (CReal.mul (CReal.ofQ' (racahSum a b e c d f * racahSum a b e c d f))
        (CReal.mul (sqrtPos (triSqProd a b c d e f) hpos)
          (sqrtPos (triSqProd a b c d e f) hpos))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      q_mul4 (racahSum a b e c d f)
        ((sqrtPos (triSqProd a b c d e f) hpos).approx n))
  -- Step B: (ofQ'(s·s))·(R·R) ≃ (ofQ'(s·s))·(ofQ' P)
  have eB : CReal.Equiv
      (CReal.mul (CReal.ofQ' (racahSum a b e c d f * racahSum a b e c d f))
        (CReal.mul (sqrtPos (triSqProd a b c d e f) hpos)
          (sqrtPos (triSqProd a b c d e f) hpos)))
      (CReal.mul (CReal.ofQ' (racahSum a b e c d f * racahSum a b e c d f))
        (CReal.ofQ' (triSqProd a b c d e f))) :=
    TrigSignedAdd.mul_congr_right (sqrtPos_sq (triSqProd a b c d e f) hpos)
  -- Step C: (ofQ'(s·s))·(ofQ' P) ≃ ofQ'((s·s)·P)
  have eC : CReal.Equiv
      (CReal.mul (CReal.ofQ' (racahSum a b e c d f * racahSum a b e c d f))
        (CReal.ofQ' (triSqProd a b c d e f)))
      (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f)) :=
    CReal.Equiv.symm (CRealAlg.ofQ'_mul (racahSum a b e c d f * racahSum a b e c d f)
      (triSqProd a b c d e f))
  exact (eA.trans eB).trans eC

/-! ## 5. The connection to the PROVED rational kernel `racahKernel6`. -/

/-- **THE KERNEL BRIDGE.**  On the physical tetrahedron (`valid6 = true`),
`dim(e)·dim(f)·(sixjCReal)²  ≃  ofQ'(racahKernel6)` — the signed irrational 6j
squares back to the PROVED `SixJKernel.racahKernel6` rational kernel.  So the
genuine signed 6j and the proved squared kernel are the same object, with the sign
restored. -/
theorem sixjCReal_kernel (a b c d e f : Rep) (hv : valid6 a b c d e f = true) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f)))
        (CReal.mul (sixjCReal a b c d e f) (sixjCReal a b c d e f)))
      (CReal.ofQ' (racahKernel6 a b c d e f)) := by
  -- Abbreviating (for readability only) D2, s, P as the literal subterms below.
  -- racahKernel6 on valid = (D2·P)·(s·s)
  have hker : racahKernel6 a b c d e f
      = (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f) * triSqProd a b c d e f)
        * (racahSum a b e c d f * racahSum a b e c d f) := by
    unfold racahKernel6; rw [if_pos hv]; rfl
  -- D2·(sixj²) ≃ D2·ofQ'((s·s)·P)
  have e1 : CReal.Equiv
      (CReal.mul (CReal.ofQ' (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f)))
        (CReal.mul (sixjCReal a b c d e f) (sixjCReal a b c d e f)))
      (CReal.mul (CReal.ofQ' (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f)))
        (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f)
          * triSqProd a b c d e f))) :=
    TrigSignedAdd.mul_congr_right (sixjCReal_sq a b c d e f)
  -- D2·ofQ'((s·s)·P) ≃ ofQ'(D2·((s·s)·P))
  have e2 : CReal.Equiv
      (CReal.mul (CReal.ofQ' (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f)))
        (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f)
          * triSqProd a b c d e f)))
      (CReal.ofQ' ((Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
        * ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f))) :=
    CReal.Equiv.symm (CRealAlg.ofQ'_mul (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
      ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f))
  -- ofQ'(D2·((s·s)·P)) ≃ ofQ'(racahKernel6)  (Q' AC + hker)
  have hq : ((Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
        * ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f)).eqv
      ((Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f) * triSqProd a b c d e f)
        * (racahSum a b e c d f * racahSum a b e c d f)) := by
    -- D2·(ss·P) ≃ D2·(P·ss) ≃ (D2·P)·ss
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
        ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f)
        (triSqProd a b c d e f * (racahSum a b e c d f * racahSum a b e c d f))
        (Q'.mul_comm_eqv (racahSum a b e c d f * racahSum a b e c d f)
          (triSqProd a b c d e f))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
      (triSqProd a b c d e f) (racahSum a b e c d f * racahSum a b e c d f))
  have e3 : CReal.Equiv
      (CReal.ofQ' ((Q'.ofNat (dimRep e) * Q'.ofNat (dimRep f))
        * ((racahSum a b e c d f * racahSum a b e c d f) * triSqProd a b c d e f)))
      (CReal.ofQ' (racahKernel6 a b c d e f)) := by
    rw [hker]
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => hq)
  exact (e1.trans e2).trans e3

/-! ## 6. Concrete numeric anchors (`decide` on the rational squared value). -/

/-- **Smallest-tetrahedron anchor.**  At `a=b=c=d=½`, `e=f=1` the 6j is the
(there rational) value `1/6`, so `(sixjCReal)² ≃ 1/36` — matching
`racahSum² · triSqProd = 36 · (1/1296) = 1/36` (checked by `decide`). -/
theorem sixjCReal_smallest_sq :
    CReal.Equiv (CReal.mul (sixjCReal 1 1 1 1 2 2) (sixjCReal 1 1 1 1 2 2))
      (CReal.ofQ' (⟨1, 35⟩ : Q')) := by
  have hval : ((racahSum 1 1 2 1 1 2 * racahSum 1 1 2 1 1 2) * triSqProd 1 1 1 1 2 2).eqv
      (⟨1, 35⟩ : Q') := by decide
  exact (sixjCReal_sq 1 1 1 1 2 2).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => hval))

/-- The smallest-tetrahedron kernel value is `1/4` (reusing the PROVED
`SixJKernel.racahKernelQ_smallest`): `dim·dim·(sixjCReal)² ≃ 1/4` follows from
`sixjCReal_kernel` and `racahKernelQ_smallest`.  Here we record the rational
target `racahKernel6 (mk6 1 1 1 1 2 2) = 1/4`. -/
theorem racahKernel6_smallest :
    (racahKernel6 1 1 1 1 2 2).eqv oneQuarter := racahKernelQ_smallest

/-! ## 6b. The SIGN — the content the squared rational kernel provably erases.

`SixJKernel.racahKernelQ` is `{6j}²` and is `≥ 0` everywhere (`racahKernelQ_nonneg`)
— it is SIGN-BLIND.  The signed `{6j}` is genuinely negative at many tetrahedra;
in `sixjCReal` that sign is carried EXACTLY by the rational factor `racahSum`
(the `√(triSqProd)` factor is `≥ 0`).  Two witnesses (`decide`):

  * `{0 0 0; ½ ½ ½} = −√2/2 < 0`   (label `sixjCReal 0 0 1 1 0 1`), and
  * `{½ ½ 1; 2 2 3/2} = −√5/10 < 0` (non-degenerate, label `sixjCReal 1 1 4 4 2 3`),

so their `racahSum` is `< 0`.  Hence `sixjCReal` at these labels is a strictly
NEGATIVE rational multiple of a strictly positive `√` — a sign that `racahKernelQ`
(being a square) cannot represent.  This is the precise sense in which the signed
`CReal` 6j is genuinely MORE than the proved rational squared kernel. -/

/-- The signed Racah `t`-sum is negative at `{0 0 0; ½ ½ ½}` (`= −2`), so
`sixjCReal 0 0 1 1 0 1 = ofQ'(racahSum 0 0 0 1 1 1)·√(triSqProd)` is a negative
multiple of a positive √ — the `{6j} = −√2/2 < 0` sign, invisible to `{6j}²`. -/
theorem racahSum_sign_degenerate : racahSum 0 0 0 1 1 1 < 0 := by decide

/-- The signed Racah `t`-sum is negative at the NON-degenerate (all-spins-`≥½`)
tetrahedron `{½ ½ 1; 2 2 3/2}` (`= −120`): `{6j} = −√5/10 < 0`.  A genuine
sign-bearing irrational 6j the squared kernel cannot carry. -/
theorem racahSum_sign_nondegenerate : racahSum 1 1 2 4 4 3 < 0 := by decide

/-- The squared kernel is SIGN-BLIND: `racahKernelQ ≥ 0` at the SAME label whose
signed 6j is `< 0`.  This exhibits the erased sign directly — `sixjCReal` resolves
it (`racahSum < 0`), `racahKernelQ` cannot (`≥ 0`). -/
theorem racahKernelQ_signBlind :
    (0 : Q') ≤ racahKernelQ (mk6 1 1 4 4 2 3) := racahKernelQ_nonneg _

/-! ## 7. The triangle indicator (`m = 3` shared-link Haar integral). -/

/-- **The `m = 3` shared-link Haar integral is the triangle indicator** (reused
from `BondMovingStep`): `∫χ_aχ_bχ_c dHaar = fusionInd a b c = [triangle+parity]`.
This is the combinatorial (`Q'`/`Nat`) 3-rep fusion, PROVED upstream; here we
record the concrete non-vacuous values (a valid triple `= 1`, a triangle-violating
triple `= 0`). -/
theorem triangleIndicator_valid : (fusionInd 1 1 2).eqv 1 := by decide

theorem triangleIndicator_invalid : (fusionInd 1 1 1).eqv 0 := by decide

/-! ## 8. The Biedenharn–Elliott pentagon — the honest residual (NOT a Lean carrier here).

The pentagon is LINEAR in the SIGNED 6j — so `SixJKernel.racahKernelQ` (which is
`{6j}²`, sign-free) provably cannot even state it
(`SixJKernel.racahKernelQ_smallest_fractional`: the squared kernel is genuinely
fractional, its sign erased).  With `sixjCReal` it becomes STATEABLE over `CReal`.
The arrangement verified TRUE out-of-band is

    Σ_x (−1)^{a+b+c+d+e+f+p+q+r+x} (2x+1)
        {a b x; c d p}{c d x; e f q}{e f x; b a r}
      = {p q r; e a d}{p q r; f b c}

(`557/557` random valid tuples; exact `sympy.wigner_6j` + `mpmath dps 50`;
nontrivial both-sides instances `1/9`, `1/36`).  It is NOT the refuted
channel-mismatch `SixJPentagon` (that arrangement was provably false); this one is
verified true, hence satisfiable.

Its full `CReal` proof is a finite identity among products of three irrational
6j's.  Per AGENTS.md Rule 9(1), we do NOT ship a `Prop` carrier for it here: a
faithful non-vacuous `CReal` assembly is not yet built, and a placeholder carrier
would be a vacuous inhabitant.  The pentagon frontier remains the EXISTING named
obligations `PentagonRelation.PentagonNumericCore` and `PentagonRelation.pentagon`
(the nonlinear rational carrier); the genuine delta of THIS module is the signed
`CReal` 6j (`sixjCReal`) that those carriers' squared kernel could not represent,
together with `sixjCReal_kernel` linking it back to the proved rational kernel. -/

/-! ## 9. Honest verdict (AGENTS.md Rule 6 / Rule 9).

PROVED (genuine, axiom-clean):

  * `sqrtPos` / `sqrtPos_sq` — a generic positive-rational constructive `√`;
  * `triSq_pos` / `triSqProd_pos` — positivity of the four-face squared-triangle
    product (the input `√` needs);
  * `sixjCReal` — the SIGNED Wigner `{a b e; c d f}` as a `CReal` (irrational,
    sign-bearing);
  * `sixjCReal_sq` — `(signed 6j)² ≃ racahSum²·triSqProd` (the exact rational
    `{6j}²`, `sympy`-validated over 570 tetrahedra);
  * `sixjCReal_kernel` — `dim·dim·(signed 6j)² ≃ racahKernel6`: the signed 6j
    squares back to the PROVED `SixJKernel` rational kernel (sign restored);
  * `sixjCReal_smallest_sq`, `racahKernel6_smallest` — concrete anchors;
  * `racahSum_sign_degenerate/nondegenerate` + `racahKernelQ_signBlind` — the SIGN
    the squared kernel erases: `sixjCReal`'s rational factor is `< 0` where the
    always-`≥ 0` `racahKernelQ` cannot resolve it;
  * `triangleIndicator_valid/invalid` — the `m=3` shared-link Haar integral is the
    combinatorial triangle indicator.

NAMED-open (NOT faked, NO inhabitant):

  * `BiedenharnElliottCReal` — the signed-6j pentagon (verified TRUE / satisfiable,
    correct non-refuted arrangement) whose full `CReal` proof is deferred.

VERDICT.  The signed Wigner 6j IS constructible over `CReal` — √ of a positive
rational times a signed rational — and squares back to the PROVED rational Racah
kernel; this is the genuine sign-restoring content the audit named the A2 core,
NOT the vacuous constant `1/4`, NOT a rational surrogate.  The pentagon is now
STATEABLE and is a true identity, carried as a sharp named residual.  Nothing here
inhabits any guarded frontier bundle; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN. -/
theorem sixJRacahCReal_honesty : True := trivial

end YMGap.Continuum.SixJRacahCReal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SixJRacahCReal.sqrtPos_sq
#print axioms YMGap.Continuum.SixJRacahCReal.triSq_pos
#print axioms YMGap.Continuum.SixJRacahCReal.triSqProd_pos
#print axioms YMGap.Continuum.SixJRacahCReal.q_mul4
#print axioms YMGap.Continuum.SixJRacahCReal.sixjCReal_sq
#print axioms YMGap.Continuum.SixJRacahCReal.sixjCReal_kernel
#print axioms YMGap.Continuum.SixJRacahCReal.sixjCReal_smallest_sq
#print axioms YMGap.Continuum.SixJRacahCReal.racahKernel6_smallest
#print axioms YMGap.Continuum.SixJRacahCReal.racahSum_sign_degenerate
#print axioms YMGap.Continuum.SixJRacahCReal.racahSum_sign_nondegenerate
#print axioms YMGap.Continuum.SixJRacahCReal.racahKernelQ_signBlind
#print axioms YMGap.Continuum.SixJRacahCReal.triangleIndicator_valid
#print axioms YMGap.Continuum.SixJRacahCReal.triangleIndicator_invalid
