/-
**The CReal-level Gauss-node quadrature interface for the `t > 0` heat-kernel
off-diagonal OS2** — the constructive-real mirror of `HeatKernelGramSOS`'s
`NodeQuadrature`, carrying the genuinely-irrational Gauss nodes `cos(kπ/(r+1))`
as honest `Type`-level data (character values at the nodes supplied with the
Chebyshev fold recurrence), plus the clean reduction of `t > 0` off-diagonal OS2
to the already-named `RiemannSOS.MomentIntegralIdentity`.

# Why a NEW (CReal) interface is needed for `t > 0`

`HeatKernelNodeQuad` closes off-diagonal OS2 for the *finite-rank positive-type*
cases over `Q'` (rational atomic measures; the `t = 0` δ_e kernel EXACTLY).  It
explicitly does NOT close the genuine `t > 0` heat kernel
`m_s = (s+1)·a^{s(s+2)}`: that moment matrix is strictly positive-definite, so no
finite *rational* atomic measure reproduces it — the classical Gauss–Chebyshev
rule needs the IRRATIONAL nodes `cos(kπ/(r+1))`.  The `Q'` substrate cannot
evaluate `U` at a `CReal` in closed form, so the node values `U_s(x_k)` must be
carried as `CReal` data anchored by the three-term fold (exactly the
`ChebOrthogonality.ChebRootData` pattern).

# What is GENUINELY PROVED here (axiom-clean)

  * `CRealNodeQuadrature M N` — the `CReal` node-quadrature residual carrier:
    `CReal` nodes `x_k`, `CReal` character values `uval s k = U_s(x_k)` (with the
    `uval_zero`/`uval_fold` anchoring to the genuine `U`-recurrence), NONNEGATIVE
    `CReal` weights, and the per-entry **moment reproduction**
    `gram M a b ≃ Σ_{k<r} ω_k·uval_a(x_k)·uval_b(x_k)` required to degree `N`
    (the Gauss `r`-point rule's exactness window).

  * `cNodeQuad_sos` / `cNodeQuad_offdiag_OS2` (**the SOS payoff, a THEOREM**) —
    a line-for-line `CReal` copy of `ChebyshevQuadPSD.momentSquare_node_sos`:
    given a `CRealNodeQuadrature`, the GNS energy `momentSquare M c N` equals the
    node sum-of-squares `Σ_k ω_k·(Σ_a c_a·uval_a(x_k))²`, hence is `≥ 0` for every
    real coefficient vector `c` (`geRat_sos_creal`).  This is the off-diagonal OS2
    of the heat-kernel Gram, sourced from the NONNEGATIVE node weights.

  * `cNodeQuad_moment_nonneg` (**the `hpos` discharge, (b)**) — the reproduced
    single-`U` moment `Σ_k ω_k·U_s(x_k) = cNodeQuadGram … s 0` is `≥ 0`, obtained
    by transporting `GramRed.gram_nonneg` (= `M.m_nonneg`) along `reproduce`.  For
    the heat kernel `M.m_nonneg` IS the proved Bochner positivity
    `ReflectionPositivity.heatKernel_nonnegCharCoeffs`
    (`m_s = dim(s)·e^{−tC₂(s)} ≥ 0`).  So `hpos` is NOT an independent obligation;
    it is Bochner pulled back along `reproduce`.

  * `momentSquarePos_of_cNodeQuadFamily` — a per-order family of node quadratures
    discharges `GramRed.MomentSquarePos` (all-order GNS positivity), hence (via the
    proved algebraic reduction) the all-order character Gram PSD.

  * `order1Quad` / `heatKernel_order1_OS2` — a FULLY-CLOSED concrete instance:
    the order-`1` (constant-observable) node quadrature for ANY moment data (one
    node, weight `m_0`, `U_0 = 1`), inhabiting `CRealNodeQuadrature M 1` outright,
    so `cNodeQuad_offdiag_OS2` fires concretely and gives `coneExp t ht c 1 ≥ 0`
    for the genuine SU(2) heat kernel through the node route.

  * `heatKernel_offdiag_OS2_{momentSquare,gramForm,coneExp}` (**the clean (c)
    reduction**) — `t > 0` off-diagonal OS2 reduced, with NO new node
    construction, to the single existing residual
    `RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht)`: `momentSquare = gramForm`
    (def), `gram` is the Clebsch–Gordan moment sum (def), and
    `RiemannSOS.momentSquarePos_of_momentIntegral` consumes the residual.  The
    `reproduce` field of `CRealNodeQuadrature` is precisely the node-quadrature
    shadow of `MomentIntegralIdentity` (Gauss exactness), reached either as a
    finite node sum (a) or as the `(2/π)·lim_n` Riemann limit (c).

# Honesty / scope (AGENTS.md Rule 6)

This does NOT inhabit `CRealNodeQuadrature (wilsonMoments t ht) N` for `t > 0`
and `N ≥ 2`: the `reproduce` field for the strictly-PD heat-kernel moment matrix
is the genuine Gauss-exactness identity at the irrational nodes `cos(kπ/(r+1))`,
which is exactly the named residual `RiemannSOS.MomentIntegralIdentity` /
`ChebyshevQuadPSD.ChebNodes.gram_eq_node_quadrature`.  What is closed: the CReal
interface, the SOS payoff (off-diagonal OS2 from a quadrature), the `hpos`/Bochner
discharge, the order-`1` instance EXACTLY, and the definitional reduction of the
`t > 0` off-diagonal OS2 scalar onto that single residual.

# Reuse / provenance

The `GramRep`/SOS rearrangement and the moment-matrix machine are the
Mathlib-free constructive transfer of the external 4D-GFF formalization
(Douglas–Hoback–Mei–Nissim, "Formalization of QFT", arXiv:2603.15770; repository
`mrdouglasny/OSforGFF`).  The `CReal` node interface mirrors
`ChebOrthogonality.ChebRootData`; the SOS regrouping mirrors
`ChebyshevQuadPSD.momentSquare_node_sos`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` (inherited from the reused `Q'`/`CReal`
finite-sum algebra and `omega`'s `Nat`/`Int` helpers).  No `Classical.*`, no
`sorryAx`, no `native_decide`, no new axioms.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.RiemannSOS
import YMGap.Continuum.ChebOrthogonality
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.HeatKernelGramSOS
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.HeatKernelGaussNode

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData momentSquare gram gramForm wilsonMoments MomentSquarePos)
open YMGap.Continuum.Pivot2 (equiv_trans add_congr mul_congr mul_congr_right equiv_refl)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A bounded `csum` congruence

`CRealContinuumAlg.csum_congr` requires the termwise `Equiv` at EVERY index; the
node reproduction (`reproduce`) only holds up to the truncation order `N` (the
Gauss `r`-point exactness window).  This bounded variant suffices: the `N`-sum
only touches indices `< N`. -/

/-- **Bounded `csum` congruence**: `Σ_{i<n} A i ≃ Σ_{i<n} B i` when `A i ≃ B i`
for every `i < n`. -/
theorem csum_congr_lt {A B : Nat → CReal} (n : Nat)
    (h : ∀ i, i < n → CReal.Equiv (A i) (B i)) :
    CReal.Equiv (CReal.csum A n) (CReal.csum B n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ m ih =>
      show CReal.Equiv (CReal.add (CReal.csum A m) (A m)) (CReal.add (CReal.csum B m) (B m))
      exact add_congr (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h m (Nat.lt_succ_self m))

/-! ## 1. The pointwise `Q'` rearrangement behind the node block

The single commutative-ring identity behind each per-node block:
`w·((c_a·U_a)·(c_b·U_b)) ≃ (c_a c_b)·(w·(U_a·U_b))`.  Five rational factors;
both sides normalise to `((((w·c_a)·c_b)·U_a)·U_b)`. -/

/-- `(p·x)·y ≃ (p·y)·x` over `Q'` (swap the last two factors). -/
theorem q_swap_last (p x y : Q') : ((p * x) * y) ≈ ((p * y) * x) := by
  calc ((p * x) * y)
      ≈ (p * (x * y)) := Q'.mul_assoc_eqv p x y
    _ ≈ (p * (y * x)) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv x y)
    _ ≈ ((p * y) * x) := Q'.eqv_symm (Q'.mul_assoc_eqv p y x)

/-- **The node-block scalar identity** `w·((c_a·U_a)·(c_b·U_b)) ≃ (c_a c_b)·(w·(U_a·U_b))`. -/
theorem cblock_q (w ca cb ua ub : Q') :
    (w * ((ca * ua) * (cb * ub))) ≈ ((ca * cb) * (w * (ua * ub))) := by
  have hL : (w * ((ca * ua) * (cb * ub))) ≈ ((((w * ca) * cb) * ua) * ub) := by
    calc (w * ((ca * ua) * (cb * ub)))
        ≈ ((w * (ca * ua)) * (cb * ub)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv w (ca * ua) (cb * ub))
      _ ≈ (((w * ca) * ua) * (cb * ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w ca ua))
      _ ≈ ((((w * ca) * ua) * cb) * ub) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv ((w * ca) * ua) cb ub)
      _ ≈ ((((w * ca) * cb) * ua) * ub) :=
          Q'.mul_eqv_congr_right _ _ _ (q_swap_last (w * ca) ua cb)
  have hR : ((ca * cb) * (w * (ua * ub))) ≈ ((((w * ca) * cb) * ua) * ub) := by
    calc ((ca * cb) * (w * (ua * ub)))
        ≈ (((ca * cb) * w) * (ua * ub)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (ca * cb) w (ua * ub))
      _ ≈ ((w * (ca * cb)) * (ua * ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (ca * cb) w)
      _ ≈ (((w * ca) * cb) * (ua * ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w ca cb))
      _ ≈ ((((w * ca) * cb) * ua) * ub) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv ((w * ca) * cb) ua ub)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## 2. The CReal node-quadrature Gram entry and the residual carrier

`cNodeQuadGram ω uval r a b = Σ_{k<r} ω_k·(uval_a(x_k)·uval_b(x_k))` is the moment
matrix of the discrete `CReal` positive measure `Σ_k ω_k δ_{x_k}` against the
characters, with the node values supplied as data. -/

/-- **The CReal node-quadrature Gram entry**
`G_{ab} = Σ_{k<r} ω_k·(uval_a(x_k)·uval_b(x_k))`. -/
def cNodeQuadGram (ω : Nat → CReal) (uval : Nat → Nat → CReal) (r : Nat) :
    Nat → Nat → CReal :=
  fun a b => CReal.csum (fun k => CReal.mul (ω k)
                (CReal.mul (uval a k) (uval b k))) r

/-- **The `t > 0` residual carrier (Type-level; AGENTS.md Rule 8).**  A finite
`CReal` Gauss quadrature reproducing the heat-kernel moment Gram `gram M`
entrywise to degree `N`: `CReal` nodes `x_k`, `CReal` character values
`uval s k = U_s(x_k)` anchored to the genuine `U`-recurrence (`uval_zero`,
`uval_fold`, exactly `ChebOrthogonality.ChebRootData`), NONNEGATIVE `CReal`
weights, and the moment-reproduction identity for `a, b < N`.

For the genuine `t > 0` heat kernel the nodes are the irrational
`cos(kπ/(r+1))`, so this is carried as data; inhabiting `reproduce` for `N ≥ 2`
is exactly the Gauss-exactness residual `RiemannSOS.MomentIntegralIdentity`. -/
structure CRealNodeQuadrature (M : MomentData) (N : Nat) where
  /-- Number of quadrature nodes (`r ≥ N` for the `r`-point rule's exactness). -/
  r : Nat
  /-- The node abscissae `x_k` (classically `cos(kπ/(r+1))`), as constructive reals. -/
  x : Nat → CReal
  /-- The node character value `uval s k = U_s(x_k)` (constructive real, as data). -/
  uval : Nat → Nat → CReal
  /-- The quadrature weights `ω_k` (constructive real). -/
  weight : Nat → CReal
  /-- The weights are nonnegative (`ω_k = w_k·κ(x_k) ≥ 0`, Christoffel/measure pos). -/
  weight_nonneg : ∀ k, ExpPos.geRat (weight k) 0
  /-- `uval 0 k = U_0(x_k) = 1`. -/
  uval_zero : ∀ k, CReal.Equiv (uval 0 k) CReal.cone
  /-- Per-node fold (Dirichlet-kernel step): `2·x_k·uval_{n+1} = uval_{n+2} + uval_n`. -/
  uval_fold : ∀ n k, CReal.Equiv
    (CReal.mul (CReal.mul (CReal.ofQ' 2) (x k)) (uval (n + 1) k))
    (CReal.add (uval (n + 2) k) (uval n k))
  /-- **Moment reproduction (degree `N`)**: each Gram entry IS the node quadrature
  of the character product, for `a, b < N`. -/
  reproduce : ∀ a b, a < N → b < N →
    CReal.Equiv (gram M a b) (cNodeQuadGram weight uval r a b)

/-! ## 3. The per-node linear functional and the node sum-of-squares -/

/-- The per-node linear functional `L_k = Σ_{a<N} c_a·uval_a(x_k)`. -/
def cNodeLin {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') (k : Nat) : CReal :=
  CReal.csum (fun a => CReal.mul (CReal.ofQ' (c a)) (Q.uval a k)) N

/-- The node sum-of-squares `Σ_{k<r} ω_k·L_k²`. -/
def cNodeSOS {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') : CReal :=
  CReal.csum (fun k =>
    CReal.mul (Q.weight k) (CReal.mul (cNodeLin Q c k) (cNodeLin Q c k))) Q.r

/-- The `(a,b,k)` body of the triple sum from substituting `reproduce` into
`momentSquare`: `(c_a c_b)·(ω_k·(uval_a·uval_b))`. -/
def cFblock {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') (a b k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (c a * c b))
    (CReal.mul (Q.weight k) (CReal.mul (Q.uval a k) (Q.uval b k)))

/-- **`cNodeSOS ≥ 0`** — a `CReal`-weighted sum of squares with nonnegative
weights `ω_k`, by `geRat_sos_creal`. -/
theorem cNodeSOS_nonneg {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') :
    ExpPos.geRat (cNodeSOS Q c) 0 :=
  SumOfSquares.geRat_sos_creal Q.weight (cNodeLin Q c) Q.weight_nonneg Q.r

/-! ## 4. The load-bearing regrouping `momentSquare ≃ cNodeSOS` -/

/-- Per node `k`: the `(a,b)` double sum of `(c_a c_b)·(ω_k·uval_a·uval_b)` equals
`ω_k·L_k²`.  The CReal mirror of `ChebyshevQuadPSD.node_block_eq`: open `L_k²` to
the double sum (`csum_prod_eq`), push `ω_k` inside (`csum_const_mul`), and match
the per-term scalars (`cblock_q`). -/
theorem cNodeBlock {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') (k : Nat) :
    CReal.Equiv (CReal.csum (fun a => CReal.csum (fun b => cFblock Q c a b k) N) N)
      (CReal.mul (Q.weight k) (CReal.mul (cNodeLin Q c k) (cNodeLin Q c k))) := by
  have hL : CReal.Equiv (CReal.mul (cNodeLin Q c k) (cNodeLin Q c k))
      (CReal.csum (fun a => CReal.csum (fun b =>
        CReal.mul (CReal.mul (CReal.ofQ' (c a)) (Q.uval a k))
          (CReal.mul (CReal.ofQ' (c b)) (Q.uval b k))) N) N) :=
    FusionRDFactor.csum_prod_eq (fun a => CReal.mul (CReal.ofQ' (c a)) (Q.uval a k))
      (fun b => CReal.mul (CReal.ofQ' (c b)) (Q.uval b k)) N N
  have hRHS : CReal.Equiv
      (CReal.mul (Q.weight k) (CReal.mul (cNodeLin Q c k) (cNodeLin Q c k)))
      (CReal.csum (fun a => CReal.csum (fun b =>
        CReal.mul (Q.weight k)
          (CReal.mul (CReal.mul (CReal.ofQ' (c a)) (Q.uval a k))
            (CReal.mul (CReal.ofQ' (c b)) (Q.uval b k)))) N) N) := by
    refine equiv_trans (mul_congr_right hL) ?_
    refine equiv_trans (CReal.Equiv.symm
      (CRealContinuumAlg.csum_const_mul (Q.weight k)
        (fun a => CReal.csum (fun b =>
          CReal.mul (CReal.mul (CReal.ofQ' (c a)) (Q.uval a k))
            (CReal.mul (CReal.ofQ' (c b)) (Q.uval b k))) N) N)) ?_
    refine CRealContinuumAlg.csum_congr (fun a => ?_) N
    exact CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (Q.weight k)
      (fun b => CReal.mul (CReal.mul (CReal.ofQ' (c a)) (Q.uval a k))
        (CReal.mul (CReal.ofQ' (c b)) (Q.uval b k))) N)
  refine CReal.Equiv.symm (equiv_trans hRHS ?_)
  refine CRealContinuumAlg.csum_congr (fun a => CRealContinuumAlg.csum_congr (fun b => ?_) N) N
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show (((Q.weight k).approx p) * ((c a * (Q.uval a k).approx p) * (c b * (Q.uval b k).approx p)))
      ≈ ((c a * c b) * ((Q.weight k).approx p * ((Q.uval a k).approx p * (Q.uval b k).approx p)))
  exact cblock_q ((Q.weight k).approx p) (c a) (c b) ((Q.uval a k).approx p) ((Q.uval b k).approx p)

/-- **The load-bearing regrouping — a THEOREM.**  Given a `CRealNodeQuadrature`,
the GNS energy `momentSquare M c N` equals the node sum-of-squares `cNodeSOS`. -/
theorem cNodeQuad_sos {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') :
    CReal.Equiv (momentSquare M c N) (cNodeSOS Q c) := by
  -- Substitute reproduction into each (a,b<N) entry and pull (c_a c_b) inside the k-sum.
  have hsub : CReal.Equiv (momentSquare M c N)
      (CReal.csum (fun a => CReal.csum (fun b =>
        CReal.csum (fun k => cFblock Q c a b k) Q.r) N) N) := by
    show CReal.Equiv (CReal.csum (fun a => CReal.csum (fun b =>
        CReal.mul (CReal.ofQ' (c a * c b)) (gram M a b)) N) N) _
    refine csum_congr_lt N (fun a ha => csum_congr_lt N (fun b hb => ?_))
    exact equiv_trans (mul_congr_right (Q.reproduce a b ha hb))
      (CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (CReal.ofQ' (c a * c b))
        (fun k => CReal.mul (Q.weight k) (CReal.mul (Q.uval a k) (Q.uval b k))) Q.r))
  refine equiv_trans hsub ?_
  -- Interchange the k-sum to the outside (swap (b,k) inside each a, then (a,k)).
  refine equiv_trans
    (CRealContinuumAlg.csum_congr
      (fun a => ChebOrthogonality.csum_swap_creal (fun b k => cFblock Q c a b k) N Q.r) N) ?_
  refine equiv_trans
    (ChebOrthogonality.csum_swap_creal
      (fun a k => CReal.csum (fun b => cFblock Q c a b k) N) N Q.r) ?_
  -- Per node k, the (a,b) block ≃ ω_k·L_k².
  exact CRealContinuumAlg.csum_congr (fun k => cNodeBlock Q c k) Q.r

/-! ## 5. The off-diagonal OS2 payoff (CReal) -/

/-- **Off-diagonal OS2 from the CReal node quadrature — a THEOREM.**  Given a
`CRealNodeQuadrature M N`, the GNS energy `momentSquare M c N` is `≥ 0` for EVERY
real coefficient vector `c` — the full off-diagonal character-product quadratic
form, sourced from the NONNEGATIVE node weights (`momentSquare ≃ cNodeSOS ≥ 0`).
This is the CReal analogue of `HeatKernelGramSOS.qGram_quadForm_nonneg`. -/
theorem cNodeQuad_offdiag_OS2 {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (c : Nat → Q') :
    ExpPos.geRat (momentSquare M c N) 0 :=
  SU3CharFactor.geRat_of_equiv (cNodeQuad_sos Q c) (cNodeSOS_nonneg Q c)

/-- **The `hpos`/Bochner discharge ((b)).**  The reproduced single-`U` moment
`Σ_{k<r} ω_k·U_s(x_k) = cNodeQuadGram … s 0` is `≥ 0`, transported from
`GramRed.gram_nonneg M s 0` (a finite sum of nonnegative moments `m_c ≥ 0`) along
`reproduce`.  So `hpos` is NOT an independent obligation — it is the moment
nonnegativity `M.m_nonneg` pulled back along the reproduction. -/
theorem cNodeQuad_moment_nonneg {M : MomentData} {N : Nat} (Q : CRealNodeQuadrature M N)
    (s : Nat) (hs : s < N) (h0 : 0 < N) :
    ExpPos.geRat (cNodeQuadGram Q.weight Q.uval Q.r s 0) 0 :=
  SU3CharFactor.geRat_of_equiv (CReal.Equiv.symm (Q.reproduce s 0 hs h0))
    (GramRed.gram_nonneg M s 0)

/-- **All-order moment-square positivity from a per-order node family.**  A family
`∀ N, CRealNodeQuadrature M N` discharges `GramRed.MomentSquarePos M` — hence, via
`GramRed.psd_of_momentSquare_nonneg`, the all-order character Gram PSD. -/
theorem momentSquarePos_of_cNodeQuadFamily {M : MomentData}
    (Qf : ∀ N, CRealNodeQuadrature M N) :
    MomentSquarePos M :=
  fun N c => cNodeQuad_offdiag_OS2 (Qf N) c

/-! ## 6. A fully-closed concrete instance: the order-`1` node quadrature

For ANY moment data, the order-`1` (constant-observable) quadrature is the single
node with weight `m_0` and `U_0 = 1`; it inhabits `CRealNodeQuadrature M 1`
outright, so the SOS payoff fires concretely and gives the heat-kernel
order-`1` OS2 through the node route. -/

/-- **The order-`1` node quadrature for any moment data.**  One node, weight
`m_0 ≥ 0`, all character values `1` (only `U_0` is touched at `N = 1`).  The fold
holds at `x = 1` (`2·1·1 = 1 + 1`), and `reproduce` at the single entry is
`gram M 0 0 ≃ m_0 ≃ ω_0·U_0·U_0`. -/
def order1Quad (M : MomentData) : CRealNodeQuadrature M 1 where
  r := 1
  x := fun _ => CReal.cone
  uval := fun _ _ => CReal.cone
  weight := fun _ => M.m 0
  weight_nonneg := fun _ => M.m_nonneg 0
  uval_zero := fun _ => equiv_refl _
  uval_fold := fun _ _ => by
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (((2 : Q') * (1 : Q')) * (1 : Q')) ≈ ((1 : Q') + (1 : Q'))
    decide
  reproduce := by
    intro a b ha hb
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    show CReal.Equiv (CReal.add CReal.czero (M.m 0))
      (CReal.add CReal.czero (CReal.mul (M.m 0) (CReal.mul CReal.cone CReal.cone)))
    refine add_congr (equiv_refl _) ?_
    exact CReal.Equiv.symm
      (equiv_trans (mul_congr_right (CRealAlg.cmul_cone CReal.cone))
        (CRealAlg.cmul_cone (M.m 0)))

/-- **Order-`1` off-diagonal OS2 for the SU(2) heat kernel, through the node
route.**  `coneExp t ht c 1 ≥ 0` for every `c`, obtained by instantiating
`cNodeQuad_offdiag_OS2` on `order1Quad (wilsonMoments t ht)` and transporting along
`momentSquare ≃ coneExp`.  A concrete payoff at `t > 0` from a genuine CReal node
quadrature. -/
theorem heatKernel_order1_OS2 (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c 1) 0 :=
  SU3CharFactor.geRat_of_equiv
    (CReal.Equiv.symm (GramRed.momentSquare_eq_coneExp t ht c 1))
    (cNodeQuad_offdiag_OS2 (order1Quad (wilsonMoments t ht)) c)

/-! ## 7. The clean (c) reduction: `t > 0` off-diagonal OS2 ↦ `MomentIntegralIdentity`

No fresh `t > 0` node construction is needed for the OS2 *scalar*: the off-diagonal
quadratic form IS the GNS energy `momentSquare` that the Riemann route already
reduces to the single residual `RiemannSOS.MomentIntegralIdentity`.  `momentSquare`
= `gramForm` (def) = `WilsonFunctional.coneExp` (def). -/

/-- **(c), `momentSquare` form.**  `t > 0` off-diagonal OS2 of the heat-kernel
moment square reduced to the single residual `MomentIntegralIdentity` (the
Gauss-exactness / `(π/2)`-moment-integral identity). -/
theorem heatKernel_offdiag_OS2_momentSquare (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (momentSquare (wilsonMoments t ht) c N) 0 :=
  RiemannSOS.momentSquarePos_of_momentIntegral (wilsonMoments t ht) h N c

/-- **(c), abstract Gram form.**  The `N×N` character Gram quadratic form
`gramForm` (= the off-diagonal OS2 form) is `≥ 0` at every order, given the single
residual `MomentIntegralIdentity`. -/
theorem heatKernel_offdiag_OS2_gramForm (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (gramForm (wilsonMoments t ht) c N) 0 :=
  GramRed.psd_of_momentSquare_nonneg (wilsonMoments t ht)
    (RiemannSOS.momentSquarePos_of_momentIntegral (wilsonMoments t ht) h) N c

/-- **(c), physical Wilson form.**  The SU(2) heat-kernel character Gram
`WilsonFunctional.coneExp` is positive-semidefinite at every order, given the
single residual `MomentIntegralIdentity` — the `t > 0` off-diagonal OS2 closed
onto the existing Riemann residual with NO new node construction. -/
theorem heatKernel_offdiag_OS2_coneExp (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  RiemannSOS.wilson_gramPSD_of_momentIntegral t ht h N c

end YMGap.Continuum.HeatKernelGaussNode

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelGaussNode.csum_congr_lt
#print axioms YMGap.Continuum.HeatKernelGaussNode.cblock_q
#print axioms YMGap.Continuum.HeatKernelGaussNode.cNodeSOS_nonneg
#print axioms YMGap.Continuum.HeatKernelGaussNode.cNodeBlock
#print axioms YMGap.Continuum.HeatKernelGaussNode.cNodeQuad_sos
#print axioms YMGap.Continuum.HeatKernelGaussNode.cNodeQuad_offdiag_OS2
#print axioms YMGap.Continuum.HeatKernelGaussNode.cNodeQuad_moment_nonneg
#print axioms YMGap.Continuum.HeatKernelGaussNode.momentSquarePos_of_cNodeQuadFamily
#print axioms YMGap.Continuum.HeatKernelGaussNode.order1Quad
#print axioms YMGap.Continuum.HeatKernelGaussNode.heatKernel_order1_OS2
#print axioms YMGap.Continuum.HeatKernelGaussNode.heatKernel_offdiag_OS2_momentSquare
#print axioms YMGap.Continuum.HeatKernelGaussNode.heatKernel_offdiag_OS2_gramForm
#print axioms YMGap.Continuum.HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp
