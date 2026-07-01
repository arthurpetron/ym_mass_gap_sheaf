/-
# The located irrational `U₄` nodes `±(√5±1)/4` — order-4 discrete Chebyshev-`U`
# orthogonality on a GENUINELY-CONSTRUCTED node datum (Track B: located √5 nodes)

The `t > 0` heat-kernel off-diagonal OS2 reduces (`HeatKernelGaussNode`,
`RiemannSOS`) to the Gauss–Chebyshev exactness of the second-kind discrete
orthogonality at the irrational nodes `x_k = cos(kπ/(M+1))` (the roots of `U_M`).
For `M = 4` those nodes are `±(√5+1)/4, ±(√5−1)/4`.  The order-4 file
`ChebGeneralOrtho` reduced order-4 discrete orthogonality to the SINGLE named
residual `LocatedRootPowerSums4 D` — "the located `U₄` roots realize the Newton
first-kind power sums `S₁,…,S₈`" — but stated it for an ARBITRARY
`ChebRootDataT 4`, with the explicit note that (unlike `M = 3`, `√½`) NO located
`M = 4` node datum had been constructed, the node squares `(3 ± √5)/8` being
irrational.

## What this module proves (genuine, axiom-clean, π-free)

  * **The located `√5` real** `sqrt5` (via `CReal.sqrtFrom 5 2`) with its defining
    identity `sqrt5·sqrt5 ≃ 5` (`sqrt5_sq`).  The single nested radical, exactly as
    `ChebLocatedRoots.shalf` was `√½` for `M = 3`.

  * **The located `U₄` nodes** `n1 = (√5+1)/4`, `n2 = (√5−1)/4` and the ± datum
    `node4 = [n1, n2, −n2, −n1]` — the genuine irrational abscissae as constructive
    reals.

  * **`rootData4 : PowerSumCollapse.ChebRootDataT 4`** — THE genuine `M = 4` located
    node datum (the object `ChebGeneralOrtho` could only postulate).  Its three
    proof fields (`uval_zero`, `uval_fold`, `uval_bridge`) are node-generic — the
    `M = 3` `rootData3` proofs, verbatim, since they route through
    `Ucr_approx`/`Tcr_approx` + `PowerSumCollapse.qbridge` with NO property of the
    node used.

  * **`Cheb.T` reflection parity** (`T_reflect`) — `T_j(−t) ≈ T_j(t)` (even `j`),
    `T_j(−t) ≈ −T_j(t)` (odd `j`), a clean paired `Q'` induction (no radicals).

  * **The odd located power sums DISCHARGED** (`Sj_odd`): `S₁ = S₃ = S₅ = S₇ ≃ 0`,
    by the ± pairing `T_j(n) + T_j(−n) ≃ 0` (odd `j`) at the located nodes —
    independent of `√5`, closing HALF of `LocatedRootPowerSums4` unconditionally.

  * **`locatedRootPowerSums4_of_even`** — the full residual `LocatedRootPowerSums4
    rootData4` REDUCED (odd half discharged) to the single sharp even residual
    `EvenLocatedPowerSums4` (`S₂ = S₄ = S₆ = S₈ ≃ −1`), the pure `√5`-quadrature
    arithmetic at the two located node squares `(3 ± √5)/8` (where the Newton
    collapse `ChebGeneralOrtho.order4_powerSum_collapse` already certifies the
    rational bookkeeping).

  * **`order4_orthoCollapse_of_locatedNodes` / `order4_diag_value_of_locatedNodes`**
    — order-4 discrete Chebyshev-`U` orthogonality (diagonal value `(4+1)/2 = 5/2`)
    on the CONSTRUCTED located datum, conditional now only on the concrete even
    residual `EvenLocatedPowerSums4` (was: on the abstract `LocatedRootPowerSums4`
    for an unconstructed `D`).

## Honesty / scope (AGENTS.md Rule 6)

This does NOT close general `M`, and does NOT (here) discharge the even residual
`EvenLocatedPowerSums4` (the `√5` node-square power sums) — it is a named `Prop`,
never `sorry`.  What is genuinely advanced over `ChebGeneralOrtho`: (i) the located
`M = 4` node datum `rootData4` is now CONSTRUCTED (irrational √5 nodes as data);
(ii) the odd half of `LocatedRootPowerSums4` is DISCHARGED unconditionally by
parity; (iii) the residual is narrowed to the single concrete even conjunction on
the constructed datum.  As `ChebGeneralOrtho` notes, this discrete collapse is the
finite Gauss SHADOW of `RiemannSOS.MomentIntegralIdentity`; inhabiting the
strictly-PD heat-kernel `CRealNodeQuadrature` for `t > 0`, `N ≥ 2` remains that
distinct named wall (the measure is `R`-modulated, not plain Chebyshev), re-exported
below.

## Reuse / provenance

The moment-matrix SOS machine is the Mathlib-free constructive transfer of the
external 4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`).  The `ChebRootDataT` node
interface, `PowerSumCollapse`, the general-`M` located assembly
`ChebGeneralOrtho.rootBridge_of_locatedGen`, and the order-4 Newton–Vieta collapse
`ChebGeneralOrtho.order4_powerSum_collapse` are the repo's layers; the `√5` square
root is the repo's constructive Heron iteration `CReal.sqrtFrom`; the order-3
located template is `ChebLocatedRoots.rootData3`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no `decide` on a non-decidable `Prop` (`decide` only on closed
`Q'`/`Nat`).  All node data (`sqrt5`/`n1`/`n2`/`node4`/`rootData4`) are `Type`-level
(MLTT/HoTT-valid); the residual `EvenLocatedPowerSums4` is a `Prop`, never `sorry`.
-/

import YMGap.Continuum.ChebGeneralOrtho

namespace YMGap.Continuum.ChebLocatedRoots4

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebLocatedRoots (Tcr Ucr Tcr_approx Ucr_approx q_fold_back)

local infix:50 " ≈ " => Q'.eqv

/-- Local `Trans` instance so `Q'.eqv` rearrangements can be written as `calc`. -/
local instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. Small `Q'` neg/mul helpers (for the parity induction) -/

/-- `(−a)·(−b) ≈ a·b`. -/
theorem neg_mul_neg_eqv (a b : Q') : ((-a) * (-b)) ≈ (a * b) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) (Q'.neg_neg_eqv (a * b)))

/-- Two-sided additive congruence `a ≈ a' → b ≈ b' → a+b ≈ a'+b'`. -/
theorem qAddC {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : (a + b) ≈ (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha) (Q'.add_eqv_congr_left a' b b' hb)

/-- `(2·(−t))·(−X) ≈ (2·t)·X` (even-step cross term). -/
theorem q_two_negX (t X : Q') : (((2 : Q') * (-t)) * (-X)) ≈ (((2 : Q') * t) * X) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((2 : Q') * (-t)) (-((2 : Q') * t)) (-X) (Q'.mul_neg_eqv 2 t))
    (neg_mul_neg_eqv ((2 : Q') * t) X)

/-- `(2·(−t))·Y ≈ −((2·t)·Y)` (odd-step cross term). -/
theorem q_two_mulX (t Y : Q') : (((2 : Q') * (-t)) * Y) ≈ (-(((2 : Q') * t) * Y)) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((2 : Q') * (-t)) (-((2 : Q') * t)) Y (Q'.mul_neg_eqv 2 t))
    (Q'.neg_mul_eqv ((2 : Q') * t) Y)

/-! ## 1. `Cheb.T` reflection parity `T_j(−t) = (−1)^j T_j(t)`

Paired induction: `T_{2k}(−t) ≈ T_{2k}(t)` and `T_{2k+1}(−t) ≈ −T_{2k+1}(t)`.
The `Q'` cross terms are handled by `q_two_negX` / `q_two_mulX` (no radicals). -/

/-- **Reflection parity of the first-kind Chebyshev polynomials over `Q'`.** -/
theorem T_reflect (t : Q') : ∀ k,
    ((Cheb.T (2 * k) (-t)) ≈ (Cheb.T (2 * k) t))
    ∧ ((Cheb.T (2 * k + 1) (-t)) ≈ (-(Cheb.T (2 * k + 1) t)))
  | 0 => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  | k + 1 => by
      obtain ⟨hE, hO⟩ := T_reflect t k
      -- even at (2k)+2
      have hE2 : (Cheb.T ((2 * k) + 2) (-t)) ≈ (Cheb.T ((2 * k) + 2) t) := by
        rw [Cheb.T_succ_succ (2 * k) (-t), Cheb.T_succ_succ (2 * k) t]
        refine qAddC ?_ (Q'.neg_eqv_congr _ _ hE)
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left ((2 : Q') * (-t)) _ _ hO)
          (q_two_negX t (Cheb.T (2 * k + 1) t))
      -- odd at (2k+1)+2
      have hO2 : (Cheb.T ((2 * k + 1) + 2) (-t)) ≈ (-(Cheb.T ((2 * k + 1) + 2) t)) := by
        rw [Cheb.T_succ_succ (2 * k + 1) (-t), Cheb.T_succ_succ (2 * k + 1) t]
        refine Q'.eqv_trans _ _ _
          (qAddC ?_ (Q'.neg_eqv_congr _ _ hO))
          (Q'.eqv_symm (Q'.neg_add_eqv ((2 : Q') * t * Cheb.T ((2 * k + 1) + 1) t)
            (-(Cheb.T (2 * k + 1) t))))
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left ((2 : Q') * (-t)) _ _ hE2)
          (q_two_mulX t (Cheb.T ((2 * k + 1) + 1) t))
      refine ⟨?_, ?_⟩
      · have h1 : 2 * (k + 1) = (2 * k) + 2 := by omega
        rw [h1]; exact hE2
      · have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
        rw [h2]; exact hO2

/-! ## 2. The located `√5` real and the `U₄` nodes -/

/-- The constructive real `√5` (`a = 5`, `L = 2`, `2·2 = 4 ≤ 5`). -/
def sqrt5 : CReal := CReal.sqrtFrom 5 2 (by decide) (by decide) (by decide)

/-- `sqrt5 · sqrt5 ≃ 5`. -/
theorem sqrt5_sq : CReal.Equiv (CReal.mul sqrt5 sqrt5) (CReal.ofQ' 5) :=
  CReal.sqrtFrom_sq_equiv 5 2 (by decide) (by decide) (by decide)

/-- `1/4`. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- The located node `n1 = (√5 + 1)/4 = cos(π/5)`. -/
def n1 : CReal := CReal.mul (CReal.ofQ' quarter) (CReal.add sqrt5 CReal.cone)

/-- The located node `n2 = (√5 − 1)/4 = cos(2π/5)`. -/
def n2 : CReal := CReal.mul (CReal.ofQ' quarter) (CReal.add sqrt5 (CReal.neg CReal.cone))

/-- The four located `U₄` nodes `[n1, n2, −n2, −n1]` (the ± pairs `±cos(π/5)`,
`±cos(2π/5)`). -/
def node4 : Nat → CReal
  | 0 => n1
  | 1 => n2
  | 2 => CReal.neg n2
  | 3 => CReal.neg n1
  | (_ + 4) => CReal.czero

/-! ## 3. The genuine located `M = 4` node datum `rootData4`

The three proof fields are node-generic (the `rootData3` proofs verbatim): they use
only `Ucr_approx`/`Tcr_approx` and the proved `Q'` weight bridge
`PowerSumCollapse.qbridge`, no property of the node. -/

/-- **THE genuine `M = 4` located node datum** on the irrational nodes `±(√5±1)/4`. -/
def rootData4 : PowerSumCollapse.ChebRootDataT 4 where
  x := node4
  uval := fun p k => Ucr (node4 k) p
  tval := fun p k => Tcr (node4 k) p
  wt := fun k => CReal.add CReal.cone (CReal.neg (CReal.mul (node4 k) (node4 k)))
  uval_zero := fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  uval_fold := fun _ _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => q_fold_back _ _)
  uval_bridge := fun p k => by
    refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
    show PowerSumCollapse.wQ ((node4 k).approx n) * (Ucr (node4 k) p).approx n
        ≈ HalfPow.half * ((Tcr (node4 k) p).approx n + (-((Tcr (node4 k) (p + 2)).approx n)))
    rw [Ucr_approx (node4 k) n p, Tcr_approx (node4 k) n p, Tcr_approx (node4 k) n (p + 2)]
    exact PowerSumCollapse.qbridge ((node4 k).approx n) p

/-- The canonical `tval 0 k ≃ 1` for `rootData4` (`T₀ = 1` at every node). -/
theorem rootData4_tval0 (k : Nat) : CReal.Equiv (rootData4.tval 0 k) CReal.cone :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 4. The odd located power sums, DISCHARGED by ± pairing -/

/-- `Tcr (−y) (2m+1) ≃ −(Tcr y (2m+1))` — the located-real shadow of the odd
reflection parity `T_{2m+1}(−t) ≈ −T_{2m+1}(t)`. -/
theorem Tcr_neg_odd (y : CReal) (m : Nat) :
    CReal.Equiv (Tcr (CReal.neg y) (2 * m + 1)) (CReal.neg (Tcr y (2 * m + 1))) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (Tcr (CReal.neg y) (2 * m + 1)).approx n ≈ (-((Tcr y (2 * m + 1)).approx n))
  rw [Tcr_approx (CReal.neg y) n (2 * m + 1), Tcr_approx y n (2 * m + 1)]
  exact (T_reflect (y.approx n) m).2

/-- `Sj rootData4 j` unfolds to the explicit 4-node sum (definitional). -/
theorem Sj4_eq (j : Nat) :
    PowerSumCollapse.Sj rootData4 j
      = CReal.add (CReal.add (CReal.add (CReal.add CReal.czero (Tcr n1 j)) (Tcr n2 j))
          (Tcr (CReal.neg n2) j)) (Tcr (CReal.neg n1) j) := rfl

/-- `((((0 + A) + B) + (−B)) + (−A)) ≈ 0` — the odd ± cancellation. -/
theorem q_cancel4 (A B : Q') : ((((0 : Q') + A) + B) + (-B)) + (-A) ≈ (0 : Q') := by
  rw [Q'.zero_add']
  -- ((A + B) + (-B)) + (-A) ≈ 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv A B (-B))) ?_
  -- (A + (B + (-B))) + (-A) ≈ 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left A (B + (-B)) 0 (Q'.add_neg_self_eqv B))) ?_
  -- (A + 0) + (-A) ≈ 0
  rw [Q'.add_zero']
  exact Q'.add_neg_self_eqv A

/-- **The odd located power sums `S₁ = S₃ = S₅ = S₇ ≃ 0`, UNCONDITIONAL.**  For every
`m`, `Σ_{k<4} T_{2m+1}(x_k) ≃ 0` at the located nodes `±(√5±1)/4`, by the ± pairing
`T_{2m+1}(n) + T_{2m+1}(−n) ≃ 0`.  Independent of `√5`. -/
theorem Sj_odd (m : Nat) :
    CReal.Equiv (PowerSumCollapse.Sj rootData4 (2 * m + 1)) (CReal.ofQ' 0) := by
  rw [Sj4_eq]
  have hN2 : CReal.Equiv (Tcr (CReal.neg n2) (2 * m + 1)) (CReal.neg (Tcr n2 (2 * m + 1))) :=
    Tcr_neg_odd n2 m
  have hN1 : CReal.Equiv (Tcr (CReal.neg n1) (2 * m + 1)) (CReal.neg (Tcr n1 (2 * m + 1))) :=
    Tcr_neg_odd n1 m
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr (Pivot2.equiv_refl _) hN2) hN1) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((((0 : Q') + (Tcr n1 (2 * m + 1)).approx n) + (Tcr n2 (2 * m + 1)).approx n)
          + (-((Tcr n2 (2 * m + 1)).approx n))) + (-((Tcr n1 (2 * m + 1)).approx n))
      ≈ (0 : Q')
  exact q_cancel4 ((Tcr n1 (2 * m + 1)).approx n) ((Tcr n2 (2 * m + 1)).approx n)

/-! ## 5. The sharp even residual and the reduction of `LocatedRootPowerSums4` -/

/-- **The single sharp order-4 EVEN located residual** (`Prop`).  The located `U₄`
roots realize the even Newton first-kind power sums `S₂ = S₄ = S₆ = S₈ ≃ −1` — the
pure `√5`-quadrature arithmetic at the two node squares `(3 ± √5)/8`, over which the
Newton collapse `ChebGeneralOrtho.order4_powerSum_collapse` already certifies the
rational bookkeeping.  Named, never `sorry`. -/
def EvenLocatedPowerSums4 : Prop :=
  CReal.Equiv (PowerSumCollapse.Sj rootData4 2) (CReal.ofQ' (-(1 : Q')))
  ∧ CReal.Equiv (PowerSumCollapse.Sj rootData4 4) (CReal.ofQ' (-(1 : Q')))
  ∧ CReal.Equiv (PowerSumCollapse.Sj rootData4 6) (CReal.ofQ' (-(1 : Q')))
  ∧ CReal.Equiv (PowerSumCollapse.Sj rootData4 8) (CReal.ofQ' (-(1 : Q')))

/-- **The order-4 located residual, REDUCED to its even half.**  With the odd half
(`S₁,S₃,S₅,S₇ ≃ 0`) discharged unconditionally by parity, `LocatedRootPowerSums4
rootData4` follows from the single even residual `EvenLocatedPowerSums4`. -/
theorem locatedRootPowerSums4_of_even (h : EvenLocatedPowerSums4) :
    ChebGeneralOrtho.LocatedRootPowerSums4 rootData4 := by
  obtain ⟨h2, h4, h6, h8⟩ := h
  intro j hj1 hj8
  match j, hj1, hj8 with
  | 0, hj1, _ => exact absurd hj1 (by decide)
  | 1, _, _ => exact Sj_odd 0
  | 2, _, _ => exact h2
  | 3, _, _ => exact Sj_odd 1
  | 4, _, _ => exact h4
  | 5, _, _ => exact Sj_odd 2
  | 6, _, _ => exact h6
  | 7, _, _ => exact Sj_odd 3
  | 8, _, _ => exact h8
  | (n + 9), _, hj8 => exact absurd hj8 (by omega)

/-! ## 6. Order-4 discrete orthogonality on the CONSTRUCTED datum -/

/-- **Order-4 discrete Chebyshev-`U` orthogonality collapse on the located datum.**
`ChebOrthogonality.PowerSumCollapse rootData4.toU` — the all-order single-`U` moment
collapse at the CONSTRUCTED located `M = 4` nodes `±(√5±1)/4`, conditional only on the
concrete even residual `EvenLocatedPowerSums4` (the odd half discharged). -/
theorem order4_orthoCollapse_of_locatedNodes (h : EvenLocatedPowerSums4) :
    ChebOrthogonality.PowerSumCollapse rootData4.toU :=
  ChebGeneralOrtho.order4_orthoCollapse_of_located rootData4 rootData4_tval0
    (locatedRootPowerSums4_of_even h)

/-- **Order-4 discrete orthogonality diagonal value `(4+1)/2 = 5/2` on the located
datum.**  `Σ_{k<4} (1 − x_k²)·U₀(x_k)² = 5/2` at the CONSTRUCTED located nodes
`±(√5±1)/4`, conditional only on `EvenLocatedPowerSums4`. -/
theorem order4_diag_value_of_locatedNodes (h : EvenLocatedPowerSums4) :
    CReal.Equiv (ChebOrthogonality.orthoSum rootData4.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((4 : Int) + 1) 2 (by decide))) :=
  ChebGeneralOrtho.order4_diag_value_of_located rootData4 rootData4_tval0
    (locatedRootPowerSums4_of_even h)

/-! ## 7. The remaining `t > 0` heat-kernel walls (honest re-exports)

The discrete collapse above is the finite Gauss SHADOW of the continuous
heat-kernel moment-integral identity.  Inhabiting the strictly-PD `t > 0`
heat-kernel node quadrature (the `R`-modulated Christoffel measure, NOT the plain
Chebyshev measure) is the distinct named residual `RiemannSOS.MomentIntegralIdentity`
— re-exported here, with the proved reduction to all-order character Gram PSD. -/

/-- **`t > 0` off-diagonal OS2 at all orders, reduced to the Gauss-exactness wall.**
Re-export of `HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp`: the SU(2)
heat-kernel character Gram `coneExp` is PSD at every order `N` given the single
residual `RiemannSOS.MomentIntegralIdentity`, whose finite shadow is the order-4
discrete orthogonality reduced above. -/
theorem heatKernel_t_pos_offdiag_OS2_of_momentIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (GramRed.wilsonMoments t ht)) (N : Nat)
    (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp t ht h N c

end YMGap.Continuum.ChebLocatedRoots4

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebLocatedRoots4.sqrt5_sq
#print axioms YMGap.Continuum.ChebLocatedRoots4.T_reflect
#print axioms YMGap.Continuum.ChebLocatedRoots4.rootData4
#print axioms YMGap.Continuum.ChebLocatedRoots4.Tcr_neg_odd
#print axioms YMGap.Continuum.ChebLocatedRoots4.Sj_odd
#print axioms YMGap.Continuum.ChebLocatedRoots4.locatedRootPowerSums4_of_even
#print axioms YMGap.Continuum.ChebLocatedRoots4.order4_orthoCollapse_of_locatedNodes
#print axioms YMGap.Continuum.ChebLocatedRoots4.order4_diag_value_of_locatedNodes
#print axioms YMGap.Continuum.ChebLocatedRoots4.heatKernel_t_pos_offdiag_OS2_of_momentIntegral
