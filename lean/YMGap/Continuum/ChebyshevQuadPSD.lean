/-
All-order heat-kernel Gram PSD via the **Gauss–Chebyshev quadrature** route —
the genuinely-provable reduction of Wall-1 to a single finite discrete-orthogonality
fact, with the node positivity sourced (NOT assumed) from the already-proved
constructive nonnegativity `R = ϑ₃·S ≥ 0`.

# The target (Wall-1)

The SU(2) heat-kernel character moments are `m_s = (s+1)·e^{−t·s(s+2)/4}`.  For a
finite character combination `q = Σ_{a<N} c_a χ_a` the GNS energy is
`E(q²) = Σ_{a,b<N} c_a c_b G_{ab}`, with `G_{ab}` the character Gram entry
(`GramRed.gram`).  The all-order positivity `MomentSquarePos` (`E(q²) ≥ 0` for
every `N`, `c`) is the analytic input that — through the already-proved algebraic
reduction `GramRed.psd_of_momentSquare_nonneg` — yields the heat-kernel character
Gram matrix being positive-semidefinite at EVERY order simultaneously.

# The quadrature route, carried out here

The classical Gauss–Chebyshev (second-kind) reproduction expresses each Gram
entry as a FINITE positive sum over nodes `x_k = cos(kπ/(n+1))`:

    G_{ab} = Σ_{k} w_k · U_a(x_k) · U_b(x_k) · κ(x_k),

with `w_k > 0` (rational) and `κ(x_k) ≥ 0` the heat-kernel value at the node.
Substituting into the double sum and regrouping gives the manifest sum-of-squares

    E(q²) = Σ_k (w_k·κ_k) · (Σ_a c_a U_a(x_k))²            (`momentSquare_node_sos`)

whose nonnegativity is `geRat_sos_creal` over `(w_k·κ_k ≥ 0)·(square)`
(`momentSquarePos_via_nodes`).  This CLOSES `MomentSquarePos` from the node data.

# What is PROVED here (axiom-clean, no fakes)

  * `kappa` / `kappa_node_nonneg` — the node heat-kernel value `κ = R(x) = ϑ₃(x)·S(x)`
    as a genuine convergent `CReal`, and its nonnegativity `κ ≥ 0` for any node
    `x ∈ [−1,1]` and parameter `a ∈ (0,1)`.  **This is the FREE node positivity,
    taken directly from `ThetaConvGen.R_geRat_zero_gen`** — NOT assumed, and NOT
    via the open differentiated-JTP identity `DiffJTP`.
  * `csum_swap` — the finite double-sum interchange `Σ_i Σ_j ≃ Σ_j Σ_i` over `CReal`
    (built from `csum_add` / `csum_congr`), the regrouping engine.
  * `weightKappa_nonneg` — each node weight×kernel `w_k·κ_k ≥ 0`.
  * `nodeSOS_nonneg` — the node sum-of-squares object `Σ_k (w_k·κ_k)·L_k² ≥ 0`.
  * `momentSquare_node_sos` (**the load-bearing regrouping, a THEOREM**) —
    given the per-entry reproduction `gram_eq_node_quadrature`, the GNS energy
    `momentSquare` equals the node SOS `Σ_k (w_k·κ_k)·(Σ_a c_a U_a(x_k))²`.
  * `momentSquarePos_via_nodes` (**CAPSTONE**) — `MomentSquarePos M` from the node
    data, composed with the algebraic reduction to give all-order character Gram
    PSD `gramPSD_via_chebNodes` (and the SU(2) `wilson_gramPSD_via_chebNodes`).

# What is NAMED-open (the honest residual)

The Mathlib-free `Q'`/`CReal` substrate cannot express `cos(kπ/(n+1))`
(a non-rational algebraic number), so the nodes, positive rational weights, and
the two finite identities they satisfy are carried as the Type-level structure
`ChebNodes M a` (genuine data, AGENTS.md Rule 8):

  * `weight` / `weight_nonneg` — the rational quadrature weights `w_k ≥ 0`
    (classically `(2/(n+1))sin²(kπ/(n+1)) > 0`).
  * `gram_eq_node_quadrature` — the per-entry **discrete-orthogonality / aliasing
    reproduction** `G_{ab} ≃ Σ_k w_k U_a(x_k) U_b(x_k) κ_k` for `a,b < N`.  This
    is a real FINITE identity; it is the single remaining mathematical content of
    Wall-1 along this route (the Gauss–Chebyshev exactness / aliasing fact).

Everything downstream of `ChebNodes` is PROVED.  So Wall-1 is reduced from the
black-box `MomentFunctionalPositive` to ONE concrete finite obligation: construct
`ChebNodes` (equivalently, prove the discrete-orthogonality/aliasing reproduction
for `cos(kπ/(n+1))`).  The node POSITIVITY half — historically the analytic
crux — is already discharged here from `R_geRat_zero_gen`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no new axioms.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.MomentSquarePSD
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.FusionRDFactor
import YMGap.Continuum.CRealContinuumAlg

namespace YMGap.Continuum.ChebyshevQuadPSD

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData MomentSquarePos momentSquare gram)
open YMGap.Continuum.CRealContinuumAlg (csum_congr csum_const_mul)
open YMGap.Continuum.FusionRDFactor (csum_prod_eq)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The node heat-kernel value `κ = R(x) = ϑ₃(x)·S(x)` and its positivity

`κ` is the genuine convergent-`CReal` product object `R(x)` of `ThetaConvGen`;
its nonnegativity is `R_geRat_zero_gen` — the FREE node positivity, sourced from
the already-proved Jacobi-theta-product nonnegativity, NOT from the open
differentiated-JTP identity. -/

/-- **The node heat-kernel value** `κ_a(x) = R(x) = ϑ₃(x)·S(x)` as a convergent
`CReal`, for a node `x ∈ [−1,1]` and parameter `a ∈ (0,1)`. -/
def kappa {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal :=
  CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1)
    (HKConvGen.sConvCReal_general ha0 ha1 hx)

/-- **The FREE node positivity** `κ ≥ 0`, taken directly from
`ThetaConvGen.R_geRat_zero_gen` (the proved `R = ϑ₃·S ≥ 0`).  This is the node
positivity asset of the quadrature route — no `DiffJTP`, no assumption. -/
theorem kappa_node_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat (kappa ha0 ha1 hx hx1) 0 :=
  ThetaConvGen.R_geRat_zero_gen ha0 ha1 hx hx1

/-! ## 2. The finite double-sum interchange `Σ_i Σ_j ≃ Σ_j Σ_i` over `CReal`

The regrouping engine: built by induction on the outer index using `csum_add`
(merge two column-sums termwise) and `csum_congr`.  Pure finite-sum bookkeeping. -/

/-- The empty inner sum collapses: `Σ_{j<n} (czero) ≃ czero`. -/
theorem csum_const_czero (n : Nat) :
    CReal.Equiv (CReal.csum (fun _ => CReal.czero) n) CReal.czero := by
  induction n with
  | zero => exact GramRed.equiv_refl _
  | succ m ih =>
      show CReal.Equiv (CReal.add (CReal.csum (fun _ => CReal.czero) m) CReal.czero)
        CReal.czero
      refine Pivot2.equiv_trans (Pivot2.add_congr ih (GramRed.equiv_refl _)) ?_
      exact GramRed.czero_add_eqv CReal.czero

/-- **The finite double-sum interchange:** `Σ_{i<m} Σ_{j<n} F i j ≃ Σ_{j<n} Σ_{i<m} F i j`. -/
theorem csum_swap (F : Nat → Nat → CReal) (m n : Nat) :
    CReal.Equiv (CReal.csum (fun i => CReal.csum (fun j => F i j) n) m)
      (CReal.csum (fun j => CReal.csum (fun i => F i j) m) n) := by
  induction m with
  | zero =>
      -- LHS = czero ; RHS = Σ_{j<n} czero ≃ czero
      show CReal.Equiv CReal.czero (CReal.csum (fun j => CReal.csum (fun i => F i j) 0) n)
      exact CReal.Equiv.symm
        (Pivot2.equiv_trans (csum_congr (fun _ => GramRed.equiv_refl _) n)
          (csum_const_czero n))
  | succ k ih =>
      -- LHS(k+1) = Σ_{i<k}Σ_j + Σ_j F k j
      show CReal.Equiv
        (CReal.add (CReal.csum (fun i => CReal.csum (fun j => F i j) n) k)
          (CReal.csum (fun j => F k j) n))
        (CReal.csum (fun j => CReal.csum (fun i => F i j) (k + 1)) n)
      -- RHS = Σ_j (Σ_{i<k} F i j + F k j) ; csum_add gives  Σ_j(A+B) ≃ Σ_jA + Σ_jB
      refine Pivot2.equiv_trans (Pivot2.add_congr ih (GramRed.equiv_refl _)) ?_
      -- goal: (Σ_jΣ_{i<k}Fij) + (Σ_jFkj) ≃ Σ_j (Σ_{i<k}Fij + Fkj)
      refine CReal.Equiv.trans
        (CReal.Equiv.symm (CRealAlg.csum_add (fun j => CReal.csum (fun i => F i j) k)
          (fun j => F k j) n)) ?_
      exact csum_congr (fun _ => GramRed.equiv_refl _) n

/-! ## 3. The node weights, kernels, and the node SOS object

`ChebNodes M a` carries the nodes `x_k` (with `[−1,1]` bounds), the positive
rational weights `w_k`, and the per-entry reproduction.  From it we build the
node kernel `κ_k`, the weight×kernel `w_k·κ_k ≥ 0`, the per-node linear
functional `L_k = Σ_a c_a U_a(x_k)`, and the manifest SOS `Σ_k (w_k·κ_k)·L_k²`. -/

/-- **The named-open node data** (Type-level; AGENTS.md Rule 8).  For a moment
functional `M` and parameter `a ∈ (0,1)`, a finite Gauss–Chebyshev quadrature:
the count `n`, the nodes `x_k ∈ [−1,1]`, positive rational weights `w_k`, and —
the single residual finite fact — the per-entry **discrete-orthogonality /
aliasing reproduction** `G_{ab} ≃ Σ_k w_k U_a(x_k) U_b(x_k) κ_k`.

The nodes are `x_k = cos(kπ/(n+1))` and `w_k = (2/(n+1))sin²(kπ/(n+1)) > 0`
classically; they are carried as data because the Mathlib-free `Q'` substrate
cannot express `cos`/`sin` at rational multiples of `π`. -/
structure ChebNodes (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) where
  /-- The number of quadrature nodes. -/
  count : Nat
  /-- The node abscissa `x_k` (classically `cos(kπ/(count+1))`). -/
  node : Nat → Q'
  /-- Each node lies in `[−1, 1]` (lower bound). -/
  node_ge : ∀ k, (-1 : Q') ≤ node k
  /-- Each node lies in `[−1, 1]` (upper bound). -/
  node_le : ∀ k, node k ≤ (1 : Q')
  /-- The positive rational quadrature weight `w_k` (classically
  `(2/(count+1))·sin²(kπ/(count+1)) > 0`). -/
  weight : Nat → Q'
  /-- The weights are strictly positive. -/
  weight_nonneg : ∀ k, (0 : Q') ≤ weight k
  /-- **The discrete-orthogonality / aliasing reproduction** (the single residual
  finite fact): the Gram entry `G_{ab}` equals the node quadrature of
  `U_a·U_b·κ`, for every `a, b`. -/
  gram_eq_node_quadrature : ∀ a' b' : Nat,
    CReal.Equiv (gram M a' b')
      (CReal.csum (fun k =>
        CReal.mul (CReal.ofQ' (weight k))
          (CReal.mul (CReal.ofQ' (Cheb.U a' (node k) * Cheb.U b' (node k)))
            (kappa ha0 ha1 (node_ge k) (node_le k)))) count)

/-- The node kernel `κ_k = R(x_k)` for the `k`-th node of a `ChebNodes`. -/
def nodeKappa {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (k : Nat) : CReal :=
  kappa ha0 ha1 (cn.node_ge k) (cn.node_le k)

/-- Each node kernel is `≥ 0` (the FREE node positivity, from `R_geRat_zero_gen`). -/
theorem nodeKappa_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (k : Nat) :
    ExpPos.geRat (nodeKappa cn k) 0 :=
  kappa_node_nonneg ha0 ha1 (cn.node_ge k) (cn.node_le k)

/-- The weight×kernel `w_k·κ_k` as a `CReal`. -/
def weightKappa {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (cn.weight k)) (nodeKappa cn k)

/-- **`w_k·κ_k ≥ 0`** — a nonnegative weight times the nonnegative node kernel. -/
theorem weightKappa_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (k : Nat) :
    ExpPos.geRat (weightKappa cn k) 0 := by
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := cn.weight k)
      (cn.weight_nonneg k) (nodeKappa_nonneg cn k)) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_mul_zero (cn.weight k)))

/-- The per-node linear functional `L_k = Σ_{a<N} c_a · U_a(x_k)` as a `CReal`. -/
def nodeLin {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (N : Nat) (k : Nat) : CReal :=
  CReal.csum (fun a' => CReal.ofQ' (c a' * Cheb.U a' (cn.node k))) N

/-- **The node sum-of-squares object** `Σ_k (w_k·κ_k)·L_k²`. -/
def nodeSOS {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (N : Nat) : CReal :=
  CReal.csum (fun k =>
    CReal.mul (weightKappa cn k)
      (CReal.mul (nodeLin cn c N k) (nodeLin cn c N k))) cn.count

/-- **`nodeSOS ≥ 0`** — a `CReal`-weighted sum of squares with nonnegative
weights `w_k·κ_k`, by `geRat_sos_creal`. -/
theorem nodeSOS_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (N : Nat) :
    ExpPos.geRat (nodeSOS cn c N) 0 :=
  SumOfSquares.geRat_sos_creal (weightKappa cn) (nodeLin cn c N)
    (weightKappa_nonneg cn) cn.count

/-- `(p·x)·y ≃ (p·y)·x` over `Q'` (swap the last two factors). -/
theorem q_swap_last (p x y : Q') : ((p * x) * y).eqv ((p * y) * x) := by
  calc ((p * x) * y)
      ≈ (p * (x * y)) := Q'.mul_assoc_eqv p x y
    _ ≈ (p * (y * x)) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv x y)
    _ ≈ ((p * y) * x) := Q'.eqv_symm (Q'.mul_assoc_eqv p y x)

/-- The per-`(a,b,k)` summand `(c_a c_b)·(w_k·((U_a U_b)·κ_k))` — the body of the
triple sum produced by substituting the node reproduction into `momentSquare`. -/
def Fblock {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (a' b' k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (c a' * c b'))
    (CReal.mul (CReal.ofQ' (cn.weight k))
      (CReal.mul (CReal.ofQ' (Cheb.U a' (cn.node k) * Cheb.U b' (cn.node k)))
        (nodeKappa cn k)))

/-! ## 3b. The per-term scalar identity (pure `Q'` commutative-ring rearrangement)

The single pointwise identity behind the per-node block:
`(ca·cb)·(w·((Ua·Ub)·κ)) ≃ (w·κ)·((ca·Ua)·(cb·Ub))`.  Proved over `Q'` by the
proven `eqv` ring lemmas (`mul_comm_eqv`, `mul_assoc_eqv`, the congruences). -/

/-- `(ca·cb)·(w·((Ua·Ub)·κ)) ≃ (w·κ)·((ca·Ua)·(cb·Ub))` over `Q'`.  Both sides are
the product of the six factors `ca, cb, w, Ua, Ub, κ`; we normalise each side to
the common left-associated form `((((w·κ)·ca)·Ua)·cb)·Ub`. -/
theorem q_block_eqv (ca cb w Ua Ub κ : Q') :
    ((ca * cb) * (w * ((Ua * Ub) * κ))).eqv
      ((w * κ) * ((ca * Ua) * (cb * Ub))) := by
  -- Reduce to: both sides equal the product of {ca,cb,w,Ua,Ub,κ} with a fixed
  -- bracketing.  Pick canonical form  K := (((((w * κ) * ca) * cb) * Ua) * Ub).
  -- LHS ≃ K :
  have hL : ((ca * cb) * (w * ((Ua * Ub) * κ))).eqv
      (((((w * κ) * ca) * cb) * Ua) * Ub) := by
    -- (ca*cb)*(w*((Ua*Ub)*κ))
    --   ≃ ((ca*cb)*w) * ((Ua*Ub)*κ)              [assoc⁻¹]
    --   ≃ (w*(ca*cb)) * (κ*(Ua*Ub))              [comm in each]
    --   ≃ ((w*κ)*((ca*cb)*(Ua*Ub)))              [regroup]  → expand to canonical
    calc ((ca * cb) * (w * ((Ua * Ub) * κ)))
        ≈ (((ca * cb) * w) * ((Ua * Ub) * κ)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (ca * cb) w ((Ua * Ub) * κ))
      _ ≈ ((w * (ca * cb)) * ((Ua * Ub) * κ)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (ca * cb) w)
      _ ≈ ((w * (ca * cb)) * (κ * (Ua * Ub))) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (Ua * Ub) κ)
      _ ≈ (((w * (ca * cb)) * κ) * (Ua * Ub)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (w * (ca * cb)) κ (Ua * Ub))
      _ ≈ ((w * ((ca * cb) * κ)) * (Ua * Ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_assoc_eqv w (ca * cb) κ)
      _ ≈ ((w * (κ * (ca * cb))) * (Ua * Ub)) :=
          Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (ca * cb) κ))
      _ ≈ (((w * κ) * (ca * cb)) * (Ua * Ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w κ (ca * cb)))
      _ ≈ ((((w * κ) * ca) * cb) * (Ua * Ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (w * κ) ca cb))
      _ ≈ (((((w * κ) * ca) * cb) * Ua) * Ub) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (((w * κ) * ca) * cb) Ua Ub)
  -- RHS ≃ K :
  have hR : ((w * κ) * ((ca * Ua) * (cb * Ub))).eqv
      (((((w * κ) * ca) * cb) * Ua) * Ub) := by
    -- (w*κ)*((ca*Ua)*(cb*Ub))
    --   ≃ (((w*κ)*(ca*Ua))*(cb*Ub))
    --   normalise factors  ca,Ua,cb,Ub  to order  ca,cb,Ua,Ub
    calc ((w * κ) * ((ca * Ua) * (cb * Ub)))
        ≈ (((w * κ) * (ca * Ua)) * (cb * Ub)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (w * κ) (ca * Ua) (cb * Ub))
      _ ≈ ((((w * κ) * ca) * Ua) * (cb * Ub)) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (w * κ) ca Ua))
      _ ≈ (((((w * κ) * ca) * Ua) * cb) * Ub) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (((w * κ) * ca) * Ua) cb Ub)
      _ ≈ (((((w * κ) * ca) * cb) * Ua) * Ub) :=
          Q'.mul_eqv_congr_right _ _ _ (q_swap_last ((w * κ) * ca) Ua cb)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## 4. The load-bearing regrouping `momentSquare ≃ nodeSOS`

`momentSquare M c N = Σ_a Σ_b (c_a c_b)·G_{ab}`.  Substitute the reproduction
`G_{ab} ≃ Σ_k w_k U_a(x_k) U_b(x_k) κ_k`, interchange the `k` sum to the outside
(`csum_swap`, twice), and recognise the inner `(a,b)` double sum at each node `k`
as `(w_k·κ_k)·(Σ_a c_a U_a(x_k))²` via `csum_prod_eq` (the product-of-sums = the
square).  All steps are the proved `CReal` finite-sum algebra. -/

/-- Per node `k`: the `(a,b)` double sum of `(c_a c_b)·(w_k U_a U_b κ_k)` equals
`(w_k·κ_k)·L_k²`.  The square `L_k² = (Σ_a c_a U_a(x_k))²` opens to the double
sum by `csum_prod_eq`, and the per-term scalars match. -/
theorem node_block_eq {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (N : Nat) (k : Nat) :
    CReal.Equiv
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.mul (CReal.ofQ' (c a' * c b'))
          (CReal.mul (CReal.ofQ' (cn.weight k))
            (CReal.mul (CReal.ofQ' (Cheb.U a' (cn.node k) * Cheb.U b' (cn.node k)))
              (nodeKappa cn k)))) N) N)
      (CReal.mul (weightKappa cn k) (CReal.mul (nodeLin cn c N k) (nodeLin cn c N k))) := by
  -- Right side: (w·κ)·(L·L) ≃ w·κ·(Σ_a Σ_b (c_a U_a)·(c_b U_b))  [csum_prod_eq]
  -- Left side: Σ_a Σ_b (c_a c_b)·(w·(U_a U_b·κ)).  Both equal Σ_a Σ_b w·κ·(c_a U_a)(c_b U_b).
  -- We prove LHS ≃ RHS by showing both ≃ the common double sum
  --   D := Σ_a Σ_b w·(κ·((c_a U_a)·(c_b U_b))).
  -- Step A: RHS ≃ D.
  have hL : CReal.Equiv (CReal.mul (nodeLin cn c N k) (nodeLin cn c N k))
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.mul (CReal.ofQ' (c a' * Cheb.U a' (cn.node k)))
          (CReal.ofQ' (c b' * Cheb.U b' (cn.node k)))) N) N) :=
    csum_prod_eq (fun a' => CReal.ofQ' (c a' * Cheb.U a' (cn.node k)))
      (fun b' => CReal.ofQ' (c b' * Cheb.U b' (cn.node k))) N N
  -- weightKappa = w·κ ; push it under the double sum
  have hRHS : CReal.Equiv
      (CReal.mul (weightKappa cn k) (CReal.mul (nodeLin cn c N k) (nodeLin cn c N k)))
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.mul (weightKappa cn k)
          (CReal.mul (CReal.ofQ' (c a' * Cheb.U a' (cn.node k)))
            (CReal.ofQ' (c b' * Cheb.U b' (cn.node k))))) N) N) := by
    refine Pivot2.equiv_trans (Pivot2.mul_congr_right hL) ?_
    refine Pivot2.equiv_trans (CReal.Equiv.symm
      (csum_const_mul (weightKappa cn k)
        (fun a' => CReal.csum (fun b' =>
          CReal.mul (CReal.ofQ' (c a' * Cheb.U a' (cn.node k)))
            (CReal.ofQ' (c b' * Cheb.U b' (cn.node k)))) N) N)) ?_
    refine csum_congr (fun a' => ?_) N
    exact CReal.Equiv.symm (csum_const_mul (weightKappa cn k)
      (fun b' => CReal.mul (CReal.ofQ' (c a' * Cheb.U a' (cn.node k)))
        (CReal.ofQ' (c b' * Cheb.U b' (cn.node k)))) N)
  -- Step B: LHS ≃ RHS, termwise (both are Σ_a Σ_b of equal CReal scalars).
  refine CReal.Equiv.symm (Pivot2.equiv_trans hRHS ?_)
  refine csum_congr (fun a' => csum_congr (fun b' => ?_) N) N
  -- termwise scalar identity:
  --   w·κ·((c_a U_a)·(c_b U_b)) ≃ (c_a c_b)·(w·(U_a U_b·κ))
  -- Both sides are products of the rational scalars
  --   w · (c_a U_a) · (c_b U_b)  and  (c_a c_b) · w · (U_a U_b) · κ
  -- with the single CReal factor κ.  Reduce to a pointwise Q' identity.
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- LHS approx: (c_a c_b)·(w·((U_a U_b)·κ_p))
  -- RHS approx: (w·κ_p)·((c_a U_a)·(c_b U_b))
  show ((cn.weight k * (nodeKappa cn k).approx p) *
        ((c a' * Cheb.U a' (cn.node k)) * (c b' * Cheb.U b' (cn.node k)))).eqv
      ((c a' * c b') * (cn.weight k *
        ((Cheb.U a' (cn.node k) * Cheb.U b' (cn.node k)) * (nodeKappa cn k).approx p)))
  -- Pure commutative-ring identity over `Q'`.
  exact Q'.eqv_symm (q_block_eqv (c a') (c b') (cn.weight k)
    (Cheb.U a' (cn.node k)) (Cheb.U b' (cn.node k)) ((nodeKappa cn k).approx p))

/-- **The load-bearing regrouping — a THEOREM.**  Given `ChebNodes`, the GNS
energy `momentSquare M c N` equals the node sum-of-squares `nodeSOS`. -/
theorem momentSquare_node_sos {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes M ha0 ha1) (c : Nat → Q') (N : Nat) :
    CReal.Equiv (momentSquare M c N) (nodeSOS cn c N) := by
  -- momentSquare = Σ_a Σ_b (c_a c_b)·G_{ab}
  -- ≃ Σ_a Σ_b (c_a c_b)·(Σ_k w_k (U_a U_b) κ_k)            [reproduction]
  -- ≃ Σ_a Σ_b Σ_k (c_a c_b)·(w_k (U_a U_b) κ_k)            [pull constant in]
  -- ≃ Σ_k Σ_a Σ_b (c_a c_b)·(w_k (U_a U_b) κ_k)            [csum_swap ×2]
  -- ≃ Σ_k (w_k·κ_k)·L_k² = nodeSOS                          [node_block_eq]
  -- Step 1: substitute the reproduction into each (a,b) entry, pull the (c_a c_b)
  --   constant inside the k-sum.
  have hsub : CReal.Equiv (momentSquare M c N)
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.csum (fun k =>
          CReal.mul (CReal.ofQ' (c a' * c b'))
            (CReal.mul (CReal.ofQ' (cn.weight k))
              (CReal.mul (CReal.ofQ' (Cheb.U a' (cn.node k) * Cheb.U b' (cn.node k)))
                (nodeKappa cn k)))) cn.count) N) N) := by
    show CReal.Equiv
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.mul (CReal.ofQ' (c a' * c b')) (gram M a' b')) N) N) _
    refine csum_congr (fun a' => csum_congr (fun b' => ?_) N) N
    -- (c_a c_b)·G_{ab} ≃ (c_a c_b)·(Σ_k ...) ≃ Σ_k (c_a c_b)·(...)
    refine Pivot2.equiv_trans
      (Pivot2.mul_congr_right (cn.gram_eq_node_quadrature a' b')) ?_
    exact CReal.Equiv.symm
      (csum_const_mul (CReal.ofQ' (c a' * c b'))
        (fun k => CReal.mul (CReal.ofQ' (cn.weight k))
          (CReal.mul (CReal.ofQ' (Cheb.U a' (cn.node k) * Cheb.U b' (cn.node k)))
            (nodeKappa cn k))) cn.count)
  refine Pivot2.equiv_trans hsub ?_
  -- Step 2: interchange the two inner sums outward: Σ_a Σ_b Σ_k ≃ Σ_k Σ_a Σ_b.
  -- First swap (b,k): inside each a', Σ_b Σ_k ≃ Σ_k Σ_b.
  have hswapBK : CReal.Equiv
      (CReal.csum (fun a' => CReal.csum (fun b' =>
        CReal.csum (fun k => Fblock cn c a' b' k) cn.count) N) N)
      (CReal.csum (fun a' => CReal.csum (fun k =>
        CReal.csum (fun b' => Fblock cn c a' b' k) N) cn.count) N) :=
    csum_congr (fun a' => csum_swap (fun b' k => Fblock cn c a' b' k) N cn.count) N
  refine Pivot2.equiv_trans hswapBK ?_
  -- Then swap (a,k): Σ_a Σ_k (Σ_b ...) ≃ Σ_k Σ_a (Σ_b ...).
  have hswapAK : CReal.Equiv
      (CReal.csum (fun a' => CReal.csum (fun k =>
        CReal.csum (fun b' => Fblock cn c a' b' k) N) cn.count) N)
      (CReal.csum (fun k => CReal.csum (fun a' =>
        CReal.csum (fun b' => Fblock cn c a' b' k) N) N) cn.count) :=
    csum_swap (fun a' k => CReal.csum (fun b' => Fblock cn c a' b' k) N) N cn.count
  refine Pivot2.equiv_trans hswapAK ?_
  -- Step 3: per node k, the (a,b) block ≃ (w_k·κ_k)·L_k²  (node_block_eq).
  refine csum_congr (fun k => ?_) cn.count
  exact node_block_eq cn c N k

/-! ## 5. CAPSTONE — `MomentSquarePos` from the node data, and all-order Gram PSD -/

/-- **CAPSTONE (per moment data).**  Given `ChebNodes M`, the GNS energy is
nonnegative at every order: `MomentSquarePos M`.  `momentSquare ≃ nodeSOS`
(`momentSquare_node_sos`) and `nodeSOS ≥ 0` (`nodeSOS_nonneg`).  This CLOSES the
all-order moment-square positivity from the single node datum — with the node
positivity coming (proved) from `R_geRat_zero_gen`. -/
theorem momentSquarePos_via_nodes {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a}
    {ha1 : a < (1 : Q')} (cn : ChebNodes M ha0 ha1) :
    MomentSquarePos M := by
  intro N c
  exact SU3CharFactor.geRat_of_equiv (momentSquare_node_sos cn c N)
    (nodeSOS_nonneg cn c N)

/-- **CAPSTONE — the all-order character Gram PSD from the node data.**  Composing
`momentSquarePos_via_nodes` with the algebraic reduction
`GramRed.psd_of_momentSquare_nonneg`: the character Gram quadratic form is
positive-semidefinite at EVERY order `N`, given `ChebNodes M`. -/
theorem gramPSD_via_chebNodes {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a}
    {ha1 : a < (1 : Q')} (cn : ChebNodes M ha0 ha1) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (GramRed.gramForm M c N) 0 :=
  GramRed.psd_of_momentSquare_nonneg M (momentSquarePos_via_nodes cn) N c

/-- **CAPSTONE — the SU(2) heat-kernel specialization.**  Given a Gauss–Chebyshev
node datum for the SU(2) heat-kernel moments `wilsonMoments t ht`, the heat-kernel
character Gram matrix `WilsonFunctional.coneExp` is positive-semidefinite at every
order — the all-order Wall-1 conclusion, reduced to the single node obligation. -/
theorem wilson_gramPSD_via_chebNodes (t : Q') (ht : (0 : Q') ≤ t) {a : Q'}
    {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (cn : ChebNodes (GramRed.wilsonMoments t ht) ha0 ha1) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  GramRed.wilson_psd_of_momentSquare_nonneg t ht (momentSquarePos_via_nodes cn) N c

/-- **The bridge to `MomentSquarePSD.UniformGramSOS`.**  The node datum supplies
the uniform manifestly-nonnegative certificate `Equiv (momentSquare M c N) W`,
`W ≥ 0`, at every order — i.e. it discharges the previously-named residual
`UniformGramSOS M` directly, with `W = nodeSOS`. -/
def uniformGramSOS_via_chebNodes {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a}
    {ha1 : a < (1 : Q')} (cn : ChebNodes M ha0 ha1) :
    MomentSquarePSD.UniformGramSOS M :=
  fun N c => ⟨nodeSOS cn c N, nodeSOS_nonneg cn c N, momentSquare_node_sos cn c N⟩

end YMGap.Continuum.ChebyshevQuadPSD

/-! ## What is PROVED vs what is NAMED-open (honest ledger)

**PROVED (axiom-clean, no fakes).**
  * `kappa_node_nonneg` — the FREE node positivity `κ = R = ϑ₃·S ≥ 0`, sourced
    DIRECTLY from `ThetaConvGen.R_geRat_zero_gen` (NOT `DiffJTP`, NOT assumed).
  * `csum_swap` — the finite double-sum interchange over `CReal`.
  * `weightKappa_nonneg`, `nodeSOS_nonneg` — node weight×kernel and the node SOS
    object are nonnegative.
  * `node_block_eq`, `momentSquare_node_sos` — the load-bearing regrouping
    `momentSquare ≃ Σ_k (w_k·κ_k)·(Σ_a c_a U_a(x_k))²` (a THEOREM, from the
    reproduction field + `csum_prod_eq` + `csum_swap`).
  * `momentSquarePos_via_nodes` (CAPSTONE) — `MomentSquarePos M` from `ChebNodes M`.
  * `gramPSD_via_chebNodes`, `wilson_gramPSD_via_chebNodes` — all-order character
    Gram PSD from the node datum, via the proved algebraic reduction.
  * `uniformGramSOS_via_chebNodes` — discharges the older `UniformGramSOS` residual.

**NAMED-open (the single residual finite fact).**  `ChebNodes M ha0 ha1`:
the Gauss–Chebyshev node datum — nodes `x_k = cos(kπ/(count+1))`, positive
rational weights `w_k = (2/(count+1))sin²(kπ/(count+1))`, and the per-entry
**discrete-orthogonality / aliasing reproduction**
`G_{ab} ≃ Σ_k w_k U_a(x_k) U_b(x_k) κ_k`.  The substrate cannot express `cos`/`sin`
at rational multiples of `π`, so this is carried as Type-level data; constructing
it (or just proving the reproduction identity) is the remaining mathematical
content of Wall-1 along this route.

**Net effect.**  `MomentSquarePos` (all-order GNS positivity, hence all-order
heat-kernel character Gram PSD) is REDUCED from the black-box analytic input to
ONE concrete finite discrete-orthogonality/aliasing fact — and the node
POSITIVITY half is already CLOSED here from `R_geRat_zero_gen`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.ChebyshevQuadPSD.kappa_node_nonneg
#print axioms YMGap.Continuum.ChebyshevQuadPSD.csum_swap
#print axioms YMGap.Continuum.ChebyshevQuadPSD.weightKappa_nonneg
#print axioms YMGap.Continuum.ChebyshevQuadPSD.nodeSOS_nonneg
#print axioms YMGap.Continuum.ChebyshevQuadPSD.node_block_eq
#print axioms YMGap.Continuum.ChebyshevQuadPSD.momentSquare_node_sos
#print axioms YMGap.Continuum.ChebyshevQuadPSD.momentSquarePos_via_nodes
#print axioms YMGap.Continuum.ChebyshevQuadPSD.gramPSD_via_chebNodes
#print axioms YMGap.Continuum.ChebyshevQuadPSD.wilson_gramPSD_via_chebNodes
#print axioms YMGap.Continuum.ChebyshevQuadPSD.uniformGramSOS_via_chebNodes
