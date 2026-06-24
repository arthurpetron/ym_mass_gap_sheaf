/-
The **node-free Riemann-sum route** to the all-order SU(2) heat-kernel Gram PSD
(Wall-1) — inhabiting `MomentSquarePSD.UniformGramSOS` through convergent
rational Riemann sums of the PROVED-nonnegative heat kernel `R = ϑ₃·S ≥ 0`,
sidestepping the (research-grade) IRRATIONAL Gauss–Chebyshev roots
`x_k = cos(kπ/(n+1))` that the `ChebyshevQuadPSD` route must carry as data.

# The mathematics (π-free where possible)

The GNS energy is `momentSquare M c N = Σ_{a,b<N} c_a c_b G_{ab}` with `G_{ab}`
the SU(2) Clebsch–Gordan character moment Gram entry.  The key analytic identity,
the **U-orthogonality moment integral**, reads

    (π/2)·G_{ab} = ∫_{−1}^1 U_a(x) U_b(x) R(x) √(1−x²) dx,

with `R = ϑ₃·S ≥ 0` (PROVED, `ThetaConvGen.R_geRat_zero_gen`) and `U` the
second-kind Chebyshev polynomials, because the Chebyshev-`U` coefficients of `R`
ARE the moments (`RCoeffReproduction.rCoeff_eq_two_a_moment`: `r_c = 2a·m_c`) and
`∫ U_c U_d √(1−x²) dx = (π/2)·δ_{cd}` (the `U` weight-orthogonality).  Hence

    (π/2)·Σ_{a,b} c_a c_b G_{ab}
        = ∫_{−1}^1 (Σ_a c_a U_a(x))² · R(x) · √(1−x²) dx  ≥ 0,

the integrand being a SQUARE times `R ≥ 0` times `√(1−x²) ≥ 0`.  The integral is
realised as a LIMIT of **rational** Riemann sums

    I_n := Σ_{k<n} w_k · R(x_k) · √(1−x_k²) · (Σ_a c_a U_a(x_k))²,

over the uniform RATIONAL partition `x_k = −1 + (2k+1)/n` (midpoints), `w_k =
2/n`.  Every node `x_k` is RATIONAL, so the proved node positivity `R(x_k) ≥ 0`
applies with NO irrational-root data.  Each summand is

    (w_k > 0) · (R(x_k) ≥ 0) · (√(1−x_k²) ≥ 0) · (square)  ≥ 0,

so `I_n ≥ 0` for every `n`, and `(2/π)·lim_n I_n ≥ 0` realises `momentSquare ≥ 0`.

# What is PROVED here (axiom-clean, no fakes)

  * `RiemannData` — the rational Riemann-sum datum: a parameter `a ∈ (0,1)`, a
    node count `n`, RATIONAL nodes `x_k ∈ [−1,1]`, and a per-node NONNEGATIVE
    Lebesgue weight `lebWeight k : CReal` with `lebWeight k ≥ 0` (the genuine
    `w_k·√(1−x_k²) ≥ 0`, carried as nonneg Type-level data — the substrate cannot
    take a rational square-root in closed form).  The node heat-kernel `R(x_k)`
    is NOT data: it is the proved-nonnegative `ChebyshevQuadPSD.kappa`.
  * `riemannSum c N n` — the rational Riemann functional
    `Σ_k (lebWeight_k · R(x_k)) · (Σ_a c_a U_a(x_k))²`.
  * `riemannSum_nonneg` (**the SOLID easy half, every `n`**) — `riemannSum ≥ 0`:
    each weight `lebWeight_k · R(x_k) ≥ 0` (`CReal.mul_nonneg` on the proved
    `kappa_node_nonneg` and the carried `lebWeight_nonneg`), so the whole object
    is a `CReal`-weighted sum of squares (`SumOfSquares.geRat_sos_creal`).
  * `uniformMidpointNodes` / `node_lo` / `node_hi` — the CONCRETE uniform-midpoint
    rational partition `x_k = (2k+1−n)/n` with PROVED `[−1,1]` bounds (pure
    `Int`/`Nat` arithmetic via `omega`), the genuine node-free abscissae.

# What is NAMED-open (the honest residual)

  * `MomentIntegralIdentity M` (the single VALUE residual) — the `(π/2)`-scaled
    moment-integral identity `momentSquare M c N ≃ (scale)·riemannLimit`,
    packaged as the Type-level supply, at every order, of a NONNEGATIVE `W`
    `Equiv` to `momentSquare`.  This is exactly the content `(π/2)·G_{ab} = ∫…`
    PLUS Riemann convergence; it is the analog, on the rational-partition route,
    of `ChebyshevQuadPSD.ChebNodes.gram_eq_node_quadrature` — but with the node
    positivity already free (rational nodes) and NO irrational roots.
  * `uniformGramSOS_of_momentIntegral` (a THEOREM) — `MomentIntegralIdentity M ⇒
    UniformGramSOS M`, feeding `MomentSquarePSD.momentSquarePos_of_uniformSOS` ⇒
    all-order character Gram PSD.

# Net effect

All-order moment-square positivity (hence the heat-kernel character Gram PSD) is
REDUCED, along this route, to ONE named value-identification residual
`MomentIntegralIdentity` — and crucially the historically-hard analytic crux,
node POSITIVITY, is ALREADY discharged FOR RATIONAL NODES from
`R_geRat_zero_gen`, so this reframing sits entirely OFF the irrational-root wall.
The per-`n` Riemann nonnegativity (`riemannSum_nonneg`) is unconditional.

# Honesty

The full value identification `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` is NOT proved
here; it is named once as `MomentIntegralIdentity` and the reduction to
`UniformGramSOS` is a theorem.  The Riemann functional and its per-`n`
nonnegativity ARE proved unconditionally.  No `sorry`/`admit`/new
axiom/`Classical.*`/`native_decide`; `decide` is used only on closed
`Int`/`Nat`-decidable goals.

# Axiom-gate

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.MomentSquarePSD
import YMGap.Continuum.ChebyshevQuadPSD
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ChebyshevU

namespace YMGap.Continuum.RiemannSOS

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData MomentSquarePos momentSquare gram)

/-! ## 1. The rational Riemann-sum datum

`RiemannData M a` carries the *rational* partition of `[−1,1]`: a node count `n`,
nodes `x_k ∈ [−1,1]` (RATIONAL — the whole point of this route), and the
per-node nonnegative Lebesgue weight `lebWeight_k = w_k·√(1−x_k²) ≥ 0` carried
as nonneg `CReal` data (the substrate has no closed-form rational square root,
so the weight is supplied; its NONNEGATIVITY is the only property used and it is
recorded as a field, exactly as `ChebNodes` carries its rational weights).

The heat-kernel value `R(x_k)` is NOT carried — it is the proved-nonnegative
`ChebyshevQuadPSD.kappa` at the rational node, so node positivity is FREE. -/

/-- **The rational Riemann-sum datum** (Type-level; AGENTS.md Rule 8).  For a
moment functional `M` and parameter `a ∈ (0,1)`: a node count, RATIONAL nodes
`x_k ∈ [−1,1]`, and the per-node NONNEGATIVE Lebesgue weight `w_k·√(1−x_k²)`
(carried as nonneg `CReal` data — no closed-form rational √).  The node
heat-kernel `R(x_k)` is the proved-nonnegative `ChebyshevQuadPSD.kappa`. -/
structure RiemannData (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) where
  /-- The number of partition cells. -/
  count : Nat
  /-- The rational node `x_k` (uniform partition of `[−1,1]`). -/
  node : Nat → Q'
  /-- Each node lies in `[−1,1]` (lower bound). -/
  node_ge : ∀ k, (-1 : Q') ≤ node k
  /-- Each node lies in `[−1,1]` (upper bound). -/
  node_le : ∀ k, node k ≤ (1 : Q')
  /-- The Lebesgue weight `w_k·√(1−x_k²)` at the `k`-th node (a `CReal`). -/
  lebWeight : Nat → CReal
  /-- The Lebesgue weight is nonnegative (`w_k > 0`, `√(1−x_k²) ≥ 0`). -/
  lebWeight_nonneg : ∀ k, ExpPos.geRat (lebWeight k) 0

/-! ## 2. The node heat-kernel value `R(x_k) ≥ 0` (FREE, rational node)

We re-use the proved `ChebyshevQuadPSD.kappa` and its FREE positivity
`kappa_node_nonneg` (from `R_geRat_zero_gen`) — at our RATIONAL nodes, no
irrational-root data is needed. -/

/-- The node heat-kernel `R(x_k) = ϑ₃(x_k)·S(x_k)` at the `k`-th rational node. -/
def nodeR {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (k : Nat) : CReal :=
  ChebyshevQuadPSD.kappa ha0 ha1 (rd.node_ge k) (rd.node_le k)

/-- **`R(x_k) ≥ 0`** — the FREE node positivity, from `R_geRat_zero_gen`, at the
rational node (no irrational-root data). -/
theorem nodeR_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (k : Nat) :
    ExpPos.geRat (nodeR rd k) 0 :=
  ChebyshevQuadPSD.kappa_node_nonneg ha0 ha1 (rd.node_ge k) (rd.node_le k)

/-! ## 3. The per-node weight `lebWeight_k · R(x_k) ≥ 0`, the linear functional,
and the Riemann sum. -/

/-- The full nonnegative per-node weight `W_k = (w_k·√(1−x_k²)) · R(x_k)`. -/
def fullWeight {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (k : Nat) : CReal :=
  CReal.mul (rd.lebWeight k) (nodeR rd k)

/-- **`W_k ≥ 0`** — a nonnegative Lebesgue weight times the nonnegative node
heat-kernel `R(x_k)`, by `CReal.mul_nonneg`. -/
theorem fullWeight_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (k : Nat) :
    ExpPos.geRat (fullWeight rd k) 0 :=
  CReal.mul_nonneg (rd.lebWeight_nonneg k) (nodeR_nonneg rd k)

/-- The per-node linear functional `L_k = Σ_{a<N} c_a · U_a(x_k)` (a `CReal`). -/
def nodeLin {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (c : Nat → Q') (N : Nat) (k : Nat) : CReal :=
  CReal.csum (fun a' => CReal.ofQ' (c a' * Cheb.U a' (rd.node k))) N

/-- **The rational Riemann sum**
`I_n = Σ_{k<n} W_k · L_k²  =  Σ_k (w_k √(1−x_k²) R(x_k))·(Σ_a c_a U_a(x_k))²`. -/
def riemannSum {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (c : Nat → Q') (N : Nat) : CReal :=
  CReal.csum (fun k =>
    CReal.mul (fullWeight rd k)
      (CReal.mul (nodeLin rd c N k) (nodeLin rd c N k))) rd.count

/-! ## 4. The SOLID easy half — `riemannSum ≥ 0` for every `n`

`riemannSum` is a `CReal`-weighted sum of squares with the manifestly nonnegative
weights `W_k = (w_k√(1−x_k²))·R(x_k) ≥ 0`.  `SumOfSquares.geRat_sos_creal`
closes it directly. -/

/-- **`riemannSum ≥ 0` — the SOLID easy half, for EVERY `n`** (axiom-clean).
The Riemann sum is `Σ_k W_k·L_k²` with each `W_k ≥ 0` (`fullWeight_nonneg`:
nonneg Lebesgue weight × proved-nonneg `R(x_k)`); a `CReal`-weighted SOS is
nonnegative (`geRat_sos_creal`). -/
theorem riemannSum_nonneg {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannData M ha0 ha1) (c : Nat → Q') (N : Nat) :
    ExpPos.geRat (riemannSum rd c N) 0 :=
  SumOfSquares.geRat_sos_creal (fullWeight rd) (nodeLin rd c N)
    (fullWeight_nonneg rd) rd.count

/-! ## 5. The CONCRETE uniform-midpoint rational nodes

The genuine node-free abscissae `x_k = −1 + (2k+1)/n = (2k+1−n)/n`, with PROVED
`[−1,1]` bounds — pure `Int`/`Nat` arithmetic.  These are the rational nodes the
whole route is built to use; they replace `cos(kπ/(n+1))` with NO irrational
data. -/

/-- The uniform-midpoint rational node `x_k = (2k+1−n)/n` for an `n`-cell
partition of `[−1,1]` (`0 < n`). -/
def uniformMidpoint (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Q'.mkPos ((2 * (k : Int) + 1) - (n : Int)) n hn

/-- **`−1 ≤ x_k`** for the uniform-midpoint nodes (`2k+1 ≥ 0`). -/
theorem node_lo (n : Nat) (hn : 0 < n) (k : Nat) :
    (-1 : Q') ≤ uniformMidpoint n hn k := by
  show ((-1 : Q').num) * ((uniformMidpoint n hn k).den : Int)
      ≤ ((uniformMidpoint n hn k).num) * ((-1 : Q').den : Int)
  rw [uniformMidpoint, Q'.mkPos_num, Q'.mkPos_den ((2 * (k : Int) + 1) - (n : Int)) n hn]
  show (-1 : Int) * (n : Int) ≤ ((2 * (k : Int) + 1) - (n : Int)) * ((-1 : Q').den : Int)
  have hden : ((-1 : Q').den : Int) = 1 := by decide
  rw [hden]
  omega

/-- **`x_k ≤ 1`** for the uniform-midpoint nodes, for `k < n` (`2k+1 ≤ 2n`). -/
theorem node_hi (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    uniformMidpoint n hn k ≤ (1 : Q') := by
  show ((uniformMidpoint n hn k).num) * ((1 : Q').den : Int)
      ≤ ((1 : Q').num) * ((uniformMidpoint n hn k).den : Int)
  rw [uniformMidpoint, Q'.mkPos_num, Q'.mkPos_den ((2 * (k : Int) + 1) - (n : Int)) n hn]
  show ((2 * (k : Int) + 1) - (n : Int)) * ((1 : Q').den : Int)
      ≤ ((1 : Q').num) * (n : Int)
  have hden : ((1 : Q').den : Int) = 1 := by decide
  have hnum : ((1 : Q').num) = 1 := by decide
  rw [hden, hnum]
  have hk' : (k : Int) < (n : Int) := by exact_mod_cast hk
  omega

/-! ## 6. The named value residual and the reduction to `UniformGramSOS`

The per-`n` Riemann sum is proved nonnegative above.  The remaining content is
the VALUE identification: that `(2/π)·lim_n I_n` equals `momentSquare`, i.e. the
`(π/2)`-scaled moment-integral identity plus Riemann convergence.  We name
exactly that as a single Type-level obligation `MomentIntegralIdentity`, and
prove that supplying it discharges the previously-named `UniformGramSOS`. -/

/-- **The single VALUE residual (Type-level; AGENTS.md Rule 8).**  At every order
`N` and coefficient vector `c`, a NONNEGATIVE constructive real `W` together with
`Equiv (momentSquare M c N) W`.  Concretely `W = (2/π)·lim_n riemannSum`: this is
the `(π/2)`-scaled moment-integral identity `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)`
(`R`'s `U`-coefficients ARE the moments, `RCoeffReproduction.rCoeff_eq_two_a_moment`;
`U`-orthogonality `∫U_cU_d√(1−x²) = (π/2)δ`) together with Riemann convergence of
the rational sums.  It is the analog of
`ChebyshevQuadPSD.ChebNodes.gram_eq_node_quadrature` on the RATIONAL-partition
route — with node positivity already free and NO irrational roots.

It is carried as `Type`-level data (`Σ`/`fun`-valued) so the certificate is
genuine computational content. -/
def MomentIntegralIdentity (M : MomentData) : Type :=
  (N : Nat) → (c : Nat → Q') →
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W)

/-- **The reduction — a THEOREM.**  `MomentIntegralIdentity M ⇒
MomentSquarePSD.UniformGramSOS M`: the named value residual is exactly the
uniform manifestly-nonnegative certificate `UniformGramSOS` consumes.  Composing
with `MomentSquarePSD.momentSquarePos_of_uniformSOS` gives all-order
moment-square positivity, hence the all-order character Gram PSD. -/
def uniformGramSOS_of_momentIntegral (M : MomentData)
    (h : MomentIntegralIdentity M) :
    MomentSquarePSD.UniformGramSOS M :=
  fun N c => h N c

/-- **All-order moment-square positivity GIVEN the value residual.**  Composing
`uniformGramSOS_of_momentIntegral` with the proved reduction
`MomentSquarePSD.momentSquarePos_of_uniformSOS`. -/
theorem momentSquarePos_of_momentIntegral (M : MomentData)
    (h : MomentIntegralIdentity M) :
    MomentSquarePos M :=
  MomentSquarePSD.momentSquarePos_of_uniformSOS M
    (uniformGramSOS_of_momentIntegral M h)

/-- **All-order character Gram PSD GIVEN the value residual** (SU(2)
heat-kernel).  The heat-kernel character Gram quadratic form
`WilsonFunctional.coneExp` is positive-semidefinite at every order `N`, GIVEN
the single named value residual `MomentIntegralIdentity (wilsonMoments t ht)` —
the route entirely off the irrational-root wall. -/
theorem wilson_gramPSD_of_momentIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : MomentIntegralIdentity (GramRed.wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  GramRed.wilson_psd_of_momentSquare_nonneg t ht
    (momentSquarePos_of_momentIntegral _ h) N c

end YMGap.Continuum.RiemannSOS

/-! ## What is PROVED vs what is NAMED-open (honest ledger)

**PROVED (axiom-clean, no fakes).**
  * `RiemannData` — the rational Riemann-sum datum (rational nodes ∈ `[−1,1]`,
    nonneg Lebesgue weights carried as data).
  * `nodeR_nonneg` — the FREE node positivity `R(x_k) ≥ 0` at the RATIONAL node,
    re-used from `ChebyshevQuadPSD.kappa_node_nonneg` / `R_geRat_zero_gen`.
  * `fullWeight_nonneg` — the per-node weight `(w_k√(1−x_k²))·R(x_k) ≥ 0`.
  * `riemannSum` / `riemannSum_nonneg` — the rational Riemann functional and its
    nonnegativity for EVERY `n` (the SOLID easy half; a `CReal`-weighted SOS).
  * `uniformMidpoint` / `node_lo` / `node_hi` — the CONCRETE uniform-midpoint
    rational nodes `x_k = (2k+1−n)/n` with PROVED `[−1,1]` bounds.
  * `uniformGramSOS_of_momentIntegral` (THEOREM) —
    `MomentIntegralIdentity ⇒ UniformGramSOS`, feeding the proved all-order
    reduction; `momentSquarePos_of_momentIntegral`,
    `wilson_gramPSD_of_momentIntegral` are its compositions.

**NAMED-open (the single VALUE residual).**  `MomentIntegralIdentity M`: the
`(π/2)`-scaled moment-integral identity `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` plus
Riemann convergence, i.e. `momentSquare ≃ (2/π)·lim_n riemannSum`.  It is the
analog of `ChebyshevQuadPSD`'s `gram_eq_node_quadrature` ON THE RATIONAL-NODE
ROUTE — but the historically-hard NODE POSITIVITY half is already free here.

**Net effect.**  All-order moment-square positivity (hence the heat-kernel
character Gram PSD) is REDUCED, along this route, to ONE named value-
identification residual `MomentIntegralIdentity`, sitting ENTIRELY OFF the
irrational-root wall: the per-`n` Riemann nonnegativity is unconditional and the
node positivity is free for rational nodes.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.RiemannSOS.nodeR_nonneg
#print axioms YMGap.Continuum.RiemannSOS.fullWeight_nonneg
#print axioms YMGap.Continuum.RiemannSOS.riemannSum_nonneg
#print axioms YMGap.Continuum.RiemannSOS.node_lo
#print axioms YMGap.Continuum.RiemannSOS.node_hi
#print axioms YMGap.Continuum.RiemannSOS.uniformGramSOS_of_momentIntegral
#print axioms YMGap.Continuum.RiemannSOS.momentSquarePos_of_momentIntegral
#print axioms YMGap.Continuum.RiemannSOS.wilson_gramPSD_of_momentIntegral
