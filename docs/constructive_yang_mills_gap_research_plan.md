# Constructive attack plan for the remaining SU(2) Yang--Mills mass-gap inequality

**Status date:** 2026-06-18  
**Prepared for:** Arthur / darthur  
**Scope:** constructive / intuitionistic proof strategy; no axiom of choice; no law of excluded middle; finite certificates and explicit moduli preferred.  
**Important audit note:** I did not audit the Lean repository itself. I treat the Lean theorem names and proof-status claims in the prompt as supplied project facts, not independently verified facts.

---

## 0. Executive thesis

The supplied program has done something useful: it has isolated a single scalar-looking obstruction,

\[
\exists c_0>0,\exists a_0>0,\forall 0<a<a_0:
\qquad \frac{1-w(a)}{a}\ge c_0,
\]

or equivalently, up to the factorization

\[
1-w^3=(1-w)(1+w+w^2),
\]

a lower floor on

\[
\frac{1-w(a)^3}{a}.
\]

But the first thing I would do is **stress-test whether this inequality is the true physical obstruction**. Under the usual asymptotic-freedom envelope

\[
a\Lambda_L \asymp e^{-B/g_0^2}g_0^{-p},
\qquad
w=e^{-t(g_0)/4},
\qquad
t(g_0)\asymp g_0^2,
\]

the bare heat-kernel quantity satisfies

\[
1-w \asymp g_0^2,
\]

while

\[
a\Lambda_L
\]

is exponentially small in \(1/g_0^2\). So the bare inequality

\[
1-w \gtrsim a\Lambda_L
\]

is easy once the bare coupling--spacing dictionary is assumed. In fact,

\[
\frac{1-w}{a}
\]

would diverge along the perturbative bare trajectory. That is a warning sign: the exact separator \(w^3\) is probably a **bare heat-kernel transfer separator**, not yet the **physical gauge-invariant continuum mass separator**.

So the work plan has two tracks:

1. **Prove the bare inequality as a kill-test.** This should be a short constructive lemma. If it is easy, that proves the current final obligation is too weak unless \(w(a)\) already contains nonperturbative physical RG information beyond the bare heat-kernel parameter.
2. **Move the real residual onto a physical separator.** Define a physical, gauge-invariant transfer-operator separator
   \[
   \operatorname{sep}_{\mathrm{phys}}(a)
   \]
   and prove the genuine lower floor
   \[
   -\log \operatorname{sep}_{\mathrm{phys}}(a)\ge c\,a\Lambda_L.
   \]

The best constructive shape for the remaining frontier is therefore not a vague continuum limit, but one of these two theorem-shaped objects:

\[
\sum_{k=0}^{\infty}(1-\rho_k)\le R<\infty
\]

for RG block multipliers \(\rho_k\), or a spacing-uniform non-abelian susceptibility / log-Sobolev certificate

\[
C_{\mathrm{LSI}}(a)\le K a^2.
\]

Both are compatible with intuitionistic formalization: finite prefixes, explicit tails, rational interval certificates, and no compactness/subsequence extraction.

---

## 1. Research findings: calibrated state of the art

### 1.1 The Clay problem remains open

The Clay Mathematics Institute page still lists Yang--Mills and the mass gap as **unsolved** and says no proof of the mass-gap property is known. It also says progress requires new ideas in both physics and mathematics. See [CMI].

Jaffe--Witten’s official problem description requires a nontrivial quantum Yang--Mills theory on \(\mathbb R^4\) for every compact simple gauge group, satisfying axioms at least as strong as the Wightman / Osterwalder--Schrader framework, with a positive mass gap. It defines a mass gap as absence of Hamiltonian spectrum in \((0,\Delta)\) for some \(\Delta>0\), after the vacuum at zero energy. See [Jaffe-Witten].

**Consequence for this program:** an isolated scalar inequality is valuable only if the objects entering it are already attached to the OS/Wightman physical Hilbert space and to local gauge-invariant observables. A scalar inequality for a bare lattice transfer separator is not automatically the Clay mass gap.

---

### 1.2 Strong-coupling lattice Yang--Mills is controlled, but not spacing-uniform in the continuum window

Shen--Zhu--Zhu prove, at explicit strong-coupling thresholds, existence and uniqueness of infinite-volume invariant measures, log-Sobolev and Poincaré inequalities, exponential ergodicity, exponential correlation decay for a large class of observables, and a strictly positive mass gap for lattice Yang--Mills. For \(SU(N)\), their abstract states a condition of the form

\[
|\beta| < \frac{1}{16(d-1)}.
\]

See [SZZ23].

**Consequence:** this is the right endpoint for Route B. It proves that stochastic-analysis / functional-inequality methods can produce a lattice mass gap for non-abelian Yang--Mills. What it does not give is the spacing-uniform continuum scaling-window bound needed for the Clay gap.

---

### 1.3 Weak-coupling / UV progress exists, but not the full IR gap

Balaban’s four-dimensional renormalization-group work is the historical rigorous UV-stability frontier. Jaffe--Witten describe Balaban’s extension to four dimensions as including asymptotic freedom control of the RG flow and quantitative estimates on large-field effects, but also emphasize that new ideas are needed for a volume-uniform mass gap and the infinite-volume limit. See [Jaffe-Witten] and [Balaban87].

Magnen--Rivasseau--Sénéor construct Schwinger functions for pure \(SU(2)\) Yang--Mills in four dimensions with a **fixed infrared cutoff** and no ultraviolet cutoff, in a regularized axial gauge. Their abstract is explicit about the fixed IR cutoff. See [MRS93].

**Consequence:** UV control and fixed-IR constructions do not by themselves prove a physical mass gap. The gap is an infrared assertion; if the IR cutoff remains fixed, the mass-gap question is not discharged.

---

### 1.4 The Polchinski-flow log-Sobolev program is real, but its scalar successes do not transfer automatically to non-abelian gauge fields

Bauerschmidt--Bodineau--Dagallier survey a renormalization-group perspective on log-Sobolev inequalities and stochastic dynamics through the Polchinski equation. See [BDD24]. Bauerschmidt--Dagallier prove that continuum \(\varphi^4_2\) and \(\varphi^4_3\) measures satisfy log-Sobolev inequalities uniformly in the lattice regularization under the optimal assumption that susceptibility is bounded. See [BD24].

**Consequence:** Route B has a correct template:

\[
\text{bounded susceptibility}
\Longrightarrow
\text{spacing-uniform LSI}
\Longrightarrow
\text{correlation decay / mass floor}.
\]

But the scalar proof uses scalar correlation tools and susceptibility bounds. The non-abelian gauge case lacks a direct FKG/Griffiths-type monotonicity replacement and has gauge constraints. The missing target should be stated as a **non-abelian susceptibility certificate**, not hidden under prose.

---

### 1.5 Heat-kernel actions are a legitimate structured coordinate system

Menotti--Onofri introduced the heat-kernel action on the group manifold as an alternative lattice gauge action and noted its strict analogy with the Berezinskii--Villain action; the abstract states that with this action the Gross--Witten singularity is rigorously absent in two dimensions. See [Menotti-Onofri].

In two dimensions, Yang--Mills is rigorously controlled. Driver analyzed two-dimensional Yang--Mills in both continuum and lattice forms and studied continuum expectations, lattice convergence, and lassos. See [Driver89]. Lévy’s Markovian holonomy-field formulation also places two-dimensional Yang--Mills in a rigorous probabilistic framework. See [Levy08].

**Consequence:** the heat-kernel formulation is an excellent testbed and coordinate chart. It should not, however, be silently treated as an exact four-dimensional RG fixed point. In \(d=2\), heat-kernel/area additivity is exact. In \(d=4\), the near-fixed-point deviation is exactly where the difficult estimate lives.

---

### 1.6 Recent claimed full solutions need hard filtering

The arXiv entry `2506.00284`, which claimed a constructive proof for pure \(SU(3)\) Yang--Mills, is marked by arXiv as withdrawn by arXiv admin because it did not meet arXiv’s research-content quality standards. See [Arxiv2506].

**Consequence:** do not use that claim as evidence. The official and refereed state remains: no known proof of the 4D non-abelian continuum mass gap.

---

### 1.7 Useful analytic side tools are available, but they solve only sub-lemmas

Several one-variable inequalities mentioned in the supplied plan are real, formalizable tools:

- Hornik--Grün give Amos-type lower and upper bounds for modified Bessel-function ratios. See [Hornik-Grun].
- Dixit--Roy--Zaharescu prove convexity and monotonicity results for quotients of theta functions. See [DRZ].
- Baricz and collaborators prove Turán-type inequalities for modified Bessel functions. See [Baricz].

**Consequence:** these are good for finite/truncated heat-kernel estimates and theta-ratio certificates. They do not by themselves prove the nonperturbative four-dimensional crossover estimate.

---

## 2. Normalization checks and a correction

The supplied notation uses

\[
w=e^{-t/4}.
\]

Then:

\[
t\to 0 \quad\Longrightarrow\quad w\to 1,
\]

and the heat kernel concentrates near the group identity. This is the weak-coupling / continuum side.

\[
t\to \infty \quad\Longrightarrow\quad w\to 0,
\]

and nontrivial character modes are suppressed, approaching a Haar-like strong-coupling side.

So any statement saying “strong coupling = small \(t\)” should be corrected or renamed. With the convention in the prompt, **small \(t\) is weak coupling** and **large \(t\) is strong-coupling-like**.

---

## 3. Error model and constructive discipline

### 3.1 Scalar errors

For real scalar inequalities, use

\[
d_{\mathbb R}(x,y)=|x-y|.
\]

At resolution \(r\in\mathbb N\), certify rational intervals of width

\[
\varepsilon_{\mathbb R}(r)=2^{-r}.
\]

A scalar claim

\[
x\le y
\]

should be represented by an interval certificate

\[
X_r=[x_r^-,x_r^+],\qquad Y_r=[y_r^-,y_r^+],
\qquad x_r^+\le y_r^-.
\]

### 3.2 Operator errors

For transfer operators or Markov generators, use operator norm

\[
d_{\mathrm{op}}(A,B)=\|A-B\|_{\ell^2\to\ell^2}
\]

with target resolution

\[
\varepsilon_{\mathrm{op}}(r)=2^{-r}.
\]

For a truncation \(A_{S,L}\) at representation cutoff \(S\) and volume cutoff \(L\), require explicit tails

\[
\|A-A_{S,L}\|
\le
E_{\mathrm{rep}}(S)+E_{\mathrm{vol}}(L).
\]

### 3.3 Infinite products

For a finite product of \(N\) certified factors, budget

\[
\varepsilon_{\prod}(r,N)=N2^{-r}.
\]

For an infinite product, require a tail certificate

\[
T_N\le 2^{-r}.
\]

No compactness extraction. No “choose a convergent subsequence.” The limit is data:

\[
N(r)\quad\text{such that}\quad n,m\ge N(r)\Rightarrow |x_n-x_m|\le 2^{-r}.
\]

---

## 4. Kill-test theorem: bare asymptotic freedom implies the displayed linear floor

### 4.1 Statement

Assume explicit data

\[
0<g\le g_*,
\qquad
\alpha g^2\le t(g)\le \bar\alpha g^2,
\qquad
0<a(g)\Lambda_L\le A e^{-B/g^2}g^{-p},
\]

with

\[
\alpha,\bar\alpha,A,B,p,g_*,\Lambda_L>0.
\]

Let

\[
w(g)=e^{-t(g)/4}.
\]

Then constructively prove:

\[
\exists c_0>0,\exists g_1>0,
\forall 0<g<g_1:
\qquad
1-w(g)
\ge
c_0\,a(g)\Lambda_L.
\]

If one has a monotone spacing trajectory \(a=a(g)\), this gives

\[
\frac{1-w(a)}{a}
\ge
c_0\Lambda_L
\]

for small \(a\).

### 4.2 Constructive proof skeleton

For \(0\le x\le 1\),

\[
1-e^{-x}\ge \frac{x}{2}.
\]

Take \(x=t/4\). If \(t\le 4\), then

\[
1-e^{-t/4}\ge \frac{t}{8}\ge \frac{\alpha}{8}g^2.
\]

So it is enough to show

\[
A e^{-B/g^2}g^{-p}\le Cg^2
\]

for small \(g\). Equivalently, with

\[
y=\frac1{g^2},
\]

show

\[
A e^{-By} y^{p/2+1}\le C
\]

for large \(y\).

Choose an integer

\[
m>p/2+1.
\]

From the exponential series,

\[
e^{By/2}\ge \frac{(By/2)^m}{m!}.
\]

Thus

\[
e^{-By}y^{p/2+1}
=
 e^{-By/2}\,e^{-By/2}y^{p/2+1}
\le
 e^{-By/2}\,m!\left(\frac{2}{B}\right)^m y^{p/2+1-m}.
\]

For \(y\ge1\), because \(p/2+1-m<0\),

\[
y^{p/2+1-m}\le 1.
\]

Pick explicit \(Y\) such that

\[
A m!\left(\frac{2}{B}\right)^m e^{-BY/2}\le C.
\]

Then for \(y\ge Y\),

\[
A e^{-By}y^{p/2+1}\le C.
\]

Everything here is constructive: the integer \(m\), the threshold \(Y\), and the lower bound \(c_0\) are witnesses.

### 4.3 Lean-facing shape

```lean
structure AFEnvelope where
  α αbar A B p Λ : CReal
  α_pos : 0 < α
  A_pos : 0 < A
  B_pos : 0 < B
  Λ_pos : 0 < Λ
  t_lower : ∀ g inSmallCoupling, α * g^2 ≤ t g
  t_upper : ∀ g inSmallCoupling, t g ≤ αbar * g^2
  spacing_upper : ∀ g inSmallCoupling,
    a g * Λ ≤ A * exp (-(B / g^2)) * g^(-p)

 theorem BareAFImpliesLinearFloor
   (H : AFEnvelope)
   (w_def : ∀ g, w g = exp (-(t g)/4)) :
   ∃ c₀ > 0, ∃ g₁ > 0, ∀ g, 0 < g → g < g₁ →
     c₀ * (a g) * H.Λ ≤ 1 - w g
```

### 4.4 Diagnostic implication

If this theorem closes quickly, then the displayed linear floor is not the Clay-hard part unless \(w(a)\) is **not merely the bare heat-kernel weight**. The true mass-gap obligation should then be moved to a physical transfer separator.

---

## 5. Replace the bare separator by a physical separator

### 5.1 Proposed object

Define a structure carrying the actual physical transfer separator:

```lean
structure PhysicalSeparator where
  sep : SpacingIndex → CReal
  sep_pos : ∀ j, 0 < sep j
  sep_lt_one : ∀ j, sep j < 1
  controlsGaugeInvariantCorr :
    ∀ O, GaugeInvariantLocal O →
      ∃ C > 0, ∀ j n,
        connectedCorr j O n ≤ C * (sep j)^n
```

Then define

\[
m_{\mathrm{phys,lat}}(a_j)
:=
-\log \operatorname{sep}_{\mathrm{phys}}(a_j).
\]

The actual floor should be

\[
\exists c>0,\exists j_0,\forall j\ge j_0:
\qquad
m_{\mathrm{phys,lat}}(a_j)
\ge
c\,a_j\Lambda_L.
\]

### 5.2 Why this matters

The exact heat-kernel identity

\[
\operatorname{sep}_{\mathrm{HK}}(w)=w^3
\]

is valuable. But before it proves the Clay mass gap, one needs a theorem of the form

\[
\operatorname{sep}_{\mathrm{phys}}(a)
\le
\Psi\bigl(w_{\mathrm{bare}}(a),R_a\bigr),
\]

where \(R_a\) measures the four-dimensional deviation from the heat-kernel fixed-point manifold, and then a controlled estimate

\[
\left|-\log\operatorname{sep}_{\mathrm{phys}}(a)
-
\Phi_{\mathrm{RG}}(w_{\mathrm{bare}}(a),R_a)
\right|
\le
\delta(a),
\qquad
\delta(a)\le C a\Lambda_L.
\]

This \(\delta(a)\) is the real crossover residual.

---

## 6. Route A: heat-kernel / theta-ratio comparison as finite certificates

### 6.1 Basic structure

Represent one RG block step as

\[
S_k
=
S_{\mathrm{HK}}(t_k)+R_k,
\]

where \(R_k\) is the residual away from the heat-kernel submanifold.

Choose a constructive Banach norm on residual coefficients. A useful model is

\[
\|R_k\|_{\mathcal B_k}
=
\sum_{\ell,s}
|r_{\ell,s}^{(k)}|
\,e^{\mu |\ell|}
\,e^{\sigma C_4(s)},
\]

where:

- \(\ell\) is a loop or polymer index,
- \(|\ell|\) is its length or support size,
- \(s\in\mathbb N\) is the \(SU(2)\) representation index,
- \(C_4(s)=s(s+2)\),
- \(\mu,\sigma>0\) are explicit weights.

Aim for the one-block theorem

\[
\|R_{k+1}\|_{\mathcal B_{k+1}}
\le
q_k\|R_k\|_{\mathcal B_k}+E_k,
\]

with

\[
0\le q_k\le1,
\qquad
\sum_k E_k<\infty.
\]

Then prove a gap-distortion bound

\[
\left|
 m_{\mathrm{phys,lat}}(a_k)-m_{\mathrm{HK}}(t_k)
\right|
\le
L_k\|R_k\|_{\mathcal B_k}.
\]

### 6.2 Finite character algebra

For \(SU(2)\), tensor products are finitary:

\[
V_m\otimes V_n
\cong
\bigoplus_{r=|m-n|,\ r\equiv m+n\pmod 2}^{m+n} V_r.
\]

That is ideal for formalization. A block certificate should compute finite sums up to \(S\), then attach a Gaussian Casimir tail:

\[
\sum_{s>S}(s+1)^q e^{-\tau s(s+2)}
\le
2^{-r}.
\]

### 6.3 Certificate structure

```lean
structure OneBlockCertificate where
  k : Nat
  precision : Nat
  repCutoff : Nat
  rhoLower rhoUpper : QPos
  lowerProof : rhoLower ≤ trueRho k
  upperProof : trueRho k ≤ rhoUpper
  widthProof : rhoUpper - rhoLower ≤ 2^(-precision)
  repTailBound : RepTail k repCutoff ≤ 2^(-precision)
  loopTailBound : LoopTail k supportCutoff ≤ 2^(-precision)
```

The output is not “the block was estimated numerically.” It is a proof object:

\[
\rho_k\in[\rho_k^-,\rho_k^+]
\]

with an auditable tail.

---

## 7. Route B: product floor from summable block loss

### 7.1 Core constructive lemma

Let

\[
0<\rho_k\le1,
\qquad
\eta_k:=1-\rho_k.
\]

If

\[
0\le\eta_k\le\frac12,
\qquad
\sum_{k=0}^{\infty}\eta_k\le R<\infty,
\]

then

\[
\prod_{k=0}^{\infty}\rho_k
=\prod_{k=0}^{\infty}(1-\eta_k)
\ge
\exp(-2R)>0.
\]

The proof uses only the elementary inequality

\[
\log(1-x)\ge -2x
\qquad
(0\le x\le1/2),
\]

finite prefix products, and an explicit Cauchy tail for the sum.

### 7.2 Dyadic sufficient condition

For dyadic spacing

\[
a_k=a_0 2^{-k},
\]

it is enough to prove

\[
1-\rho_k\le A a_k^\theta
\qquad
(\theta>0).
\]

Then

\[
\sum_{k=0}^{\infty}(1-\rho_k)
\le
A a_0^\theta\sum_{k=0}^{\infty}2^{-\theta k}
=
\frac{A a_0^\theta}{1-2^{-\theta}}.
\]

This is fully constructive because the geometric-series modulus is explicit.

### 7.3 Lean-facing shape

```lean
theorem summableBlockLoss_to_productFloor
  (ρ : Nat → CReal)
  (hpos : ∀ k, 0 < ρ k)
  (hle : ∀ k, ρ k ≤ 1)
  (hhalf : ∀ k, 1 - ρ k ≤ (1/2 : CReal))
  (hsum : SummableWithBound (fun k => 1 - ρ k) R)
  (hR : 0 ≤ R) :
  ∃ c > 0, ∀ n,
    c ≤ Finset.prod (Finset.range n) ρ
```

This lemma should be built before any frontier analysis. It converts the real obstruction into:

\[
\boxed{\sum_k(1-\rho_k)<\infty.}
\]

---

## 8. Route B frontier: non-abelian susceptibility certificate

### 8.1 The missing certificate

Define a non-abelian susceptibility bound for the gauge-invariant sector. A prototype:

\[
\sup_e
\sum_{e'}
e^{m d(e,e')}
\left\|
\operatorname{Cov}_{\mu_a}
\bigl(\nabla_e F,\nabla_{e'}F\bigr)
\right\|
\le C,
\]

uniformly in the scaling window.

Here:

- \(e,e'\) are lattice edges,
- \(d(e,e')\) is lattice graph distance,
- \(\nabla_e\) is a left/right-invariant group derivative on the copy of \(SU(2)\) at edge \(e\),
- \(F\) ranges over a controlled class of local gauge-invariant test functions,
- \(m,C>0\) are independent of \(a\) in the target scaling window.

Lean-facing record:

```lean
structure NonAbelianSusceptibility where
  m C : QPos
  bound :
    ∀ a, InScalingWindow a →
      weightedCovarianceNorm μ[a] m ≤ C
  volumeModulus :
    ∀ a r, ∃ L₀, ∀ L L' ≥ L₀,
      measureDistance μ[a,L] μ[a,L'] ≤ 2^(-r)
```

### 8.2 Desired implication

Prove formally:

\[
\mathrm{NonAbelianSusceptibility}
\Longrightarrow
\mathrm{UniformLSI}
\Longrightarrow
\mathrm{PhysicalGapFloor}.
\]

Lean-facing:

```lean
theorem NASuscept_to_uniform_LSI
  (H : NonAbelianSusceptibility) :
  ∃ K > 0, ∀ a, InScalingWindow a →
    LSIConstant μ[a] ≤ K * a^2

theorem uniform_LSI_to_physical_gap_floor
  (H : ∃ K > 0, ∀ a, InScalingWindow a →
      LSIConstant μ[a] ≤ K * a^2) :
  ∃ c > 0, ∀ a, SmallSpacing a →
    c * a ≤ physicalLatticeMass a
```

The first theorem is frontier analysis. The second should be mostly formal once the correct dynamic-to-static bridge is in place.

---

## 9. Finite-volume / finite-cutoff discipline

Every object should be finite before taking a limit. For spacing \(a_j\), volume radius \(L\), representation cutoff \(S\), and precision \(r\), define a rational interval approximation

\[
\mu_{j,L,S,r}.
\]

Every analytic theorem should have the form

\[
\left|
Q_{j,L,S,r}-Q_{j,\infty,\infty}
\right|
\le
E_{\mathrm{vol}}(j,L)
+
E_{\mathrm{rep}}(j,S)
+2^{-r}.
\]

The proof object must include explicit functions

\[
L(j,r),
\qquad
S(j,r),
\qquad
r'(j,r)
\]

such that the total error is at most \(2^{-r}\).

This is the intuitionistic substitute for unsafe phrases like:

- “take a convergent subsequence,”
- “by compactness,”
- “choose a minimizer,”
- “almost surely, after passing to a limit,”
- “the continuum measure exists.”

The constructive version is always a modulus.

---

## 10. Prioritized work plan

### Phase 1: immediate formal wins

#### Task 1. `BareAFImpliesLinearFloor`

Build the elementary theorem from Section 4.

**Why first:** it is the best diagnostic. If it closes easily, the current final inequality must be reinterpreted as physical-RG data, not bare heat-kernel data.

**Expected difficulty:** low.

**Deliverable:** axiom-clean constructive proof with explicit constants.

---

#### Task 2. `SummableBlockLoss_to_productFloor`

Build the product-floor lemma from Section 7.

**Why second:** it is pure constructive analysis and will be used by both routes.

**Expected difficulty:** low-to-medium depending on available constructive real/exponential/log infrastructure.

**Fallback:** prove the rational product bound

\[
\prod_k(1-\eta_k)
\ge
\prod_k e^{-2\eta_k}
\]

as a named inequality only after importing or defining enough exponential/log facts. A cruder rational bound using

\[
1-x\ge 4^{-x}
\]

on dyadic rational grids may be easier if exponentials are expensive.

---

#### Task 3. `PhysicalSeparator` interface

Add the physical separator structure and stop identifying it with \(w^3\) without a comparison theorem.

**Why third:** this prevents the proof graph from accidentally proving a bare lattice gap instead of the physical mass gap.

**Expected difficulty:** medium, mostly design.

---

### Phase 2: certified finite block

#### Task 4. `SU2CharacterTail`

Formalize tail bounds of the form

\[
\sum_{s>S}(s+1)^q e^{-\tau s(s+2)}\le 2^{-r}.
\]

**Expected difficulty:** medium.

**Proof idea:** compare polynomial times Gaussian to a shifted geometric series after choosing \(S\) large enough.

---

#### Task 5. `OneBlockSU2Certificate`

Compute one block-spin step with a representation cutoff and a loop/support cutoff. The output is an interval enclosure for \(\rho_0\).

**Expected difficulty:** medium-to-high.

**Success criterion:** produce one auditable certificate, not a universal theorem.

---

#### Task 6. `BlockLossRateInterface`

State the frontier as:

\[
1-\rho_k\le A a_k^\theta.
\]

Then prove:

\[
\texttt{BlockLossRateInterface}
\Longrightarrow
\texttt{RGBlockPersistence}
\Longrightarrow
\texttt{physGapMin}>0.
\]

**Expected difficulty:** low once Task 2 is done.

---

### Phase 3: physical functional inequalities

#### Task 7. `NonAbelianSusceptibility` record

Make the missing non-abelian susceptibility theorem a formal record with edge-gradient covariance bounds, volume modulus, and gauge-invariant test-function class.

**Expected difficulty:** medium, mostly definitions.

---

#### Task 8. `NASuscept_to_uniform_LSI` conditional theorem

Prove the conditional implication from the non-abelian susceptibility record to a spacing-uniform log-Sobolev or Poincaré inequality.

**Expected difficulty:** high.

**Benefit:** even a conditional theorem is valuable because it localizes exactly what the scalar \(\varphi^4\) technology supplies and what the non-abelian case lacks.

---

#### Task 9. `UniformLSI_to_PhysicalGapFloor`

Complete the dynamic-to-static bridge:

\[
C_{\mathrm{LSI}}(a)
\le
K a^2
\Longrightarrow
m_{\mathrm{phys,lat}}(a)\ge c a.
\]

**Expected difficulty:** medium-to-high.

**Key requirement:** the observable sector must be gauge-invariant and tied to the OS transfer Hilbert space.

---

## 11. Decision tree

### Branch A: `BareAFImpliesLinearFloor` proves easily

Then revise the project statement:

\[
\frac{1-w_{\mathrm{bare}}(a)}{a}\ge c_0
\]

is a theorem about the bare trajectory, not the Clay-hard theorem.

The new open theorem should be:

\[
-
\log\operatorname{sep}_{\mathrm{phys}}(a)
\ge
c a\Lambda_L.
\]

### Branch B: `BareAFImpliesLinearFloor` fails

Then one of the assumptions is wrong or missing:

1. \(t(g_0)\asymp g_0^2\) is not the dictionary being used;
2. \(w(a)\) is not a bare heat-kernel weight;
3. \(a\Lambda_L\) is not attached to the usual perturbative AF trajectory;
4. the scaling variable in the Lean object differs from the continuum physics notation.

In that case, the next task is not more analysis; it is **type disambiguation** of \(w(a)\).

### Branch C: physical separator comparison is proved

If one proves

\[
\operatorname{sep}_{\mathrm{phys}}(a)
\le
\operatorname{sep}_{\mathrm{HK}}(w(a))\,e^{\delta(a)},
\qquad
\delta(a)\le C a\Lambda_L,
\]

then Route A becomes viable. The exact \(w^3\) separator becomes a real physical input rather than a bare model calculation.

### Branch D: non-abelian susceptibility is proved

If one proves the spacing-uniform non-abelian susceptibility certificate, Route B becomes viable and likely more robust than Route A, because it directly controls physical correlations.

---

## 12. What to avoid

1. **Do not use weak compactness as existence.** Jaffe--Witten explicitly exclude weak existence by compactness unless it is supplemented by the required axioms and mass-gap properties. See [Jaffe-Witten].
2. **Do not identify a bare transfer gap with a physical mass gap without a theorem.** The exact formula \(w^3\) is not enough by itself.
3. **Do not treat fixed-spacing strong-coupling gap as continuum gap.** SZZ23 is powerful, but its theorem is in a strong-coupling region and does not automatically cross to weak coupling / continuum scaling. See [SZZ23].
4. **Do not cite withdrawn claimed solutions as support.** arXiv withdrew `2506.00284` for quality-standard reasons. See [Arxiv2506].
5. **Do not hide the hard part in “RG trajectory.”** The RG trajectory must be data with a measurement map and error modulus.

---

## 13. Compact theorem map

The constructive target graph I would build is:

```text
BareAFEnvelope
  └── BareAFImpliesLinearFloor
        └── diagnostic: current scalar inequality is easy if w is bare

PhysicalSeparator
  ├── UniformLSI_to_PhysicalGapFloor
  │     └── physGapMin > 0
  └── HKPhysicalComparison
        └── Route A physical use of sep_HK = w^3

SummableBlockLoss
  └── BlockLossRateInterface
        └── RGBlockPersistence
              └── RGGapPersistence
                    └── physGapMin > 0

NonAbelianSusceptibility
  └── NASuscept_to_uniform_LSI
        └── UniformLSI_to_PhysicalGapFloor
```

The single best next theorem is:

\[
\boxed{
\sum_k(1-\rho_k)
\le R
\Longrightarrow
\prod_k\rho_k\ge e^{-2R}>0.
}
\]

The single best diagnostic theorem is:

\[
\boxed{
\text{AF envelope}+t\asymp g^2
\Longrightarrow
\frac{1-e^{-t/4}}{a}\ge c_0.
}
\]

The single real frontier theorem is:

\[
\boxed{
\operatorname{sep}_{\mathrm{phys}}(a)
\text{ decays no faster than }e^{-c a\Lambda_L}
}
\]

or equivalently a spacing-uniform functional inequality:

\[
\boxed{
C_{\mathrm{LSI}}(a)\le K a^2.
}
\]

---

## 14. Bottom line

The program should be pushed in a slightly more defensive direction.

The exact heat-kernel result

\[
\operatorname{sep}_{\mathrm{HK}}(w)=w^3
\]

is a good machine-checked anchor. But if \(w\) is the bare heat-kernel parameter, then the displayed inequality

\[
\frac{1-w(a)}{a}\ge c_0
\]

should follow from the usual asymptotic-freedom envelope by an elementary constructive comparison. That means the real four-dimensional Yang--Mills difficulty has not disappeared; it has moved into the unproved comparison between the bare heat-kernel separator and the physical gauge-invariant continuum transfer separator.

The cleanest next move is therefore:

1. prove the bare inequality as a diagnostic;
2. introduce `PhysicalSeparator`;
3. prove `SummableBlockLoss_to_productFloor`;
4. formalize the missing non-abelian susceptibility or heat-kernel residual as a precise record;
5. use finite block certificates plus summable tails to avoid every nonconstructive limit step.

That keeps the project honest and still aggressive: every claim is a build, every limit has a modulus, and the true residual becomes a theorem-shaped object rather than a fog bank.

---

## References and source notes

[CMI]: Clay Mathematics Institute, “Yang--Mills & the Mass Gap.”  
https://www.claymath.org/millennium/yang-mills-the-maths-gap/

[Jaffe-Witten]: Arthur Jaffe and Edward Witten, “Quantum Yang--Mills Theory,” official Clay problem description.  
https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf

[Luscher-Weisz95]: Martin Lüscher and Peter Weisz, “Two-loop relation between the bare lattice coupling and the MSbar coupling in pure SU(N) gauge theories,” arXiv:hep-lat/9502001.  
https://arxiv.org/abs/hep-lat/9502001

[Menotti-Onofri]: P. Menotti and E. Onofri, “The action of SU(N) lattice gauge theory in terms of the heat kernel on the group manifold,” Nuclear Physics B 190 (1981), 288--300.  
https://cds.cern.ch/record/134274

[Osterwalder-Seiler78]: K. Osterwalder and E. Seiler, “Gauge Field Theories on the Lattice,” Annals of Physics 110 (1978), 440--471.  
https://inspirehep.net/literature/120117

[Balaban87]: T. Bałaban, “Renormalization group approach to lattice gauge field theories. I. Generation of effective actions in a small field approximation and a coupling constant renormalization in 4D,” Communications in Mathematical Physics 109 (1987), 249--301.  
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-109/issue-2/Renormalization-group-approach-to-lattice-gauge-field-theories-I-Generation/cmp/1104116842.pdf

[MRS93]: J. Magnen, V. Rivasseau, and R. Sénéor, “Construction of YM4 with an infrared cutoff,” Communications in Mathematical Physics 155 (1993), 325--383.  
https://link.springer.com/article/10.1007/BF02097397

[SZZ23]: Hao Shen, Rongchan Zhu, and Xiangchan Zhu, “A stochastic analysis approach to lattice Yang--Mills at strong coupling,” Communications in Mathematical Physics 400 (2023), 805--851; arXiv:2204.12737.  
https://arxiv.org/abs/2204.12737

[BDD24]: Roland Bauerschmidt, Thierry Bodineau, and Benoit Dagallier, “Stochastic dynamics and the Polchinski equation: An introduction,” Probability Surveys 21 (2024), 200--290.  
https://projecteuclid.org/journals/probability-surveys/volume-21/issue-none/Stochastic-dynamics-and-the-Polchinski-equation-An-introduction/10.1214/24-PS27.full

[BD24]: Roland Bauerschmidt and Benoit Dagallier, “Log-Sobolev inequality for the \(\varphi^4_2\) and \(\varphi^4_3\) measures,” Communications on Pure and Applied Mathematics 77 (2024), 2579--2612; arXiv:2202.02295.  
https://arxiv.org/abs/2202.02295

[Helffer-Sjostrand]: B. Helffer and J. Sjöstrand, “On the correlation for Kac like models in the convex case,” Journal of Statistical Physics 74 (1994), 349--369. See also Helffer’s follow-up notes on decay of correlations and Witten Laplacians.  
https://www.numdam.org/item/AIHPB_1999__35_4_483_0.pdf

[Driver89]: B. K. Driver, “YM2: continuum expectations, lattice convergence, and lassos,” Communications in Mathematical Physics 123 (1989), 575--616.  
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-123/issue-4/YM_2-continuum-expectations-lattice-convergence-and-lassos/cmp/1104178984.pdf

[Levy08]: Thierry Lévy, “Two-dimensional Markovian holonomy fields,” arXiv:0804.2230.  
https://arxiv.org/abs/0804.2230

[Chatterjee18]: Sourav Chatterjee, “Yang--Mills for probabilists,” arXiv:1803.01950.  
https://arxiv.org/abs/1803.01950

[CCHS24]: Ajay Chandra, Ilya Chevyrev, Martin Hairer, and Hao Shen, “Stochastic quantisation of Yang--Mills--Higgs in 3D,” Inventiones Mathematicae 237 (2024), 541--696.  
https://link.springer.com/article/10.1007/s00222-024-01264-2

[Hornik-Grun]: Kurt Hornik and Bettina Grün, “Amos-type bounds for modified Bessel function ratios,” Journal of Mathematical Analysis and Applications 408 (2013), 91--101.  
https://pmc.ncbi.nlm.nih.gov/articles/PMC4047631/

[DRZ]: Atul Dixit, Arindam Roy, and Alexandru Zaharescu, “Convexity of Quotients of Theta Functions,” arXiv:1104.2401.  
https://arxiv.org/abs/1104.2401

[Baricz]: Árpád Baricz and Saminathan Ponnusamy, “On Turán type inequalities for modified Bessel functions,” arXiv:1010.3346.  
https://arxiv.org/abs/1010.3346

[Arxiv2506]: D. C. Jacobsen, “A Constructive Proof of Existence and Mass Gap for Pure SU(3) Yang--Mills in Four-Dimensional Space-Time,” arXiv:2506.00284, withdrawn by arXiv admin.  
https://arxiv.org/abs/2506.00284
