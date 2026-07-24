# RG as state evolution plus interface evolution

## Status and scope

This note records the 2026-07-22 structural correction prompted by the
supplied polynomial-tree analysis.  The former shorthand

\[
X_{k+1}=R_k(X_k)
\]

is safe only after proving that adjacent scales have been transported into a
common effective interface.  Before that stabilization, an RG step changes
both the state and the type of the next legal operation:

\[
(I_k,S_k)\xrightarrow{(a_k,d_k)}(I_{k+1},S_{k+1}),
\qquad
I_{k+1}=\operatorname{rest}_k(a_k,d_k).
\]

This is a correction to the proof architecture, not progress on the hard
analytic estimate.  In particular, nothing in the new scaffold proves a
cutoff-uniform contraction, a landing theorem, dimensional transmutation,
reflection positivity, continuum existence, clustering, or a physical mass
lower bound.

## The interface polynomial

At scale `k`, the legal interaction is a polynomial

\[
P_k=\sum_{a:I_k}y^{D_k(a)}.
\]

The initial action vocabulary is:

1. integrate a fluctuation field;
2. extract the relevant part;
3. localize a polymer;
4. rescale fields;
5. transport an observable;
6. verify analytic bounds;
7. abort with a counterexample.

The response type is evidence returned by the operation.  Verification is a
sum of a proof-carrying success and explicit diagnostic evidence.  A failed
verification therefore selects a diagnostic child interface; it cannot be
silently coerced onto the intended analytic branch.

The non-polynomial carriers are also part of `RGInterface`: cutoff data,
retained fields, polymer activities, relevant coordinates, norm data,
observable data, certificate data, and dynamic/interface error data.  This is
what makes a scale change capable of changing the state type itself.

## Constructive Lean encoding

The implementation is
[`lean/YMGap/RG/PolynomialTree.lean`](../lean/YMGap/RG/PolynomialTree.lean).
It has four layers.

### Finite approximants

`PolyTreeApprox n` is executable by structural recursion on `n`.
`PolyTreeHomApprox` implements the finite morphism tower

\[
\operatorname{Hom}_{n+1}(p,q)=
\prod_i\sum_j\prod_e\sum_d
\operatorname{Hom}_n(p_{i,d},q_{j,e}).
\]

The module exports checked depth-1, depth-2, and depth-3 approximants of a
small branching RG program.

### Infinite behavior

Lean does not provide the literal coinductive record suggested in the source
text.  `PolyTree` is instead a transition coalgebra consisting of an internal
node-code type, the current node, its polynomial observation, and the child
transition.  Every finite observation is productive, while a constant
polynomial embeds as a one-state coalgebra.

### State/interface separation

`RGState I` is indexed by the current `RGInterface I`.  `RGStep` gives its
successor the type

```text
RGState (interface (next node action response))
```

directly.  An update cannot return a state for the wrong child interface.
`RGTrace` recursively packages finite typed histories.

### Checked trace and honest boundary

`demoThreeScaleTrace` checks the requested scales 0, 1, and 2;
`demoThreeTransitionTrace` extends it by one transition into the stable-tail
interface.  Each step carries an analytic-step witness,
observable-transport witness, certificate update, and cumulative
interface-error update.  The example also checks that successful and failed
verification select different children.

The trace is a type-system test with natural-number payloads.  It is not the
Yang--Mills analytic trace and discharges no frontier atom.

### Coherent transport and stabilization certificates

[`lean/YMGap/RG/InterfaceStability.lean`](../lean/YMGap/RG/InterfaceStability.lean)
implements the structural content of RG-I4 and RG-I5.  `InterfaceTransport`
constructively transports actions, dependent response evidence, and every
scale-dependent state carrier.  Forward and backward state transports have
exact round-trip theorems.  `InterfaceTransportPreserves` adds explicit
meaning-preservation witnesses for relevant coordinates, norms, localization,
observables, and certificates, so a carrier equivalence cannot silently stand
in for an analytic preservation result.

Production integration exposed a necessary refinement: integrating out a
fluctuation field is generally not invertible.  Exact `InterfaceTransport` is
therefore the coordinate-change/special-case API, not the physical default.
[`lean/YMGap/RG/DirectedInterfaceTransport.lean`](../lean/YMGap/RG/DirectedInterfaceTransport.lean)
defines forward-only maps for actions, dependent responses, every state
carrier, and both error ledgers.  It carries separate semantic and error
preservation witnesses and embeds exact transports when inverses really are
available.

[`lean/YMGap/RG/InductiveInterfaceBridge.lean`](../lean/YMGap/RG/InductiveInterfaceBridge.lean)
connects the new interface layer to the existing `InductiveState` and
`StepTypeWithBudget Q'` machinery.  It supplies exact-rational relevant/KP
carriers, a lossless legacy state adapter, and a budgeted transition carrying
the existing S1--S4 witnesses.  Actual retained fields, observables,
spacing/volume data, and physical coarse-graining functions remain inputs.

`StableTailCertificate` packages the selected branch, `k_*`, the common stable
interface `P_*`, transports, four-component discrepancy, tolerance, and a
computable modulus.  Its `scaleFor` operation returns a scale witness together
with a proof that every later certified tail offset is within a requested
positive rational resolution.  The checked `demoStableTail` instance enters
at scale 2, transports into the stable demo interface, and then has zero
interface discrepancy.

This completes the reusable certificate machinery, not its Yang--Mills
instantiation.  The physical transports, preservation theorems, and analytic
decay estimate for `epsilon_int(k)` remain open.

### Constant ray, stable dynamics, and the first downstream consumer

[`lean/YMGap/RG/DirectedStableTailPresentation.lean`](../lean/YMGap/RG/DirectedStableTailPresentation.lean)
extracts exactly what forward transports justify: a typed selected source ray,
a forward-normalized constant-interface ray and state family, separate error
semantics, and a computable resolution landing scale.  It does not claim
state recovery, injectivity, off-ray transport, or whole-tree equivalence.
`StableTailPresentation.lean` retains the stronger round-trip presentation
for the special case with actual carrier equivalences.

[`lean/YMGap/RG/StableDynamics.lean`](../lean/YMGap/RG/StableDynamics.lean)
packages an explicit rational `q<1`, preserved admissible domain, constructive
landing witness, and separate summable dynamic/interface distortion streams.
It derives geometric post-landing contraction and combined tail bounds while
keeping the physical orbit tied to transported RG states.  These are
consumers of named hypotheses, not proofs of the physical estimates.

[`lean/YMGap/RG/DirectedStableDynamics.lean`](../lean/YMGap/RG/DirectedStableDynamics.lean)
is the production-default composition: its stable orbit is exactly the
forward image of a node-indexed source-state family under the directed tail
transport.  It exposes landing, post-landing contraction, and split-budget
consequences without a backward map or source-space admissibility claim.

[`lean/YMGap/RG/StableDynamicsCorrelationBridge.lean`](../lean/YMGap/RG/StableDynamicsCorrelationBridge.lean)
is the first honest downstream bridge.  Given a physical correlation readout,
it derives geometric decay; given an exact finite spectral identification, it
returns a finite located spectral gap with positive rational margin.  The
volume-uniform floor/modulus, physical-spacing conversion, continuum measure,
and OS bindings remain open, so no uniform or continuum mass-gap structure is
inhabited.
`DirectedStableDynamicsCorrelationBridge.lean` supplies the same finite
consumer directly from the forward-only physical package, with no adapter
through an exact-equivalence certificate.

## Executable simulation and falsification track

[`computations/rg_interface_tree.py`](../computations/rg_interface_tree.py)
mirrors the structure with exact rational arithmetic.  Its tests in
[`tests/test_rg_interface_tree.py`](../tests/test_rg_interface_tree.py) enforce:

1. executable depth-1, depth-2, and depth-3 tree approximants;
2. a componentwise interface discrepancy whose maximum decreases toward a
   stable reference;
3. contraction measured only after adjacent states are transported to one
   chart;
4. branch sensitivity under successful versus failed verification;
5. rejection of a state tagged with the wrong child interface;
6. exact chart semantics and complete-state transport round trips;
7. an explicit stabilization scale and checked dyadic tail suffix;
8. separate logging of `C_dyn` and `C_int`.

These are regression tests for the architecture.  The demonstration constants
are not estimates for Yang--Mills theory.

## Required theorem order

The analytic campaign must now respect this order.

### A. Interface stabilization

Construct `k_*`, a stable interface `P_*`, and coherent transports of all
interfaces on the selected tail.  The transports must preserve relevant
coordinate projection, the Gaussian norm, localization, observables, and
certificate interpretation up to a computed discrepancy

\[
d_{\mathrm{int}}(P_k,P_*)=
\max\{d_{\mathrm{coord}},d_{\mathrm{norm}},d_{\mathrm{obs}},
d_{\mathrm{cert}}\}
\le \varepsilon_{\mathrm{int}}(k).
\]

### B. Stable-interface contraction

Only after A, define transported operators on the common interface and prove

\[
\sup_{k\ge k_*}\|D\widetilde R_k\|\le q<1
\]

uniformly in the cutoff and throughout the certified Gaussian ball.

### C. Constructive landing

Construct an actual `k_0 >= k_*` at which the physical ultraviolet trajectory
enters that ball.  A proposition denying non-landing is insufficient.

## Split distortion budget

Every scale log must distinguish

\[
C_k^{\mathrm{dyn}}
\quad\text{from}\quad
C_k^{\mathrm{int}}.
\]

The first is the analytic scale-transformation error on the current interface;
the second is the error of interface transport.  A coherent-equivalence tail
requires separate summability of their logarithmic distortions.  The old
single constant is recovered only in the special case
`C_int = 1` definitionally.

## Relationship to the existing code

`RG/InductiveState.lean` and `computations/inductive_state.py` remain useful
scale-local packages.  They are now understood as the constant-interface
specialization.  The new module does not replace their proved budget
machinery; a production integration must index their field, polymer, norm,
observable, and certificate carriers by `RGInterface` and construct the
transport maps between adjacent scales.

The immediate analytic frontier remains the existing Core-B / physical
single-step campaign.  Its eventual theorem must consume the stabilized,
transported interface rather than assume one from the start.
