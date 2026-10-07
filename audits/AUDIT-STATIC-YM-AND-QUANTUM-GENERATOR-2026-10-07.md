# Static Yang--Mills, torus holonomy and the quantum generator (2026-10-07)

Whole-project goal unchanged and OPEN: nontrivial quantum Yang--Mills on R^4
for every compact simple group, SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap, constructively formalized in Lean.

The user-supplied static/Maxwell/torus/spinor discussion was reviewed by a
bounded parallel source reviewer and checked against primary sources. This
is a scope correction and work-plan update, not a new Lean theorem.

## Retained distinction

A classical fixed point of Hamiltonian evolution is not a limit setting the
quantum Hamiltonian to zero. The target Hamiltonian generates time
translations on the reconstructed quantum Hilbert space; its spectrum above
the vacuum, not the value of magnetic energy on classical static fields,
defines the required mass gap. This is explicit in Jaffe--Witten, sections
3--4 of the [official Clay problem statement](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf).

Use the classical equations only as consistency checks or analytic tools
when a concrete SAME-action consumer is identified. Do not remove electric
fluctuations, quantum excited states, continuous-time reconstruction or
physical mass calibration from the target. Setting a field's time derivative
to zero and constructing a short-time generator are different tasks.

## Corrections before reuse

- Keep the static equation as `d_A^* F_A=0` (equivalently `d_A * F_A=0`
  with the metric/sign conventions fixed). It is the Yang--Mills variational
  equation, not the stronger assertion `nabla_A F_A=0`. Bianchi is a separate
  identity. The explicit variation and equations are in
  [Beiner, sections 2--3 and Proposition 5.1](https://math.berkeley.edu/~gbeiner/papers/Yang_Mills.pdf).
- Commuting holonomy triples describe the FLAT torus sector with the
  appropriate bundle/global-form conditions, not the full interacting
  theory. Twisted sectors and non-toral commuting triples require care;
  [Selivanov--Smilga](https://arxiv.org/abs/hep-th/0010243) construct such flat
  vacua. No general nonflat reconstruction from curvature and just three
  holonomies is imported. The proved reconstruction framework uses a
  holonomy map on the loop space with explicit axioms:
  [Hajac](https://arxiv.org/abs/math-ph/9809019).
- Self-dual two-forms act on positive spinors as TRACELESS endomorphisms,
  not generally scalar endomorphisms. Gauge twisting adds the associated
  representation factor. See [Atiyah--Hitchin--Singer, section 1, p. 429](https://www.math.miami.edu/~cscaduto/teaching/782-fall-2023/notes/AHS.pdf).
  No Weitzenbock coefficient is adopted without fixed conventions; a coupled
  spinor-field system is not substituted for pure Yang--Mills.

## Existing code consumers and honest boundary

- `lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, `PositiveTimeOSRoot`,
  pins the physical state form to reflected positive-time observables. Its
  fields are requirements, not an inhabitant for continuum 4D Yang--Mills.
- `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraph.lean:76`, `GraphLimit`,
  retains simultaneous source/output graph convergence moduli for the
  original regularized time series. The module explicitly does NOT claim a
  full-carrier densely defined physical Hamiltonian or continuous-time
  generator. Static geometry does not fill that missing identification.
- `lean/YMGap/Continuum/TorusWilsonAction.lean:247`, `holonomy`, and `:261`,
  `wilsonAction`, retain literal plaquette holonomy and the full torus action.
  `lean/YMGap/Continuum/SU2TorusCenteredFiniteRatio.lean:33`,
  `actual_torus_ratio`, is a finite interacting response inequality. Neither
  construction restricts the action to flat commuting triples.

Decision: add these scope guards to the existing work plan; do not launch a
new static-moduli or spinor formalization without a missing quantum analytic
input it actually supplies. Continue the original signed-cost and AF/RG
producer work. No classical axiom, new frontier field, proof-status change,
routine arXiv listing scan or additional compilation is introduced by this
review.
