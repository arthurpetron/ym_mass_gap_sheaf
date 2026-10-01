# Quadratic floor of the even corrected Young budget

Date: 2026-10-01 UTC. This concerns the explicit UPPER-bound formula from
the retained quadratic source test. It is not a lower bound on actual
energy and does not refute a Yang--Mills scaling family.

## Formula and its consumer

For a positive raw source mass A, put x=F/A, where F is the raw
plaquette-square moment. The plaquette square cap gives 0<=x<=4.
The previous retained-square estimate

    64*A*E + (1-w^32)^2*(F-A)^2 <= 32*A*C

has C=(1-w^32)*A+(1+w^32-2*w^12)*F. Thus the displayed upper budget
for E/A is

    B(w,x) = ((1-w^32)+(1+w^32-2*w^12)*x)/2
             - (1-w^32)^2*(x-1)^2/64.

The original finite estimate is
`BF4ExactSlabFixedSpatialSourceEvenCancellation.padded_terminal_even_square`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:199`).
The collected channel formula is
`BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.plaquetteChannelCost_collected`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:106`).
The ratio discussion here requires A>0; the new scalar theorem itself takes
an arbitrary rational x in [0,4] and does not assert a new source construction.

## Polynomial argument

B is concave in x. Its excess above the chord joining x=0 and x=4 is
(1-w^32)^2*x*(4-x)/64, which is nonnegative. At x=0, with
a=1-w^32 in [0,1], 64*B=a*(32-a)>=31*(1-w)^2.

At x=4, use u=w^4 to reduce the polynomial degree:

    64*B(w,4) = 151 - 256*u^3 + 114*u^8 - 9*u^16
              = (1-u)^2 * Q(u),

where the coefficients of Q, in ascending powers, are

    151, 302, 453, 348, 243, 138, 33,
    -72, -63, -54, -45, -36, -27, -18, -9.

The negative coefficients sum to -324 and occur at powers at least seven.
The term 348*u^3 pays them because u^k<=u^3 for these exponents on [0,1].
Equivalently, Q-151 is the sum of the positive low terms with coefficient
24 at u^3 and the eight nonnegative terms
9*(8-n)*(u^3-u^(7+n)), n=0,...,7. Consequently Q>=151.
Since 1-w^4>=1-w, the x=4 endpoint also exceeds the common floor.
The chord argument then gives, for EVERY allowed x,

    B(w,x) >= 31*(1-w)^2/64.

For h=1-w>0 and 64*C*h<31, this rules out B(w,x)<=C*h^3,
including when x changes with w. It does not rule out an actual energy
bound E/A<=C*h^3 established by a stronger argument.

## Consequence for proof selection

Improving concentration of F/A alone cannot make THIS upper budget cubic.
When the consumer needs a smaller order than h^2 relative to raw source
mass, a stronger retained cancellation or a different justified observable
estimate is necessary. The theorem does not decide which physical spacing
law is correct, nor prove that every useful consumer requires cubic order.

The same-density variance and calibration issues remain as recorded in
`audits/AUDIT-ACTUAL-SOURCE-MOMENT-INPUTS-2026-10-01.md`. The raw q^2
source moments still cannot be identified with the interacting q*Pq law.
Joint odd/even tests and the complete signed Ward remainder are not ruled
out by this floor for the even-only budget.

## Checked declarations and verification

The new module is `lean/YMGap/Continuum/SU2PlaquetteEvenBudgetFloor.lean`:

- `evenBudget64`, line 48, defines 64*B with integral coefficients.
- `evenBudget64_formula`, line 66, pins the literal w^12/w^32 formula.
- `even_budget_floor`, line 303, proves the universal quadratic floor.
- `even_budget_not_cubic`, line 358, proves the precise cubic obstruction.

The final focused check exited successfully. The definition's printed gate
is axiom-free; the three theorem gates are exactly {propext, Quot.sound}.
The factorization is kernel-checked by polynomial coefficient reflection;
the independent finite coefficient calculation is not trusted as a proof.
No sorry, new axiom, Classical dependency, native_decide, noncomputable
declaration or canonical field was added.

The monitored check used one worker, a 20 GiB worker ceiling, 12 GiB OS
reserve and live pressure monitoring. Verification was serialized with
the physical subgap-module check. No full root build, tree audit or guard
was run. The root import is registered but not checked as an aggregate.
No canonical chart state changed or was reprinted.

Final log: `/tmp/ym-even-budget-floor-20261001.log`.
SHA-256: `affa76db4ed595f9bb75d9dc7843328e5ae44bb30145529a1b70d7512ce49d3a`.
