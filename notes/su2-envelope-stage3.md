# The envelope lemma, stage three: the majorant-series envelope (work_plan §17c)

Companion note to `computations/su2_envelope3.py`.  Executes the §17b
"next lever" — the route the plan ranked as polydisc-Cauchy → tau^4 law →
P2 — in the form the analysis showed is strictly stronger than both of
the first two items.

## The structural move

Stages one/two bound the whole remainder-after-tau^3 by ONE Cauchy tail
at order 8, paying (cM/r0)^8 with r0 ~ 4e-3 pinned by the insertion
budget: ~1e21 of structural loss.  Stage three observes that the middle
Taylor coefficients a_k (k = 8, 10, ..., N) of the entry function
T(eta) = E[A(eta;xi)] are plain global Gaussian moments — no analyticity
needed — and bounds each by an exact-rational majorant m_k built from a
positive-coefficient composition:

* the integrand factorizes: (character trace) x (16 link Haar factors)
  x (20 face Jacobians) x (multi-letter face action factors exp(-g_f));
* each factor's eta-coefficients are dominated by explicit series with
  positive coefficients in per-face/per-link field atoms:
  - g_f per order: cubic = 2 t3_f (the §17b triple-product sums — ZERO
    on 16 of 20 faces), quartic = p_f^2 + 2 s_f d3_f with (p_f, d3_f)
    exact per-face constants from the labelled BCH fold (repeated-link
    top-level brackets dropped), quintic mixed, >= sextic by the
    Goldberg/Dynkin scalar closure [z^i](f^2 - z^2), f = -log(2-e^z);
  - Jacobian z/sin z (positive z^2-coefficients) composed with the
    phi^2 majorant (cubic refined by t3_f); Haar dominated by
    (sinh u/u)^2; character by an exp majorant;
* monomial expectations close by pooled Hoelder
  E[prod chi^{a_i}] <= E[chi^D] (chi = chi_3; even moments exact
  rationals, odd <= (4/5) 2^{m+1}(m+1)!).

The log-composition to X_11 uses the majorant log Lambda =
-log(1 - sum m_k z^k).  Only the ultra-tail (orders > N) still uses the
stage-two Cauchy machinery (re-optimized per order), plus the
large-field, LF-polynomial (new — see below), and image shells.

## The theorem

    |X_11(tau) - 6 tau^2 - (115/6) tau^3| <= R_X(tau)  on (0, tau*],
    tau* = 2^-44   (N = 12, kappa = 1/9),
    R_X(tau*)/tau*^2 = 0.875 <= 3   =>   X_11 > 0 on (0, 2^-44],

with R_X/tau^2 nondecreasing (each summand is, on the asserted shell
domains), so one exact check certifies the whole interval.  Progression
(all sound, post-repairs): stage one 2^-82, stage two 2^-61, stage
three 2^-44 — a 2^17 jump from the majorant route, 2^38 from the §17b
release.  U(1) mirror: R_X^{U1}(tau*) ~ 1.1e-44 << 8 tau*, so the
separation X_SU2 > 0 > X_U1 stands on the common interval, now with the
mirror's majorants gated against the EXACT abelian coefficients
(V-hat = 8 from (G^-1), coefficients 4^j/j!).

## The second repair (§17c, honesty)

Stages one/two consumed the eta^8 Cauchy tail as K_small * tau^4,
dropping the 8^4 of eta^8 = (8 tau)^4.  Both modules now carry
ETA8 = 8^4 explicitly: stage one 2^-76 -> 2^-82 (coincidentally the
unsound §17a headline), stage two 2^-55 -> 2^-61, mirror K_U1 ->
3.14e10.  Stage three's powers are exact by construction.  Also made
explicit: the E[1_LF |poly-coeff|] piece of the large-field split
(closed by Cauchy-Schwarz with L^2 majorants mL2_k), which stages
one/two absorbed silently in shell slack — at their tau* it is
~e^{-3e7}, genuinely negligible, but it belongs in the ledger.

## Gates (all green)

g_fold (labelled majorants dominate the exact vector BCH fold per face
on rational vectors), g_dynkin numeric (mpmath matrix logs, t-grading
Vandermonde fit: exact grades 2-4 under a_k sigma^k on the real face
words), g_moments (mu uppers vs mpmath chi_3), g_series (positivity +
z/sin z Taylor match + haar domination), g_u1_exact (majorants dominate
the exact abelian coefficients), g_star (stage-one mechanism gate),
g_dominate (stage three > stage two).  Suite: envelope tests 15/15.

## What binds now, ranked

1. The m_8/Lambda_8 term itself: the pooled-Hoelder step E[prod chi^a]
   <= E[chi^D] ignores monomial spread across near-independent atoms
   (~1e4 loss at degree 16).  Sharp product moments (Wick/Isserlis
   trace formulas for quadratic-form atoms, or a Cauchy-Schwarz tree)
   are the next constant lever inside m_k.
2. The large-field shell exp(-r0^2/(128 cM^2 tau)) caps any series
   improvement at tau ~ 2^-30±3 for budget-admissible r0: the fix is
   compact-domain (owned-boundary) large-field bounds — image
   technology, not more orders.
3. The matched-flow form 1 < tau'/tau <= 1 + c tau: the diagonal
   kappa_3 or the P2 iterated-map consumer.  The exact tau^4 cross law
   is now needed only for MD.4 curvature sharpness, not positivity.

Cloud only; no Lean in this stage; push owed.
