# Next rational calibration: existing constructive data, not a new input

This is a source-grounded proof plan, NOT a checked calibration theorem.
It was reviewed while the original polynomial-test check ran. No compiler
or routine literature scan was launched for this note.

## The data-level witness is already available

For a supplied rational `0 < eta < 1`, the proposed next construction is

    N = sqrtModulus eta eta hEta hEta (3/2) hThreeHalves
    x = heronSeq eta N
    rho = divPos eta x (heronSeq_pos hEta N).

The source producers are `CReal.sqrtModulus` in
`lean/YMGap/Constructive/Sqrt.lean:958`, `CReal.errAt_modulus_le` (`:964`),
`CReal.heronSeq` (`:238`) and `CReal.heronSeq_pos` (`:256`); positive rational
division is `Q'.divPos` in
`lean/YMGap/Constructive/RegularCRealArith.lean:105`.
The namespace of the Heron declarations is `YMGap.Constructive.CReal`.

The modulus theorem bounds the error by `(eta+eta)*(3/2) = 3*eta`.
Together with `CReal.heronSeq_sq_ge` (`Sqrt.lean:571`), the proposed
algebra gives `eta <= x*x <= 4*eta`, hence
`eta/4 <= rho*rho <= eta`. These algebraic joins and `0 < rho < 1`
still need Lean proofs. They are not new assumptions to ledger as analytic
inputs: the intended witness N is already an explicit Nat-valued function.

In particular, the Prop-valued `CReal.errAt_eventually_small`
(`lean/YMGap/Constructive/Sqrt.lean:1029`) is not evidence that this witness
is missing. Its proof also constructs `mulModulus(...).1.den` explicitly;
`CReal.mulModulus` (`:936`) returns Sigma data. Do not extract a Nat by
choice or add a fresh calibration field merely because the eventual-form
theorem has an existential statement.

## Intended consumer and remaining joins

With this rational rho the proposed parameters are

    qbar = 1-rho*rho
    r = (1+rho)/(1-rho), s = (1-rho)/(1+rho).

The scalar identities to prove are `r*s=1`, `0<s<1` and
`2/qbar-1=(r+s)/2`. The checked `T_center_recip_le` in
`lean/YMGap/Continuum/ChebyshevReciprocalPair.lean:165` then bounds the
positive normalizing reciprocal by `2*s^n`.

This does not construct the original centered coercivity constant or eta.
The actual rescaled-operator contraction, the polynomial cone/covariance
join, useful spatial and physical-spacing control, OS/Hamiltonian passage,
and the continuum/every-group Clay target remain open. The full construction
and these parameter identities are future work, not proved by this note.
