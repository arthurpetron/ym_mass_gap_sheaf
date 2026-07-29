"""Pins for the P2 matched-flow consumer at depth 2 (work_plan §17f)."""

from fractions import Fraction as F

from computations.p2_matched_flow import (
    envelope_windows,
    gate_sigma_squared,
    gate_su2_psd_sigma,
    gate_u1_parity,
    pair01_su2,
    pair01_u1,
    t2_window_full,
    tau_ratio,
    u1_envelope,
)


def test_d1_theorem_code_path_and_banked_object():
    """sigma(A^2) = sigma(A)^2 through the Sturm path, and the banked
    M = 1 SU(2) Gram is PSD with exact sigma^2 covariance."""
    assert gate_sigma_squared()
    psd, eq, sig, sig2 = gate_su2_psd_sigma()
    assert psd and eq
    assert sig[0] > 0


def test_u1_conjugated_gram_breaks_sigma_covariance():
    """The banked VERDICT: on the abelian conjugated Gram the depth-2
    separator falls strictly BELOW sigma^2 (parity-odd second
    channel), M-stable — depth-2 separator content exists for U(1)
    and not for the composed SU(2) kernel."""
    eq2, sig, sig2 = gate_u1_parity(2)
    assert not eq2
    assert sig2[1] < sig[0] ** 2          # strictly below, certified
    eq3, _, _ = gate_u1_parity(3)
    assert not eq3


def test_su2_certified_composition_drift_at_half():
    """The headline at s = 1/2: tau'/tau and tau''/tau both certified
    in (3.99, 4.0) (strictly below the 2D rule), and the composition
    drift is CERTIFIED POSITIVE but tiny — s'' < s' with the windows
    disjoint, drift ~ 1.7e-5 in tau''/tau - tau'/tau — the same
    direction as the abelian mirror's exact drift (~+7.5e-2), with a
    ~4000x certified magnitude separation.  Scheme-covariant: the
    {0,1} control basis certifies the same sign."""
    from computations.p2_iterated import entry_windows
    s = F(1, 2)
    ew = entry_windows(s)
    tw = t2_window_full(s, ew)
    for basis in ((0, 1, 2), (0, 1)):
        v1 = envelope_windows(ew, s, basis)
        v2 = envelope_windows(tw, s, basis)
        _p1, sp1 = pair01_su2(v1)
        _p2, sp2 = pair01_su2(v2)
        t1 = tau_ratio(sp1, s)
        t2 = tau_ratio(sp2, s)
        assert 3.99 < t1[0] and t1[1] < 4.0
        assert 3.99 < t2[0] and t2[1] < 4.0
        # certified drift: s'' < s' strictly (windows disjoint)
        assert sp2[1] < sp1[0]
        # and tiny: below 1e-4 in the tau-ratio
        import math
        d_hi = (math.log(float(sp2[0]))
                - math.log(float(sp1[1]))) / math.log(float(s))
        assert d_hi < 1e-4
    # U(1) mirror at the same s: certified POSITIVE drift ~ 7.5e-2 —
    # same sign, three-to-four orders larger
    pu1 = pair01_u1(u1_envelope(s, 1))
    pu2 = pair01_u1(u1_envelope(s, 2))
    assert pu2[1] < pu1[0]                # s'' < s' exact lane
    u1 = tau_ratio(pu1, s)
    u2 = tau_ratio(pu2, s)
    assert u2[0] > u1[1] + 0.05           # abelian drift magnitude
