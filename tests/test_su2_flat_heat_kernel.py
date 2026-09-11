"""Pins for the exact flat (image-sum) representation of the SU(2)
heat kernel (work_plan §16d) — the SU(2) analogue of the abelian
Poisson step and the entry point of the c_SU2 derivation."""

from computations.su2_flat_heat_kernel import (
    character_projection_gate,
    heat_image_sum,
    identity_gate,
    normalization_gate,
)


def test_identity_40_digits():
    ok, worst = identity_gate(40)
    assert ok, f"worst rel {worst}"


def test_haar_normalization():
    ok, worst = normalization_gate(35)
    assert ok, f"worst rel {worst}"


def test_character_projection():
    ok, worst = character_projection_gate(30)
    assert ok, f"worst rel {worst}"


def test_small_tau_flat_dominance():
    # at tau -> 0 the j = 0 image dominates: K ~ e^tau sqrt(pi)
    # * phi / (4 tau^{3/2} sin phi) * e^{-phi^2/(4 tau)}
    import mpmath as mp
    tau = mp.mpf("0.05")
    phi = mp.mpf("0.7")
    k = heat_image_sum(phi, tau)
    lead = (mp.e ** tau * mp.sqrt(mp.pi) * phi
            / (4 * tau ** mp.mpf("1.5") * mp.sin(phi))
            * mp.e ** (-phi * phi / (4 * tau)))
    assert abs(k / lead - 1) < mp.mpf("1e-30")
