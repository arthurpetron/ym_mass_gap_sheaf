"""Moduli vector — the single algebraic object collapsing §2.1's 10 moduli.

Manuscript Ch. 1.5 of `docs/outline.md` Part B (authorized 2026-05-26):
collapse the 10 named moduli of `docs/outline.md` §2.1 into a single
`ModuliVector` with a `registry_inequality` propagating through the
construction.

# Why

`docs/outline.md` §2.1 lists 10 registered moduli (5 ε-approximation
budgets + 5 structural lower-bound quantities) one at a time, each with
its own role in the construction.  Reviewers and authors alike had to
track 10 disconnected entities.  The `ModuliVector` packages them as
**one algebraic object** with a single registry inequality:

    Σ ε_i ≤ tolerance                       (approximation budget closure)
    0 < σ_phys ≤ σ̂_k                        (renormalized string tension survives)
    0 < m_∞² ≤ σ_phys                       (mass-from-clustering chain)
    m_∞ ≤ m_0                                (continuum-stable mass)

The single inequality chains all five structural moduli + the five ε
moduli into one propagation, making "the moduli registry" a concrete
algebraic object the reader can track.

# The 10 moduli (per `outline.md` §2.1)

  * `eps_UV` — UV modulus ε_UV(r, a).
  * `eps_IR` — IR modulus ε_IR(r, L).
  * `eps_RG` — RG truncation modulus ε_RG(r, k).
  * `eps_cap` — buffer-overlap gluing modulus ε_∩(r, k).
  * `eps_num` — numerical-approximation modulus ε_num(r, N).
  * `sigma_0` — bare area-law modulus σ_0(G, a, L, R).
  * `sigma_hat_k` — renormalized string-tension modulus σ̂_k = a_k² σ_k.
  * `sigma_phys` — uniform physical string-tension lower bound σ_phys(G) > 0.
  * `m_0` — finite-regulator clustering modulus m_0(G, a, L).
  * `m_inf` — continuum-stable clustering modulus m_∞(G, r) > 0.

# What this module does NOT do

Collapsing the moduli into one vector is **presentation**, not new
analytical content — the manuscript chapter docstring is explicit about
this.  The Python module mirrors the Lean `ModuliAlgebra.lean` and
provides:

  * A frozen dataclass with the 10 fields + validation.
  * A `registry_inequality(tolerance)` method returning a structured
    pass/fail report.
  * Named pilot instances (`canonical_pilot_moduli`,
    `wilson_pilot_moduli`) populated from the actual SU(2) pilot data.

For the manuscript-level claim "the 10 moduli form a single algebraic
object", the Lean-side `ModuliAlgebra.lean` is the load-bearing
artefact (with axiom-clean `decide` proofs at Q'); this Python module
is the friendly mirror for downstream consumers.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class RegistryInequalityResult:
    """Structured pass/fail outcome of `ModuliVector.registry_inequality`.

    Each field corresponds to one clause of the registry inequality
    chain.  `passes` is True iff every clause is satisfied; otherwise
    the failing clause(s) are listed in `failed_clauses`.
    """

    epsilon_total_le_tolerance: bool
    """Σ ε_i ≤ tolerance: approximation budget closure."""

    sigma_phys_positive: bool
    """0 < σ_phys: existential physical string-tension lower bound."""

    sigma_hat_k_ge_sigma_phys: bool
    """σ_phys ≤ σ̂_k: renormalized string tension survives RG."""

    m_inf_positive: bool
    """0 < m_∞: clustering bound is non-trivial."""

    m_inf_squared_le_sigma_phys: bool
    """m_∞² ≤ σ_phys: mass-from-clustering chain (Wilson loop → mass)."""

    m_inf_le_m_0: bool
    """m_∞ ≤ m_0: continuum bound dominates finite-regulator bound."""

    @property
    def passes(self) -> bool:
        """All clauses pass."""
        return (
            self.epsilon_total_le_tolerance
            and self.sigma_phys_positive
            and self.sigma_hat_k_ge_sigma_phys
            and self.m_inf_positive
            and self.m_inf_squared_le_sigma_phys
            and self.m_inf_le_m_0
        )

    @property
    def failed_clauses(self) -> tuple[str, ...]:
        """Names of clauses that failed (empty if `passes` is True)."""
        clauses = (
            ("epsilon_total_le_tolerance", self.epsilon_total_le_tolerance),
            ("sigma_phys_positive", self.sigma_phys_positive),
            ("sigma_hat_k_ge_sigma_phys", self.sigma_hat_k_ge_sigma_phys),
            ("m_inf_positive", self.m_inf_positive),
            ("m_inf_squared_le_sigma_phys", self.m_inf_squared_le_sigma_phys),
            ("m_inf_le_m_0", self.m_inf_le_m_0),
        )
        return tuple(name for name, ok in clauses if not ok)


@dataclass(frozen=True)
class ModuliVector:
    """**The moduli vector** — the single algebraic object collapsing
    `docs/outline.md` §2.1's 10 moduli (manuscript Ch. 1.5, 2026-05-26).

    Fields are nonneg-rational quantities organized into two groups:

    Group 1 — ε approximation moduli (upper bounds, summed to ε_total):
      * `eps_UV` — UV modulus.
      * `eps_IR` — IR modulus.
      * `eps_RG` — RG truncation modulus.
      * `eps_cap` — buffer-overlap gluing modulus.
      * `eps_num` — numerical-approximation modulus.

    Group 2 — structural moduli (positive lower bounds, propagated by
    the registry inequality):
      * `sigma_0` — bare area-law modulus σ_0(G, a, L, R).
      * `sigma_hat_k` — renormalized string-tension modulus σ̂_k.
      * `sigma_phys` — uniform physical string-tension lower bound.
      * `m_0` — finite-regulator clustering modulus.
      * `m_inf` — continuum-stable clustering modulus.

    The `registry_inequality(tolerance)` method checks the chained
    propagation per `outline.md` Ch. 1.5 §"Registry inequality"."""

    # Group 1: ε approximation moduli.
    eps_UV: float
    eps_IR: float
    eps_RG: float
    eps_cap: float
    eps_num: float

    # Group 2: structural moduli.
    sigma_0: float
    sigma_hat_k: float
    sigma_phys: float
    m_0: float
    m_inf: float

    def __post_init__(self) -> None:
        for name in (
            "eps_UV", "eps_IR", "eps_RG", "eps_cap", "eps_num",
            "sigma_0", "sigma_hat_k", "sigma_phys", "m_0", "m_inf",
        ):
            val = getattr(self, name)
            if val < 0:
                raise ValueError(f"{name} must be nonneg; got {val}")

    @property
    def epsilon_total(self) -> float:
        """Σ ε_i = ε_UV + ε_IR + ε_RG + ε_∩ + ε_num: total approximation budget."""
        return (
            self.eps_UV
            + self.eps_IR
            + self.eps_RG
            + self.eps_cap
            + self.eps_num
        )

    def registry_inequality(self, tolerance: float) -> RegistryInequalityResult:
        """Check the registry inequality chain at the given tolerance.

        Returns a `RegistryInequalityResult` listing pass/fail of each
        clause.  See the class docstring for the chain.
        """
        if tolerance <= 0:
            raise ValueError(f"tolerance must be positive; got {tolerance}")
        return RegistryInequalityResult(
            epsilon_total_le_tolerance=self.epsilon_total <= tolerance,
            sigma_phys_positive=self.sigma_phys > 0,
            sigma_hat_k_ge_sigma_phys=self.sigma_phys <= self.sigma_hat_k,
            m_inf_positive=self.m_inf > 0,
            m_inf_squared_le_sigma_phys=(self.m_inf * self.m_inf) <= self.sigma_phys,
            m_inf_le_m_0=self.m_inf <= self.m_0,
        )


# --------------------------------------------------------------------------
# Pilot instances
# --------------------------------------------------------------------------


# Canonical-pilot moduli values, sourced from:
#   * eps_* — small ε contributions (~1% each); placeholder uniform
#             allocation consistent with the constructive-law obligation.
#   * sigma_0 = 1.0 — the canonical pilot σ̂_0 = 1.
#   * sigma_hat_k = 9991/10000 — post-c_λ-Casimir-gap derivation.
#   * sigma_phys = 9991/10000 — uniform lower bound at the same value.
#   * m_inf = m_0 = 999/1000 — the constructive mass-gap bound
#                              (post-c_λ-upgrade).
canonical_pilot_moduli: ModuliVector = ModuliVector(
    eps_UV=0.01,
    eps_IR=0.01,
    eps_RG=0.01,
    eps_cap=0.01,
    eps_num=0.01,
    sigma_0=1.0,
    sigma_hat_k=9991.0 / 10000.0,
    sigma_phys=9991.0 / 10000.0,
    m_0=999.0 / 1000.0,
    m_inf=999.0 / 1000.0,
)
"""Canonical-pilot moduli vector at g_0 = 0.30, K = 3.

Values sourced from the Phase-3 / Phase-7.1 pilot data
(`mass_gap_bound.py::canonical_mass_gap_bound`) plus uniform
ε-allocation at 1% each.  At tolerance = 0.1, the registry inequality
passes all clauses."""


wilson_pilot_moduli: ModuliVector = ModuliVector(
    eps_UV=0.01,
    eps_IR=0.01,
    eps_RG=0.01,
    eps_cap=0.01,
    eps_num=0.01,
    sigma_0=1.0,
    sigma_hat_k=9997.0 / 10000.0,
    sigma_phys=9997.0 / 10000.0,
    m_0=999.0 / 1000.0,
    m_inf=999.0 / 1000.0,
)
"""Wilson-pilot moduli vector at g_0 = 0.50, K = 3."""
