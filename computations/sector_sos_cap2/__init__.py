"""INDEPENDENT-REPLICATION TOOLING for the sector-SOS certificate
(work_plan §17g, notes/sector-sos-positivity.md).

STATUS: gated, NOT yet pinned in the test suite.  `spinnet` (the fast
exact rational spin-network evaluator) is gated BIT-FOR-BIT against the
incumbent evaluator `computations.dp3_fixed_tile.network_value_fixed` on
all 171 cap<=1 configurations, 320 character-orthogonality identities and
130 random networks (see `xcheck2`), and the cap<=1 family it rebuilds
reproduces `computations.sector_sos` exactly.  It exists only to build the
DISJOINT cap<=2 family (187 sectors) used as the independent replication
gate; nothing on the certificate's critical path depends on it.  Pinning
these modules in `tests/` is a named follow-up.
"""
