"""Long-running verification drivers that strengthen the manuscript.

Each module here is a self-contained driver that runs an expensive
computation (minutes to hours) to extend a manuscript claim past the
fast-iteration scale used elsewhere in `computations/`.  Results are
written as JSON sidecars next to a regenerated SVG/PDF so the
manuscript can cite them once they're produced.

Modules:
  * `uv_decay_ultra_long_k`     — Theorem 15.3.1 at K = 10^5
  * `g0_phase_boundary_scan`    — convergent-regime boundary at fine
                                  g_0 resolution
  * `m0_bootstrap_high_n`       — Appendix D bootstrap at N = 10^6
  * `mcmc_continuum_scan`       — Wilson-action SU(2) MCMC at 8^4, 12^4
                                  for a wider β grid

Each module exposes a top-level `main()` and can be invoked as

    python -m computations.long_runs.<module_name>

with `--help` for any per-run knobs.
"""
