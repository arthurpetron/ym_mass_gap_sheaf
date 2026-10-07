# Scope: trace route on the strong-coupling carrier (2026-10-06 PT)

- PROVED (non-vacuity, CIRCULAR link): `scFamily_lowerMargin_via_trace`. The model
  `rateModel` has λ₀ = timeRate by construction; no new spectral information.
- PROVED no-go: the genuine heat-kernel model `excitedCharModel w N` has specMax ≤ w³ <
  timeRate at w = 1/1024, so it cannot serve as S in `hlink`.
- PROVED finite: `midModel_interval` (w = 1/2, 3 excited spins), certified by
  `specMax_mem_of_trace_bounds` with n = 1. Certifies the closed-form model only.
- MISSING for a genuine intermediate-coupling certificate: a `WilsonDynamicFamily` rate at
  w = 1/2 (the strong-coupling guards fail there) and a proved link
  rate ≤ specMax (needs `CharacterDiagResolution`, OPEN).
- U(1) rule: the trace algebra and rateModel are group-blind; scFamily is the SU(2)
  quaternion carrier at strong coupling (U(1) also has strong-coupling decay), so the
  non-vacuity result is group-blind in content and says nothing at large β. No large-β
  claim is made, so nothing is refuted.
