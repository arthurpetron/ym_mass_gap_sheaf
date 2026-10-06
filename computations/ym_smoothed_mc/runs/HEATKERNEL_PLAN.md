# Heat-kernel action: feasibility plan (ON HOLD per YM Bot, 2026-10-06; nothing implemented)

## Target: the repo carrier
From the repo:
- `docs/fieldspace-2026-07-06.md`
- `lean/docs/rg-transport-notes.md` (`RGTransport.lean:45`)
- `docs/fusion_logconcave.md`

Per-plaquette weight (character expansion, s = 2j):

    K_w(U) = sum_{s>=0} (s+1) w^{s(s+2)} chi_s(U),   chi_s(U) = sin((s+1)theta)/sin(theta),  U ~ diag(e^{i theta}, e^{-i theta})

Here w = e^{-t/4} is the weight per Casimir unit, s(s+2) = 4 C_2(j), and the carrier time is **t = -4 log w** (this is what the repo docs call "g^2"; the standard Wilson coupling is g_W^2 = 2t, see below). So K_w = sum_j (2j+1) e^{-t j(j+1)} chi_j: the SU(2) heat kernel at time t. K_w > 0 for all theta, and E chi_s = (s+1) w^{s(s+2)}. This matches the repo's `charFunc`/`coeffW`.

**Coupling convention (corrected 2026-10-06, P7b; confirmed by YM Bot): the carrier heat-kernel time is t = -4 log w, and the STANDARD Wilson coupling is g_W^2 = 2t = -8 log w (A ≈ 1.942).** Below, beta_W = 4/g_W^2 at leading order.

Weak coupling: Poisson resummation gives K_w(theta) ∝ (theta/sin theta) e^{-theta^2/t} (1 + O(e^{-pi^2/t})). Compared with Wilson e^{beta cos theta} ≈ e^{beta} e^{-beta theta^2/2}, this gives beta_W ≈ 2/t = 4/g_W^2. That is consistent with g_W^2 = 2t: the leading-order map is w_LO = exp(-g_W^2/8) = exp(-1/(2 beta_W)).

## beta_W ↔ w mapping
There are two maps:
- **Character (one-plaquette) matching:** equate the normalized fundamental coefficients, e^{-3t/4} = I_2(beta)/I_1(beta). The table quotes the matched carrier t and the standard g_W^2 = 2t.
- **Leading-order map:** g_W^2 = 4/beta_W.

| beta_W | I2/I1 | carrier t = -4 log w | g_W^2 = 2t = -8 log w (matched) | w (matched) | g_W^2 LO = 4/beta | w_LO = e^{-1/(2 beta)} |
|---|---|---|---|---|---|---|
| 2.30 | 0.47928 | 0.9806 | **1.9613** | 0.78258 | 1.7391 | 0.80462 |
| 2.50 | 0.50720 | 0.9051 | **1.8103** | 0.79749 | 1.6000 | 0.81873 |
| 2.60 | 0.52034 | 0.8710 | **1.7421** | 0.80432 | 1.5385 | 0.82505 |
| 2.70 | 0.53297 | 0.8391 | **1.6781** | 0.81078 | 1.4815 | 0.83095 |
| 2.85 | 0.55098 | 0.7947 | **1.5895** | 0.81981 | 1.4035 | 0.83909 |
| 2.95 | 0.56239 | 0.7674 | **1.5348** | 0.82543 | 1.3559 | 0.84409 |
| 3.00 | 0.56792 | 0.7544 | **1.5087** | 0.82813 | 1.3333 | 0.84648 |

So our Wilson window beta 2.5-3.0 corresponds to w ≈ 0.797-0.828 (matched) or 0.819-0.846 (LO), with standard g_W^2 ≈ 1.81-1.51 (matched) or 1.60-1.33 (LO). The matched and LO maps differ by 0.02 in w (13% in g_W^2). Neither replaces a t0 scale determination at the HK points.

## Update algorithm (fits the existing p4run structure)
The single-link conditional density is prod over the 6 plaquettes p containing U of K_w(U V_p). Unlike Wilson, it does not depend on U only through Re tr(U A).
1. **Tabulate** S(theta) = -log K_w(theta) on a fine grid (for example 2^16 points in [0, pi]) with cubic interpolation.
   - Use the character sum, truncated at s_max with w^{s(s+2)} < 1e-18. That is s_max ≈ 2 sqrt(41/t) ≈ 15 for t ≈ 0.75.
   - Alternatively use the Poisson-resummed form, which is faster for small t.
   - Check the table against direct summation to 1e-13.
2. **Heatbath-Metropolis:**
   - Proposal: U' from the existing Kennedy-Pendleton heatbath, using the staple sum A and beta_eff = 4/g_W^2 = 2/t (tuned for acceptance).
   - Accept with min(1, exp(-sum_p [S(theta_p(U')) - S(theta_p(U))] + beta_eff Re tr[(U - U') A]/2)).
   - This is an exact independence-Metropolis step with respect to the HK weight. Expected acceptance is about 85-95% at t ≈ 0.75, where the HK and Wilson plaquette distributions differ mostly in the tails.
3. **Overrelaxation:** the Wilson reflection U → V U^† V (V = A/|A|) is not microcanonical for HK. Apply it as a proposal with a Metropolis accept on ΔS_HK. It is cheap and keeps the decorrelation benefit; acceptance is expected above 90%.
4. **Checkerboard / threading:** unchanged, since the update stays link-local (6 plaquettes). The cost is about 1.5-2x a Wilson sweep: 6 plaquette traces, 12 table lookups and one accept per link.
5. **New flags:** `--action hk --nome w` (or `--t`), with `w` written in the header. The spatial flow, loops and analysis are unchanged.

## Validation (before any production)
- **Exact limits:** on 2^4 and 4^4 lattices, check strong coupling (t large, <plaq> → e^{-3t/4} at leading order) and weak coupling (t → 0) against the character expansion and perturbation theory.
- **Detailed balance:** single-link histogram test against the exact conditional density (chi^2 on a 1-link system with frozen staples).
- **Wilson cross-check:** at the matched t(beta = 2.5), <plaq> and the t0/a^2 scale should be close to Wilson beta = 2.5 (known Menotti-Onofri closeness); quantify the residual.

## Cost
- Coding: about 0.5 day. Validation: about 0.5 day.
- Compute: one 24^3x32 HK point plus one t0 measurement takes about 1-1.5 h at 3 threads (sweeps 1.5-2x Wilson). A 2-nome check (w ≈ 0.80, 0.82, i.e. g_W^2 ≈ 1.78, 1.59) is about 3 h.

## Not started; held pending the anchor/carrier decision.
