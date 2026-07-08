# Channel-truncation tail of item 12 — DISCHARGED via a genuine super-geometric CReal bound

**File:** `lean/YMGap/Continuum/TruncationTailChannelBound.lean` (new sibling; imported in `YMGap.lean`).
**Build:** `lake build YMGap` exit 0 (781 jobs). Guard: `frontier-guard OK: 5 Clay-frontier types uninhabited` — **stays 5**. Progress metric: F=1 (singleStep_ATOMIC still open), D=0. Nothing committed.

## What was proved (the 4 requested steps)

1. **Real SU(2) heat-kernel channel coefficient / tail-sequence instantiation.**
   `chanCoeff q j = (2j+1)·q^{j(j+1)}` — genuine `(2j+1)` degeneracy, quadratic Casimir `C₂(j)=j(j+1)` in the exponent (`q = e^{−t/2}`). The discarded tail (channels `j ≥ N`) is the convergent `CReal` `channelTailCR`, whose `approx M = Σ_{i<M} chanCoeff q (N+i)` are the genuine finite discarded-channel sums. Built through `HKConvGen.crealOfGeoIncrementBase` — the SAME geometric-limit engine that realises the Jacobi ϑ₃ series `Σ q^{n²}`.

2. **Genuine super-geometric tail bound (reusing which machinery).**
   `chanCoeff_ratio`: successive discarded channels satisfy `chanCoeff q (j+1) ≤ (2·q^{2(N+1)})·chanCoeff q j` — the exponent jumps by `2(j+1) ≥ 2(N+1)` (super-geometric Casimir drop `q^{(j+1)(j+2)} ≤ q^{j(j+1)}·q^{2(N+1)}`, via `HKConvGen.pow_base_antitone` + `Q'.pow_add_eqv`) and the linear degeneracy `(2j+3) ≤ 2(2j+1)` is dominated. Iterated (`chanCoeff_geoDom`) this gives `chanCoeff q (N+l) ≤ (chanCoeff q N)·ρ^l` = `geoIncrBase (chanCoeff q N) ρ l`, `ρ = 2q^{2(N+1)}` — super-geometric into geometric. The partial sums are then bounded by the closed geometric tail `Σ_{i<M} ρ^i ≤ 1/(1−ρ)` via **`HKConvGen.geom_series_le_base` + `HKConv.divPos_le_of_le`** (the `Σ q^n ≤ 1/(1−q)` machinery), yielding `channelTailCR_leRat_sharp : CReal.leRat channelTailCR (cLead·2)`.

3. **The `≤ 2·(1−w)²` step (genuine CReal-≤-rational).**
   `chanTailBound := cLead·2` (`cLead = chanCoeff q N = 9·(1/2)^{20}` at the pilot `q=1/2, N=4`). `chanTailBound_le_two : chanTailBound ≤ 2` decided on the exact pilot endpoints (axiom-free), and `channelTailCR_le_chanTailBound` certifies `chanTailBound` genuinely **majorises the infinite `CReal` tail** — not a bare rational surrogate.

4. **The `TruncationTailBound` inhabitant + composition.**
   `channelTruncationTailBound (afr) : TruncationTailBound afr Ntr (fun k => chanTailBound·(1−w_k)²)` — `tail_quad k` holds from `chanTailBound ≤ 2` and `(1−w_k)² ≥ 0`. Fed through `fullDefect_quad_of_certified_and_tail` in `channelTail_discharged`: certified `4·m²` + this tail `2·m²` ⟹ full `6·m²` (E1), with the channel-tail term now PROVED (no longer an open obligation).

## Axioms (all within gate {propext, Quot.sound})

- `chanCoeff_ratio`, `chanCoeff_geoDom`, `channelTailCR`, `channelTailCR_leRat_sharp`, `channelTruncationTailBound`, `channelTail_discharged`: `[propext, Quot.sound]`.
- `chanTailBound_le_two`: **no axioms** (pure `decide`). No `native_decide`, no `sorry`, no `Classical.*`.

## Honest verdict

**The CHANNEL-truncation tail of item 12 is DISCHARGED** as a genuine constructive super-geometric bound: the real discarded-channel `CReal` sum is dominated by `chanTailBound ≤ 2` via the base-`ρ` geometric majorant (reusing the ϑ₃/`geoTailBase`/`geom_series_le_base` machinery), and `TruncationTailBound` is inhabited by a **non-degenerate** tail-defect sequence (`chanTailBound = 9/2^{19} > 0`, not the zero witness).

**Not closed (unchanged residuals), item 12 now gated only on:**
- the **finite-scale certification** — a uniform-in-`k` channel weight `≤ 2` at EVERY scale needs `N` to grow with the scale (the tail weight grows as `q = e^{−t_k/2}→1`; the pilot fixes ONE nome). This is the remaining `N ≈ 26` interval-arithmetic work (the `htrunc` hypothesis).
- the **deep-scaling scale-tail `singleStep` (E2)** — the RG recursion on `trueMargin`, entirely untouched. **Guard stays 5** (confirmed: `singleStep`/Tier0/UniformSpacingFloor/ClayTarget/… all uninhabited); `singleStep` NOT closed. This is the channel residual, ONE off the primary a→0 bet, not the bet itself. Clay YM mass gap remains OPEN.
