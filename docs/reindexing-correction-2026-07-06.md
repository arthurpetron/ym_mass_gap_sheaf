# Reindexing correction — the acN→Ucoup bridge is NOT bookkeeping (2026-07-06)

> Honest correction. The prior notes (`uturan.md`, `coreB.md`) framed the
> `acN↔Ucoup` reindexing as "bookkeeping, not mathematics." A rigorous pass
> (agent, no Lean changes) **refuted** that, and the coordinator independently
> confirmed it numerically (`computations/verify_trunc.py`). The full-range
> Turán `(‡)` — proved unconditional in `FusionUTuranEnvelope.uturan_unconditional`
> — does **not** close Core B. This does not retract `(‡)`; it corrects what `(‡)`
> is worth.

## The exact reindexing (verified, 0 mismatches s=0..24, w=1/2)

With `f(S) = c4(S) + 2(S+1)`, `Q = 1/w²`:

```
acN(s+1, S) = w^{f(S)} · Wtrunc(Q, S),   Wtrunc(Q,S) = Σ_{i=1}^{s+1} i(S+2−i)·Q^{i(S+2−i)}
```

The index shift is `i = p+1`; the per-term coefficient `dimQ(p)·dimQ(S−p) = i(S+2−i)`
matches `Ucoup`'s summand exactly. The exponent reserve is exactly `+2`:
`f(s)+f(s+2) = 2·f(s+1)+2` (pure Nat, from `c4_sum_symm`), so dividing `(†)` by the
common `w^{2f(s+1)}` leaves `w² = 1/Q` — the source of `256/225`. Hence
`(†) ⟺ (‡_trunc): 256·Wtrunc(s)·Wtrunc(s+2) ≤ 225·Q·Wtrunc(s+1)²`.

## Why the full-range `(‡)` does NOT imply `(‡_trunc)`

`acN(s+1,·)` uses the FIXED truncation range `p<s+1` for all three total degrees:

| factor | role | truncation | safe? |
|---|---|---|---|
| `acN(s+1, s)`   | denominator | none — `Wtrunc(s)=Ucoup(s+2)` exactly | — |
| `acN(s+1, s+2)` | denominator | drops i=s+2,s+3 (smaller denom) | SAFE |
| `acN(s+1, s+1)` | **numerator** | drops i=s+2, i.e. `−(s+2)Q^{s+2}` | **UNSAFE** |

The numerator `Wtrunc(s+1) = Ucoup(s+3) − (s+2)Q^{s+2} < Ucoup(s+3)` (confirmed exact).
`(‡_trunc)`'s RHS `225Q·Wtrunc(s+1)²` is therefore SMALLER than `225Q·Ucoup(s+3)²`;
`(‡)` bounds the larger quantity and does not transfer. Monotone bounding fails.

## What is true, and the corrected route

- `(‡_trunc)` **holds** uniform-in-`s` (verified): worst ratio 1.7465 (Q=4), 1.9315
  (Q=5), 2.3191 (Q=8) — all `≥ 1`.
- `SymMinorGershgorin` **is** the `256/225 = 1.1378` reserve `(†)` (via the proved
  Andréief identity `acN_defect_double_eq`). `(‡_trunc)`'s 1.7465 clears it → the
  route to close the fusion node is `(‡_trunc) → SymMinorGershgorin`.
- `FiniteSMargin` needs `40000/22801 = 1.7543` — `(‡_trunc)`'s 1.7465 does **not**
  clear it; that on-ramp is a distinct, tighter node, not the target.

## The corrected residual (genuine work, not bookkeeping)

1. **`(‡_trunc)`** — re-run the envelope on the TRUNCATED sums `Wtrunc`. Upper legs
   transfer for free (`Wtrunc ≤ Ucoup ≤ hi`); the lower leg needs central-term
   extraction at truncated length `s+2` (valid `s≥2`; `s=0,1` by direct monomial
   argument). Margin worst ≈ 1.7465, ample for the `256/225` reserve.
2. **The `Q' = 1/w²` reindexing layer** — negative-power clearing (a `Q'`
   positive-inverse + `qpow(1/w²)·qpow(w,2) = 1` layer). Delicate, not in-tree —
   the genuine blocker.

Then `(‡_trunc) → SymMinorGershgorin` closes Core ① (the fusion local-CLT node).
Still one node, not the 4D Yang–Mills mass gap; the Clay core
(`TrueMarginRecursionPhysical`) and the other atoms remain open.
