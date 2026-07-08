# Routes to the binding wall (`singleStep`) — adjudication under the ledger rule

*2026-07-08 (items 12–15). The burn-down says D=0: everything reduces *to* `singleStep`, nothing
below it. So the only moves that matter on the binding wall are (a) a construction that actually
closes it, or (b) a reformulation that is *strictly weaker* than `singleStep` (a new legal
decomposition). The ledger rule: any reformulation that merely *equi-inhabits* `singleStep` is a
C++ — record it, do not spend a campaign on it. This doc adjudicates the four proposed routes.*

`singleStep` (`SingleStepDefectBound`): the real 4D SU(N) block-spin defects satisfy `step` +
summable `(δ+ε)` + `(1−Σδ)·m₀ > Σε`. Equivalently (proved this session, `EpsilonSummability`):
`ε_k` quadratic ⟺ the budget closes.

---

## Item 12 — Koch–Wittwer computer-assisted rigorous RG  **[PRIMARY BET — a construction, not an adjudication]**

**Why this repo specifically can close `singleStep` through it.** Koch–Wittwer (Feigenbaum
conjecture) and the certified hierarchical-RG fixed-point analyses established a *completed* proof
class: rigorous interval arithmetic proving contraction of an RG map that pencil-and-paper
estimates could not reach. This project is uniquely positioned because the **Q' exact-rational
substrate with `decide`-checkable inequalities is already a certified-arithmetic engine**, and the
ε-dichotomy has already reduced the question to a concrete quantitative property (`ε_k` quadratic
decay) of a concrete numerically-selected map (transverse MK, `λ ≈ 0.5`).

**Proof shape (the one that composes with `HierarchicalMassGap`):**
1. Project the real block-spin map onto a finite-dimensional truncation (finitely many fusion
   channels / character coefficients).
2. Certify the contraction/defect bounds on the truncation by **exact interval arithmetic**,
   machine-checked natively in the Q' substrate (`decide` on rational interval endpoints — this is
   the part the substrate makes cheap and the part Koch–Wittwer had to build by hand).
3. Prove **ONE analytic lemma** bounding the truncation error (the tail of the discarded channels).

All the Balaban-type hardness concentrates into step 3 — but *one* lemma with certified numerics on
both sides is categorically easier than the full estimate chain, and it composes with (does not
compete with) the hierarchical program: hierarchical (exact, δ=0) + the truncated certified
contraction + the one truncation-error lemma = the 4D floor via the same proved Grönwall fold
(`euclidean_reduction`).

**Verdict: BUILD.** This is the load-bearing bet. **De-risk first via item 9** (Python MCMC scouting
of the defect scaling per block-spin scheme) — identify the truncation order at which the certified
contraction holds and the scheme for which the truncation error is controllable, *before* writing
Lean. Then: (i) Lean interval-arithmetic kernel over Q' (interval endpoints + `decide`d bounds);
(ii) the finite truncated map + its certified contraction; (iii) the truncation-error lemma (the
real analytic content — where a collaborator helps most, item 10).

---

## Item 13 — Resurgence / trans-series (Écalle; Dunne–Ünsal)  **[ADJUDICATE]**

**The reformulation.** The sweep machine-checked that the residual IS the renormalon ambiguity.
Resurgence is exactly the theory of how renormalon ambiguities cancel: the perturbative series and
the non-perturbative (instanton/condensate) sectors form a trans-series whose lateral Borel
ambiguities cancel between sectors, leaving an unambiguous real answer whose leading NP piece is
the Λ-scale — i.e. `ε_k`. Restate `singleStep` as: *"the lateral-Borel ambiguity of the constructed
activity cancels against the constructed condensate sector."* The repo's Borel/renormalon modules
(`FieldSpaceRenormalonZ1`, the sweep) are already most of the statement layer.

**Adjudication (honest prediction: LIKELY EQUI-INHABIT → C++, worth a one-session confirm).** The
cancellation statement, if proved, yields an *unambiguous positive real* Λ (the gap exists and is
Λ-scale). But the constructive/quantitative content that makes it a *proof* — that the NP piece is
positive and survives with a controlled magnitude — is the same summable-defect budget as
`singleStep`: the cancellation is a two-sided statement whose "real part is positive and bounded
below" clause is `(1−Σδ)·m₀ > Σε` in Borel-transform coordinates. So the cancellation and the
defect budget are two coordinate views of the same non-perturbative content ⟹ **equi-inhabit**.
- **BUT test before assuming:** there is a real chance the cancellation is provable from
  Borel-summability *structure* (Écalle's alien-derivative relations) without re-deriving the full
  defect magnitude — in which case it is **strictly weaker** and is a beautiful new legal
  decomposition no one has formalized. The Borel modules make this a one-session Lean adjudication:
  state `ResurgentCancellation` as a Prop, and prove `SingleStepDefectBound → ResurgentCancellation`
  (easy direction) + attempt `ResurgentCancellation → SingleStepDefectBound` (if it goes through
  with only Borel-structural input, strictly weaker; if it needs the magnitude, equi-inhabit).

**Verdict: ADJUDICATE (one session), do not campaign.** Record the outcome either way.

---

## Item 15 — Two-scale / RG-adapted LSI (Bauerschmidt–Bodineau; Otto–Reznikoff; Zegarlinski)  **[ADJUDICATE]**

**The reformulation.** A uniform-in-`a` log-Sobolev inequality for the lattice measure implies the
gap. The *single-scale* Bakry–Émery curvature version was refuted in the sweep (curvature is
orthogonal — it lands on the marginal part and cannot track the essential singularity), and that
refutation stands. But the *two-scale* methods (Zegarlinski iterated conditioning, Otto–Reznikoff
scale decomposition, Bauerschmidt–Bodineau polymer-LSI) prove LSIs precisely where curvature fails,
by running the inequality *along the RG flow*.

**Adjudication (honest prediction: LIKELY EQUI-INHABIT → C++, worth a one-session confirm).**
Running the LSI along the RG flow means each RG step degrades the LSI constant by a per-step defect;
a uniform LSI needs those per-step defects summable. That per-scale defect control **is** the
`singleStep` budget — the two-scale LSI's essential input is the same summable `(δ+ε)`. ⟹
**equi-inhabit**.
- **BUT test before assuming:** the polymer-LSI (Bauerschmidt–Bodineau) sometimes yields a uniform
  LSI from a per-scale condition that is *weaker* than the full defect budget (a spectral-gap-of-
  the-conditional-measure bound rather than the margin budget). If the two-scale decomposition's
  sufficient condition is genuinely weaker than `(1−Σδ)·m₀ > Σε`, it is a **strictly weaker** legal
  move — a beautiful result. Adjudicate as with item 13: `TwoScaleLSI` Prop, prove the easy
  direction, attempt the reverse under only the polymer-LSI per-scale input.

**Verdict: ADJUDICATE (one session), do not campaign.**

---

## Item 14 — Stochastic quantization (Chandra–Chevyrev–Hairer–Shen)  **[WATCH ONLY]**

Construct the YM measure as the invariant measure of the YM Langevin SPDE on gauge orbits; the gap
becomes a spectral-gap/ergodicity statement for the Markov semigroup. **Honest assessment: do not
build.** d=4 is *critical* for this SPDE and out of reach even classically; the machinery (regularity
structures) is a multi-year formalization on its own and is architecturally alien to the Q'/CReal
substrate; and it does not obviously evade the non-perturbative wall — the invariant-measure
construction hides Λ-generation in global well-posedness. **Route: watch-and-collaborate.** If the
d=3 program produces a gap theorem, its structure informs ours; the collaborator net (item 10)
should include this community (Chandra, Chevyrev, Hairer, Shen, Bauerschmidt).

---

## Summary sequencing

| Item | Route | Verdict | Action |
|---|---|---|---|
| 12 | Koch–Wittwer certified RG | **PRIMARY BET** | Build (de-risk via item 9 first) |
| 13 | Resurgence / trans-series | Likely equi-inhabit; possibly strictly weaker | One-session Lean adjudication |
| 15 | Two-scale LSI | Likely equi-inhabit; possibly strictly weaker | One-session Lean adjudication |
| 14 | Stochastic quantization | Out of reach; hides the wall | Watch + collaborator net |

The prediction for 13 and 15 is *equi-inhabit* (C++), but both carry a real chance of a strictly-
weaker decomposition, so both are worth the cheap adjudication — and neither is worth a campaign.
The campaign is item 12, and its first move is item 9 (Python scouting). The ledger rule holds:
adjudicate the reformulations, build the construction.
