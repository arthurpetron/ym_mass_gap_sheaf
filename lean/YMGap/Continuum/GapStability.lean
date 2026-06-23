/-
Route 1 — **topological protection of the spectral gap: STABILITY, not magnitude.**

# What this module is — and what it is emphatically NOT

A SECOND, independent route to controlling the gap along a deformation (e.g. the
RG / asymptotic-freedom flow) is *topological protection*: a gap, once it
EXISTS, is PROTECTED as long as a DISCRETE INTEGER invariant — the number of
spectral modes lying strictly below a fixed separator — stays constant.
Equivalently, the gap cannot close without that integer changing (an eigenvalue
CROSSING the separator).  This is the elementary finite-dimensional shadow of the
K-theory / index-theoretic "topological gap protection" idea.

**This route gives gap STABILITY ONLY.  It NEVER gives a gap magnitude / lower
bound.**  The honest reading is uncompromising on three points:

  1. It PRESUPPOSES a gap.  The integer invariant `belowCount` is only meaningful
     once a located gap already exists; the route cannot manufacture one.
  2. It is an AFTER-THE-FACT statement: "the gap cannot close without the integer
     jumping".  A constant integer ⇒ no crossing ⇒ the separator-below-`1`
     structure transports — but the route says nothing about HOW FAR below `1`.
  3. The integer CANNOT SEE THE MARGIN SHRINKING.  An excited eigenvalue may
     approach the separator `μ` arbitrarily closely from below — the margin
     `1 − specMax` shrinking toward `0` — while `belowCount` stays constant
     (nothing crosses).  So a constant integer is NECESSARY but NOT SUFFICIENT for
     a POSITIVE continuum gap; that quantitative content lives elsewhere.

This route therefore COMPLEMENTS, and does not replace, the quantitative
curvature / dimensionless-ratio route, which is the one that actually delivers a
positive *magnitude* with an explicit modulus (`UniformRatioVariation` and the
continuum-ratio limit).  The present module is strictly WEAKER than that route:
it transports the *shape* of a gap (something is below the separator) but is
blind to the *size* of the gap.  It does NOT close the continuum limit.

# The genuine content proved here

  * `belowCount S μ` — the discrete integer invariant: the number of modes
    `i < S.k` with `S.lam i < μ`.  Its basic properties (range, monotonicity in
    the prefix, the "all below" extreme).
  * `NoCross` — the per-step no-crossing condition along a discrete deformation
    `S : Nat → SpectralModel`: across one step no mode changes which side of the
    separator `μ` it lies on (`S k`.lam i `< μ` ↔ `S (k+1)`.lam i `< μ`), and the
    mode count is unchanged.
  * `belowCount_eq_of_noCross` — **the protection lemma:** no-crossing forces the
    integer invariant to be EQUAL across the step.  (So the integer can change
    ONLY by a crossing — the topological-protection statement in finite form.)
  * `LocatedSpectralGap`-transport: `allBelow`-at-`μ` (`μ < 1`) is exactly a
    located gap at separator `μ`; under `NoCross` it transports across one step
    (`transport_step`) and hence along the whole path (`transport_path`).

Everything is axiom-clean (`propext` / `Quot.sound` only via the reused `Q'`
order lemmas), pure `Q'` / `Nat`.  The quantitative-margin caveat above is made
explicit in `belowCount_blind_to_margin` (the integer is unchanged by deforming
an eigenvalue strictly toward — but not across — the separator).
-/

import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.GapStability

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap

/-! ## 1. The discrete integer invariant `belowCount`

`belowCount S μ` counts the modes `i < S.k` whose eigenvalue lies STRICTLY below
the separator `μ`.  The strict comparison `S.lam i < μ` is decidable on `Q'`
(`Q'`'s `DecidableRel (· < ·)`), so the count is computable.  This integer is the
located, discrete invariant of the topological-protection route — it is what stays
constant when the gap is protected and jumps when the gap closes. -/

/-- Count of `i < n` with `lam i < μ` (the strict-below count over the prefix). -/
def belowCountAux (lam : Nat → Q') (μ : Q') : Nat → Nat
  | 0 => 0
  | n + 1 => belowCountAux lam μ n + (if lam n < μ then 1 else 0)

/-- **The discrete integer invariant.**  The number of spectral modes `i < S.k`
with eigenvalue strictly below the separator `μ`.  This is the located,
computable, integer-valued datum the topological-protection route tracks. -/
def belowCount (S : SpectralModel) (μ : Q') : Nat := belowCountAux S.lam μ S.k

/-- The prefix count never exceeds the prefix length. -/
theorem belowCountAux_le (lam : Nat → Q') (μ : Q') :
    ∀ n, belowCountAux lam μ n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      show belowCountAux lam μ n + (if lam n < μ then 1 else 0) ≤ n + 1
      by_cases h : lam n < μ
      · rw [if_pos h]
        exact Nat.succ_le_succ (belowCountAux_le lam μ n)
      · rw [if_neg h, Nat.add_zero]
        exact Nat.le_succ_of_le (belowCountAux_le lam μ n)

/-- `belowCount` is bounded by the number of modes. -/
theorem belowCount_le (S : SpectralModel) (μ : Q') : belowCount S μ ≤ S.k :=
  belowCountAux_le S.lam μ S.k

/-- The prefix count is monotone in the prefix length. -/
theorem belowCountAux_mono (lam : Nat → Q') (μ : Q') {m n : Nat} (h : m ≤ n) :
    belowCountAux lam μ m ≤ belowCountAux lam μ n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
      rename_i n' _
      refine Nat.le_trans ih ?_
      show belowCountAux lam μ n' ≤ belowCountAux lam μ n' + (if lam n' < μ then 1 else 0)
      exact Nat.le_add_right _ _

/-! ### The "all below" extreme: `belowCount = k`

When EVERY mode is strictly below `μ`, the count saturates at the full mode count
`S.k`.  This is the integer-signature of a located gap at separator `μ`. -/

/-- A predicate: every mode of `S` is strictly below the separator `μ`. -/
def AllBelow (S : SpectralModel) (μ : Q') : Prop := ∀ i, i < S.k → S.lam i < μ

/-- If every prefix entry is `< μ`, the prefix count saturates at the length. -/
theorem belowCountAux_eq_of_all (lam : Nat → Q') (μ : Q') :
    ∀ n, (∀ i, i < n → lam i < μ) → belowCountAux lam μ n = n
  | 0, _ => rfl
  | n + 1, h => by
      show belowCountAux lam μ n + (if lam n < μ then 1 else 0) = n + 1
      rw [if_pos (h n (Nat.lt_succ_self n))]
      rw [belowCountAux_eq_of_all lam μ n (fun i hi => h i (Nat.lt_succ_of_lt hi))]

/-- **The "all below" integer signature.**  `AllBelow S μ ⇒ belowCount S μ = S.k`:
when every mode lies strictly below the separator, the invariant saturates. -/
theorem belowCount_eq_k_of_allBelow (S : SpectralModel) (μ : Q')
    (h : AllBelow S μ) : belowCount S μ = S.k :=
  belowCountAux_eq_of_all S.lam μ S.k h

/-! ## 2. `AllBelow` at `μ < 1` IS a located gap at separator `μ`

`AllBelow S μ` (every mode `< μ`) gives, for `μ < 1`, every mode `≤ μ < 1` — i.e.
exactly a `LocatedSpectralGap` at separator `μ`.  This is the bridge that lets the
integer-level protection statement speak about the genuine located gap. -/

/-! `SpectralGapBound S μ` quantifies `∀ i`, but `belowCount` / `AllBelow` only
constrain the supported prefix `i < S.k`.  The clean located-gap bridge therefore
needs the strict-below hypothesis on ALL indices.  We package that as
`AllBelowFull` and use it for the transport; the prefix-only `AllBelow` remains the
discrete integer invariant tracked by `belowCount`. -/

/-- Every mode index (not just `i < S.k`) is strictly below `μ`.  This is the
hypothesis the unrestricted `SpectralGapBound` needs. -/
def AllBelowFull (S : SpectralModel) (μ : Q') : Prop := ∀ i, S.lam i < μ

/-- `AllBelowFull` restricts to the prefix `AllBelow` (so it implies the same
saturated integer signature). -/
theorem allBelow_of_full {S : SpectralModel} {μ : Q'} (h : AllBelowFull S μ) :
    AllBelow S μ := fun i _ => h i

/-- **`AllBelowFull` at `μ < 1` IS a located gap at separator `μ`.**  Every mode
`≤ μ < 1`; the located content is derived.  This is the honest bridge: the
located gap is precisely the statement that all modes sit strictly below a
separator below the vacuum eigenvalue `1`. -/
def locatedGap_of_allBelowFull {S : SpectralModel} {μ : Q'} (hμ : μ < (1 : Q'))
    (h : AllBelowFull S μ) : LocatedSpectralGap S where
  sep := μ
  sep_lt_one := hμ
  bound := fun i => Q'.le_of_lt (h i)

/-! ## 3. The per-step no-crossing condition

A discrete deformation is a path `S : Nat → SpectralModel` (e.g. the AF-scheduled
sequence of finite spectral models).  The per-step NO-CROSSING condition at the
separator `μ` says: across one step, no mode changes which side of `μ` it is on,
and the mode count is unchanged.  This is the constructive content of "no level
crosses the separator" — the precise hypothesis under which the integer invariant
is protected. -/

/-- **The no-crossing condition for one step** `k → k+1` at separator `μ`.

  * `count_eq` — the mode count is unchanged across the step (the deformation does
    not create or destroy modes).
  * `side` — no mode crosses `μ`: for every supported index, being strictly below
    `μ` is preserved IN BOTH DIRECTIONS across the step.

This is a per-step *variation* condition (a finite, decidable, side-of-separator
statement), the discrete analogue of "the eigenvalues vary continuously without
any of them touching the separator". -/
structure NoCross (S : Nat → SpectralModel) (μ : Q') (k : Nat) : Prop where
  /-- The number of modes is unchanged across the step. -/
  count_eq : (S (k + 1)).k = (S k).k
  /-- No mode crosses the separator: strict-below membership is preserved both
  ways across the step (for every index). -/
  side : ∀ i, ((S k).lam i < μ ↔ (S (k + 1)).lam i < μ)

/-! ## 4. THE protection lemma — no crossing ⇒ the integer is invariant

If no mode crosses `μ` (and the count is unchanged), the prefix counts agree at
every length, hence the discrete invariant `belowCount` is EQUAL across the step.
This is the finite-dimensional topological-protection statement: **the integer can
change only by a crossing.** -/

/-- The prefix counts agree at every length when the per-index side is preserved. -/
theorem belowCountAux_eq_of_side (lam lam' : Nat → Q') (μ : Q')
    (hside : ∀ i, (lam i < μ ↔ lam' i < μ)) :
    ∀ n, belowCountAux lam μ n = belowCountAux lam' μ n
  | 0 => rfl
  | n + 1 => by
      show belowCountAux lam μ n + (if lam n < μ then 1 else 0)
         = belowCountAux lam' μ n + (if lam' n < μ then 1 else 0)
      rw [belowCountAux_eq_of_side lam lam' μ hside n]
      congr 1
      by_cases h : lam n < μ
      · rw [if_pos h, if_pos ((hside n).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hside n).mpr h'))]

/-- **The topological-protection lemma (finite form).**  Under `NoCross`, the
discrete integer invariant is EQUAL across the step:
`belowCount (S (k+1)) μ = belowCount (S k) μ`.  Equivalently, the integer can
change ONLY by a mode crossing the separator.  This is the *only* honest
contribution of the topological route: a discrete obstruction to the gap closing,
phrased as the constancy of a computable integer.

It says NOTHING about the gap's magnitude (see `belowCount_blind_to_margin`). -/
theorem belowCount_eq_of_noCross (S : Nat → SpectralModel) (μ : Q') (k : Nat)
    (h : NoCross S μ k) :
    belowCount (S (k + 1)) μ = belowCount (S k) μ := by
  show belowCountAux (S (k + 1)).lam μ (S (k + 1)).k
     = belowCountAux (S k).lam μ (S k).k
  rw [h.count_eq]
  exact (belowCountAux_eq_of_side (S (k + 1)).lam (S k).lam μ
    (fun i => (h.side i).symm) (S k).k)

/-! ## 5. THE stability theorem — the located gap transports under no-crossing

The honest payoff.  Under `NoCross`, `AllBelowFull` at `μ` transports across the
step (`side` preserves strict-below for every index), so the located gap at
separator `μ` (with `μ < 1` FIXED along the path) persists.  Iterating gives
persistence along the whole discrete deformation.

CRITICAL: this transports the *shape* of the gap (all modes below the fixed
separator `μ < 1`).  It does NOT transport, certify, or improve the gap's
*margin* `1 − specMax`; that quantity may shrink toward `0` along the path while
`NoCross` holds throughout (see `belowCount_blind_to_margin`).  Stability, not
magnitude. -/

/-- `AllBelowFull` transports across one no-crossing step. -/
theorem allBelowFull_step (S : Nat → SpectralModel) (μ : Q') (k : Nat)
    (h : NoCross S μ k) (hk : AllBelowFull (S k) μ) :
    AllBelowFull (S (k + 1)) μ :=
  fun i => (h.side i).mp (hk i)

/-- **The single-step stability theorem.**  A located gap at the FIXED separator
`μ < 1`, carried as `AllBelowFull (S k) μ`, transports across a no-crossing step
to a located gap at scale `k+1`.  The separator `μ` (and hence `sep < 1`) is the
SAME — the topological route protects the gap's existence at the fixed separator,
not its margin. -/
def transport_step (S : Nat → SpectralModel) (μ : Q') (hμ : μ < (1 : Q')) (k : Nat)
    (h : NoCross S μ k) (g : AllBelowFull (S k) μ) :
    LocatedSpectralGap (S (k + 1)) :=
  locatedGap_of_allBelowFull hμ (allBelowFull_step S μ k h g)

/-- `AllBelowFull` transports along the whole path, given no-crossing at every
step. -/
theorem allBelowFull_path (S : Nat → SpectralModel) (μ : Q')
    (hnc : ∀ k, NoCross S μ k) (h0 : AllBelowFull (S 0) μ) :
    ∀ k, AllBelowFull (S k) μ
  | 0 => h0
  | k + 1 => allBelowFull_step S μ k (hnc k) (allBelowFull_path S μ hnc h0 k)

/-- **THE stability theorem (path form).**  Given no-crossing at EVERY step
(`∀ k, NoCross S μ k`) at a FIXED separator `μ < 1`, a located gap at scale `0`
(as `AllBelowFull (S 0) μ`) transports to a located gap at EVERY scale `k`.

This is the topological-protection reduction in full: the continuum gap persists
along the (discrete, e.g. AF-scheduled) flow IF the per-step no-crossing condition
holds — equivalently, if the discrete mode-count invariant `belowCount` never
jumps.  See `belowCount_const_path` for the integer-signature companion.

HONEST SCOPE.  This is STABILITY ONLY.  It (i) PRESUPPOSES the gap at scale `0`;
(ii) protects only the FIXED separator `μ`, never a margin; (iii) is blind to the
margin shrinking (`belowCount_blind_to_margin`).  It is strictly WEAKER than the
quantitative `UniformRatioVariation` route, which alone yields a POSITIVE
continuum-gap *magnitude* with an explicit modulus.  It does NOT close the
continuum limit. -/
def transport_path (S : Nat → SpectralModel) (μ : Q') (hμ : μ < (1 : Q'))
    (hnc : ∀ k, NoCross S μ k) (g0 : AllBelowFull (S 0) μ) (k : Nat) :
    LocatedSpectralGap (S k) :=
  locatedGap_of_allBelowFull hμ (allBelowFull_path S μ hnc g0 k)

/-- **The integer-signature companion.**  Under no-crossing at every step, the
discrete invariant `belowCount (S k) μ` is CONSTANT in `k` (equal to its scale-`0`
value).  This is the observable signature of the protection: a constant integer
along the flow.  NB: this constancy is NECESSARY for the gap to persist but, on
its own, NOT SUFFICIENT — see the caveat below. -/
theorem belowCount_const_path (S : Nat → SpectralModel) (μ : Q')
    (hnc : ∀ k, NoCross S μ k) :
    ∀ k, belowCount (S k) μ = belowCount (S 0) μ
  | 0 => rfl
  | k + 1 => by
      rw [belowCount_eq_of_noCross S μ k (hnc k)]
      exact belowCount_const_path S μ hnc k

/-! ## 6. THE honest caveat — the integer is BLIND to the margin shrinking

A constant integer invariant is NECESSARY but NOT SUFFICIENT for a positive gap
magnitude.  The integer `belowCount` only records WHICH SIDE of the separator each
mode is on; it cannot see HOW FAR an eigenvalue sits below the separator.  An
eigenvalue may be deformed strictly TOWARD the separator `μ` (margin shrinking
toward `0`) without ever crossing it — and `belowCount`, `AllBelow`, `NoCross`,
and the entire transport above are UNCHANGED.

We make this explicit: two spectral models that differ only by moving one
eigenvalue closer to `μ` (but still strictly below it) have the SAME `belowCount`.
Hence the integer route, by itself, can never certify a POSITIVE *limiting* margin
— that quantitative content must come from the curvature / `UniformRatioVariation`
route.  This is the precise sense in which the topological route gives stability,
not magnitude. -/

/-- **The margin-blindness caveat (made precise).**  If two spectral models share
the same mode count and every mode is on the same side of the separator `μ`, their
`belowCount` is identical — REGARDLESS of how close to `μ` (above or below) the
eigenvalues sit.  In particular, deforming an eigenvalue strictly toward `μ` from
below (shrinking the margin `μ − lam i` toward `0`) leaves `belowCount` constant.

The integer invariant therefore CANNOT detect the gap margin shrinking: a constant
`belowCount` is consistent with the margin `→ 0`.  This is why the topological
route gives STABILITY ONLY and the POSITIVE magnitude must come from the
quantitative route. -/
theorem belowCount_blind_to_margin (S S' : SpectralModel) (μ : Q')
    (hk : S'.k = S.k) (hside : ∀ i, (S.lam i < μ ↔ S'.lam i < μ)) :
    belowCount S' μ = belowCount S μ := by
  show belowCountAux S'.lam μ S'.k = belowCountAux S.lam μ S.k
  rw [hk]
  exact belowCountAux_eq_of_side S'.lam S.lam μ (fun i => (hside i).symm) S.k

end YMGap.Continuum.GapStability

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GapStability.belowCount_le
#print axioms YMGap.Continuum.GapStability.belowCountAux_mono
#print axioms YMGap.Continuum.GapStability.belowCount_eq_k_of_allBelow
#print axioms YMGap.Continuum.GapStability.locatedGap_of_allBelowFull
#print axioms YMGap.Continuum.GapStability.belowCountAux_eq_of_side
#print axioms YMGap.Continuum.GapStability.belowCount_eq_of_noCross
#print axioms YMGap.Continuum.GapStability.allBelowFull_step
#print axioms YMGap.Continuum.GapStability.transport_step
#print axioms YMGap.Continuum.GapStability.allBelowFull_path
#print axioms YMGap.Continuum.GapStability.transport_path
#print axioms YMGap.Continuum.GapStability.belowCount_const_path
#print axioms YMGap.Continuum.GapStability.belowCount_blind_to_margin
