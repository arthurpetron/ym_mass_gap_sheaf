/-
  OSCSLedger.lean — the OS/CS structure of the slab network
  values, kernel-checked at the coefficient-ledger level.

  GENERATED FILE: emitted by scripts/gen_oscs_lean.py from the
  merged banked ledgers computations/su2_cs_diagonals.json* and
  computations/su2_m2_finality.json*; upstream computation the
  exact contraction engines rust/haar_contract (work_plan
  §16j, gated against every banked exact value) via
  computations/su2_rust_eval.py and the Python reference
  engine computations/su2_cut_eval.py — all arithmetic exact.
  Do not edit literals by hand — regenerate.

  What this file banks (the config-level shadow of DP.R1's OS
  Gram positivity; work_plan §§16h–16j):

  * OS POSITIVITY.  Every landed reflection-diagonal value is
    nonnegative (`diag_nonneg`).  Diagonals are OS norms under
    the Osterwalder–Seiler link reflection; nonnegativity is a
    PREDICTION of that structure and the computed values comply.

  * THE OS/CS INEQUALITY.  N² ≤ D_a · D_b for every landed
    off-diagonal whose diagonal partners are both landed
    (`cs_bound_all`).  The partner keys are NOT transcribed:
    `d4Images` rederives the D4 action in Lean and
    `cs_partners_located` kernel-checks that each cited partner
    value sits in the diagonal ledger at a D4 image of the key
    the lemma demands.

  * THE CRUDE BOUND.  |N| ≤ d_n d_m Π_f d_f, the face product
    rederived in Lean from the labelling (`diag_le_crude`,
    `m2_le_crude`) — the bound driving §16g's domination
    transfer.

  * THE SIGN CENSUS.  Off-diagonal values DO go negative (6j
    recoupling interference); the count is kernel-checked, so
    the CS inequality is exercised on signed data.

  Provenance caveat (spike-wide): the ledger literals are
  transported from the exact contraction engines; re-deriving
  them inside Lean from the main tree's finite product Haar
  evaluation is the wiring TODO shared with DualKappa.lean,
  FrozenHub.lean, DP6Ledger.lean and DP3M2Ledger.lean.

  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace OSCSLedger

/-- An exact rational as (numerator, denominator), denominator a
positive `Nat`; comparisons cross-multiply into `Int`. -/
abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qNonneg (a : Q) : Bool := decide (0 ≤ a.1) && decide (0 < a.2)

def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)

/-- a ≤ b by cross-multiplication (valid: denominators positive). -/
def qLe (a b : Q) : Bool := decide (a.1 * qDen b ≤ b.1 * qDen a)

def qMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)

def qSq (a : Q) : Q := qMul a a

/-- |a| ≤ k for a natural bound k, by cross-multiplication. -/
def qAbsLeNat (a : Q) (k : Nat) : Bool :=
  decide (a.1.natAbs ≤ k * a.2)

/-- 4x Casimir of the spin label n (n = 2j): C(n) = n(n+2). -/
def casimir4 (n : Nat) : Nat := n * (n + 2)

/-- Dimension of the spin label n: d_n = n + 1. -/
def dimOf (n : Nat) : Nat := n + 1

def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0

def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1

def prodDSq (l : List Nat) : Nat :=
  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1

/-- A half-configuration key: the loop spin and the D4-orbit data
(perimeter classes q, interior walls w, tile spins t). -/
structure Key where
  loop : Nat
  q : List Nat
  w : List Nat
  t : List Nat
  deriving BEq, DecidableEq

/-- A full slab configuration (as in DP3M2Ledger). -/
structure Config where
  q : List Nat
  w : List Nat
  top : List Nat
  bot : List Nat
  deriving BEq, DecidableEq

/-- Cyclic rotation by r. -/
def rot (r : Nat) (l : List Nat) : List Nat := l.drop r ++ l.take r

/-- The reflection on corner-anchored lists: fix the head, reverse
the rest (q and t); walls reverse outright. -/
def reflAnchored : List Nat → List Nat
  | [] => []
  | x :: rest => x :: rest.reverse

/-- The 8 images of a key under the D4 action: rotations shift
corners and sides together; the reflection fixes the anchor of q
and t and reverses w.  This is the SAME action gated against
computed network values in computations/su2_cs_tail.cs_gate —
value-invariance is an input fact; the ACTION is rederived here. -/
def d4Images (k : Key) : List Key :=
  (List.range 4).flatMap (fun r =>
    let qq := rot r k.q
    let ww := rot r k.w
    let tt := rot r k.t
    [ ⟨k.loop, qq, ww, tt⟩,
      ⟨k.loop, reflAnchored qq, ww.reverse, reflAnchored tt⟩ ])

/-- The crude value bound for a half-diagonal:
d_loop² Π_q d² Π_w d Π_t d² (top = bot = t on a diagonal). -/
def diagCrude (k : Key) : Nat :=
  dimOf k.loop * dimOf k.loop * prodDSq k.q * prodD k.w
    * prodDSq k.t

/-- The crude value bound for an off-diagonal configuration:
d_n d_m Π_q d² Π_w d Π_top d Π_bot d. -/
def m2Crude (n m : Nat) (c : Config) : Nat :=
  dimOf n * dimOf m * prodDSq c.q * prodD c.w * prodD c.top
    * prodD c.bot

/-- The landed reflection-diagonal ledger: (key, exact OS norm
N(loop, loop; q, w, t, t)).  97 landed values;
budget-missed keys are ABSENT, never zero-filled. -/
def diagLedger : List (Key × Q) :=
  [ ⟨⟨0, [0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2]⟩, (1, 6561)⟩,
    ⟨⟨0, [0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1]⟩, (1, 4096)⟩,
    ⟨⟨0, [0, 1, 1, 2], [1, 0, 1, 2], [0, 1, 1, 2]⟩, (1, 20736)⟩,
    ⟨⟨0, [0, 1, 1, 2], [1, 2, 1, 2], [0, 1, 1, 2]⟩, (1, 20736)⟩,
    ⟨⟨0, [0, 1, 2, 1], [1, 1, 1, 1], [0, 1, 2, 1]⟩, (1, 20736)⟩,
    ⟨⟨0, [0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2]⟩, (1, 104976)⟩,
    ⟨⟨0, [0, 2, 1, 2], [2, 1, 1, 2], [0, 2, 1, 2]⟩, (1, 104976)⟩,
    ⟨⟨0, [1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1]⟩, (1, 73728)⟩,
    ⟨⟨0, [1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1]⟩, (7, 442368)⟩,
    ⟨⟨0, [1, 1, 1, 2], [0, 0, 1, 1], [1, 1, 1, 2]⟩, (1, 110592)⟩,
    ⟨⟨0, [1, 1, 1, 2], [0, 2, 1, 1], [1, 1, 1, 2]⟩, (1, 995328)⟩,
    ⟨⟨0, [1, 1, 1, 2], [2, 2, 1, 1], [1, 1, 1, 2]⟩, (11, 2985984)⟩,
    ⟨⟨0, [1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2]⟩, (1, 839808)⟩,
    ⟨⟨0, [1, 1, 2, 2], [2, 1, 0, 1], [1, 1, 2, 2]⟩, (1, 5038848)⟩,
    ⟨⟨0, [1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2]⟩, (1, 2519424)⟩,
    ⟨⟨0, [1, 2, 2, 2], [1, 0, 2, 1], [1, 2, 2, 2]⟩, (1, 4251528)⟩,
    ⟨⟨1, [0, 0, 0, 2], [0, 0, 2, 2], [1, 1, 1, 1]⟩, (1, 5184)⟩,
    ⟨⟨1, [0, 0, 0, 2], [0, 0, 2, 2], [1, 1, 1, 3]⟩, (1, 5184)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 1, 2], [1, 1, 0, 1]⟩, (1, 9216)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 1, 2], [1, 1, 2, 1]⟩, (1, 746496)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 1, 2], [1, 1, 2, 3]⟩, (1, 46656)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 3, 2], [1, 1, 0, 3]⟩, (1, 36864)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 3, 2], [1, 1, 2, 1]⟩, (1, 46656)⟩,
    ⟨⟨1, [0, 0, 1, 2], [0, 1, 3, 2], [1, 1, 2, 3]⟩, (25, 2985984)⟩,
    ⟨⟨1, [0, 0, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1]⟩, (1, 104976)⟩,
    ⟨⟨1, [0, 0, 2, 2], [0, 2, 2, 2], [1, 1, 1, 3]⟩, (1, 1679616)⟩,
    ⟨⟨1, [0, 1, 0, 2], [1, 1, 2, 2], [1, 0, 1, 1]⟩, (1, 27648)⟩,
    ⟨⟨1, [0, 1, 0, 2], [1, 1, 2, 2], [1, 0, 1, 3]⟩, (1, 55296)⟩,
    ⟨⟨1, [0, 1, 0, 2], [1, 1, 2, 2], [1, 2, 1, 1]⟩, (11, 746496)⟩,
    ⟨⟨1, [0, 1, 0, 2], [1, 1, 2, 2], [1, 2, 1, 3]⟩, (19, 1492992)⟩,
    ⟨⟨1, [0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2]⟩, (1, 124416)⟩,
    ⟨⟨1, [0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 0, 1, 2], [1, 0, 0, 1]⟩, (1, 9216)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 0, 1, 2], [1, 2, 2, 1]⟩, (1, 6718464)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 0, 1, 2], [1, 2, 2, 3]⟩, (1, 419904)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 0, 3, 2], [1, 0, 0, 3]⟩, (1, 36864)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 0, 3, 2], [1, 2, 2, 1]⟩, (1, 419904)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1]⟩, (1, 746496)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 3]⟩, (1, 373248)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 0, 1]⟩, (1, 82944)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1]⟩, (1, 5038848)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 3]⟩, (11, 10077696)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 3, 2], [1, 0, 2, 1]⟩, (1, 186624)⟩,
    ⟨⟨1, [0, 1, 1, 2], [1, 2, 3, 2], [1, 2, 2, 1]⟩, (7, 5038848)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 1, 1], [1, 0, 1, 0]⟩, (1, 12288)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 1, 1], [1, 0, 1, 2]⟩, (1, 331776)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 1, 1], [1, 2, 1, 2]⟩, (7, 26873856)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 1, 1], [1, 2, 3, 2]⟩, (1, 419904)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 3, 1], [1, 0, 1, 2]⟩, (1, 82944)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 3, 1], [1, 2, 1, 2]⟩, (1, 6718464)⟩,
    ⟨⟨1, [0, 1, 2, 1], [1, 1, 3, 1], [1, 2, 3, 0]⟩, (1, 331776)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1]⟩, (1, 124416)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 3]⟩, (1, 995328)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1]⟩, (11, 30233088)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 3]⟩, (19, 241864704)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 3, 1]⟩, (1, 15116544)⟩,
    ⟨⟨1, [0, 1, 2, 2], [1, 3, 0, 2], [1, 2, 1, 1]⟩, (1, 419904)⟩,
    ⟨⟨1, [0, 1, 3, 1], [1, 2, 2, 1], [1, 0, 2, 0]⟩, (1, 55296)⟩,
    ⟨⟨1, [0, 1, 3, 1], [1, 2, 2, 1], [1, 0, 2, 2]⟩, (1, 995328)⟩,
    ⟨⟨1, [0, 2, 0, 2], [2, 2, 2, 2], [1, 1, 1, 1]⟩, (7, 1259712)⟩,
    ⟨⟨1, [0, 2, 1, 2], [2, 1, 1, 2], [1, 1, 0, 1]⟩, (1, 82944)⟩,
    ⟨⟨1, [0, 2, 1, 2], [2, 1, 1, 2], [1, 1, 2, 1]⟩, (11, 181398528)⟩,
    ⟨⟨1, [0, 2, 1, 2], [2, 1, 1, 2], [1, 1, 2, 3]⟩, (1, 22674816)⟩,
    ⟨⟨1, [1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2]⟩, (1, 93312)⟩,
    ⟨⟨1, [1, 1, 1, 1], [0, 2, 2, 2], [2, 2, 2, 2]⟩, (1, 7558272)⟩,
    ⟨⟨1, [1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2]⟩, (1, 1259712)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 0, 1, 1], [0, 0, 0, 1]⟩, (1, 3072)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 0, 1, 1], [2, 2, 2, 3]⟩, (1, 1259712)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 0, 1, 3], [2, 2, 2, 1]⟩, (0, 1)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 1, 1], [0, 0, 2, 1]⟩, (1, 248832)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 1, 1], [2, 2, 2, 1]⟩, (1, 45349632)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 1, 1], [2, 2, 2, 3]⟩, (1, 11337408)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 1, 3], [2, 2, 0, 1]⟩, (1, 559872)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 3, 1], [0, 0, 2, 1]⟩, (1, 62208)⟩,
    ⟨⟨1, [1, 1, 1, 2], [0, 2, 3, 1], [2, 2, 2, 1]⟩, (1, 45349632)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [0, 2, 0, 1]⟩, (1, 82944)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [0, 2, 2, 1]⟩, (1, 3359232)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [2, 0, 2, 3]⟩, (1, 2519424)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [2, 2, 2, 1]⟩, (1, 90699264)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [2, 2, 2, 3]⟩, (1, 7558272)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 3], [2, 0, 2, 1]⟩, (1, 5038848)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 3], [2, 2, 0, 1]⟩, (1, 839808)⟩,
    ⟨⟨1, [1, 1, 1, 3], [0, 0, 2, 2], [0, 0, 0, 2]⟩, (1, 13824)⟩,
    ⟨⟨1, [1, 1, 2, 2], [0, 1, 0, 3], [2, 2, 1, 1]⟩, (0, 1)⟩,
    ⟨⟨1, [1, 1, 2, 2], [0, 1, 2, 1], [0, 0, 1, 1]⟩, (1, 41472)⟩,
    ⟨⟨1, [1, 1, 2, 2], [0, 1, 2, 1], [2, 2, 1, 1]⟩, (1, 272097792)⟩,
    ⟨⟨1, [1, 1, 2, 2], [0, 1, 2, 1], [2, 2, 1, 3]⟩, (1, 68024448)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 0, 1], [2, 2, 1, 1]⟩, (1, 45349632)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 0, 3], [2, 0, 1, 1]⟩, (1, 559872)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1]⟩, (1, 3359232)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 2, 1], [2, 2, 1, 1]⟩, (1, 204073344)⟩,
    ⟨⟨1, [1, 2, 1, 2], [1, 1, 1, 1], [0, 1, 0, 1]⟩, (1, 36864)⟩,
    ⟨⟨1, [1, 2, 1, 2], [1, 1, 1, 1], [0, 1, 2, 1]⟩, (1, 8957952)⟩,
    ⟨⟨1, [1, 2, 1, 2], [1, 1, 1, 1], [2, 1, 2, 3]⟩, (1, 102036672)⟩,
    ⟨⟨1, [1, 2, 1, 2], [1, 1, 1, 3], [2, 1, 0, 1]⟩, (1, 2239488)⟩,
    ⟨⟨1, [1, 2, 1, 2], [1, 1, 1, 3], [2, 1, 2, 1]⟩, (1, 1632586752)⟩,
    ⟨⟨1, [1, 2, 2, 2], [1, 0, 2, 1], [2, 1, 1, 1]⟩, (1, 272097792)⟩ ]

/-- Non-vacuity pin. -/
theorem diag_count : diagLedger.length = 97 := by decide

/-- **OS positivity at ledger level**: every landed diagonal is
nonnegative — as the Osterwalder–Seiler reflection structure
demands of a norm.  (7 of the off-diagonal values below are
negative, so this is not a triviality of the evaluator.) -/
theorem diag_nonneg :
    diagLedger.all (fun r => qNonneg r.2) = true := by decide

/-- Every diagonal obeys the crude bound, with the face product
rederived from the labelling — the |N| ≤ d_n d_m Π d_f input to
§16g's domination transfer, checked on every landed value. -/
theorem diag_le_crude :
    diagLedger.all (fun r => qAbsLeNat r.2 (diagCrude r.1))
      = true := by decide

/-- The landed direct M = 2 off-diagonal ledger:
(n, m, config, exact N).  40 landed values. -/
def m2Ledger : List (Nat × Nat × Config × Q) :=
  [ ⟨0, 0, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [0, 1, 1, 1]⟩, (1, 4096)⟩,
    ⟨0, 0, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [0, 1, 1, 2], [0, 1, 1, 2]⟩, (1, 20736)⟩,
    ⟨0, 0, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [0, 1, 2, 2]⟩, (1, 104976)⟩,
    ⟨0, 0, ⟨[0, 2, 1, 2], [2, 1, 1, 2], [0, 2, 1, 2], [0, 2, 1, 2]⟩, (1, 104976)⟩,
    ⟨0, 0, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 73728)⟩,
    ⟨0, 0, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (7, 442368)⟩,
    ⟨0, 0, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [1, 1, 2, 2]⟩, (1, 839808)⟩,
    ⟨0, 1, ⟨[0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2], [1, 1, 1, 1]⟩, (1, 26244)⟩,
    ⟨0, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 0, 2, 2]⟩, (1, 27648)⟩,
    ⟨0, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 2, 2, 2]⟩, (1, 41472)⟩,
    ⟨0, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 0, 1, 1]⟩, (1, 139968)⟩,
    ⟨0, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 2, 1, 1]⟩, (1, 1259712)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [0, 0, 2, 2]⟩, (1, 82944)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [2, 2, 2, 2]⟩, (1, 746496)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [0, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [2, 0, 2, 2]⟩, (1, 373248)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 2], [2, 2, 1, 1], [1, 1, 1, 2], [2, 2, 2, 1]⟩, (1, 10077696)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [0, 0, 1, 1]⟩, (1, 186624)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (-1, 15116544)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [0, 2, 1, 1]⟩, (1, 5038848)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 0, 1, 1]⟩, (1, 5038848)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (1, 22674816)⟩,
    ⟨1, 1, ⟨[0, 0, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 104976)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 0, 2, 2]⟩, (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 0, 2, 2]⟩, (1, 373248)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 0, 2, 1]⟩, (1, 746496)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 2, 2, 1]⟩, (-1, 3359232)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 0, 2, 1]⟩, (-1, 3359232)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 2, 2, 1]⟩, (1, 5038848)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 0, 1, 1]⟩, (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 2, 1, 1]⟩, (-1, 3359232)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 0, 1, 1]⟩, (-1, 3359232)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 2, 1, 1]⟩, (11, 30233088)⟩,
    ⟨1, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]⟩, (1, 93312)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [0, 2, 1, 1]⟩, (1, 3359232)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [2, 0, 1, 1]⟩, (-1, 10077696)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [0, 2, 1, 1]⟩, (-1, 10077696)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [2, 0, 1, 1]⟩, (1, 3359232)⟩ ]

/-- Non-vacuity pin. -/
theorem m2_count : m2Ledger.length = 40 := by decide

/-- **The sign census**: exactly the kernel-checked number of
off-diagonal values are strictly negative — 6j recoupling
interference, the phenomenon behind DP3M2Ledger's fence.  The
CS inequality below is exercised on signed data. -/
theorem m2_negative_count :
    (m2Ledger.filter (fun r => qNeg r.2.2.2)).length = 7
      := by decide

/-- Every off-diagonal obeys the crude bound (rederived weight). -/
theorem m2_le_crude :
    m2Ledger.all (fun r =>
      qAbsLeNat r.2.2.2 (m2Crude r.1 r.2.1 r.2.2.1)) = true := by
  decide

/-- The CS-checkable rows: every landed off-diagonal whose two
diagonal partners are both landed, with the cited partner values.
Entries: (n, m, config, N, D_a, D_b).  The partner VALUES are
literals; their membership in `diagLedger` at the D4 image of
the key the lemma demands is kernel-checked below, so the
pairing is rederived, not trusted. -/
def csRows : List (Nat × Nat × Config × Q × Q × Q) :=
  [ ⟨0, 0, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [0, 1, 1, 1]⟩, (1, 4096), (1, 4096), (1, 4096)⟩,
    ⟨0, 0, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [0, 1, 1, 2], [0, 1, 1, 2]⟩, (1, 20736), (1, 20736), (1, 20736)⟩,
    ⟨0, 0, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [0, 1, 2, 2]⟩, (1, 104976), (1, 104976), (1, 104976)⟩,
    ⟨0, 0, ⟨[0, 2, 1, 2], [2, 1, 1, 2], [0, 2, 1, 2], [0, 2, 1, 2]⟩, (1, 104976), (1, 104976), (1, 104976)⟩,
    ⟨0, 0, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 73728), (1, 73728), (1, 73728)⟩,
    ⟨0, 0, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (7, 442368), (7, 442368), (7, 442368)⟩,
    ⟨0, 0, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [1, 1, 2, 2]⟩, (1, 839808), (1, 839808), (1, 839808)⟩,
    ⟨0, 1, ⟨[0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2], [1, 1, 1, 1]⟩, (1, 26244), (1, 6561), (1, 104976)⟩,
    ⟨0, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 0, 2, 2]⟩, (1, 27648), (1, 4096), (1, 124416)⟩,
    ⟨0, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 2, 2, 2]⟩, (1, 41472), (1, 4096), (1, 373248)⟩,
    ⟨0, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 0, 1, 1]⟩, (1, 139968), (1, 104976), (1, 124416)⟩,
    ⟨0, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 2, 1, 1]⟩, (1, 1259712), (1, 104976), (11, 30233088)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [0, 0, 2, 2]⟩, (1, 82944), (1, 73728), (1, 93312)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [2, 2, 2, 2]⟩, (1, 746496), (1, 73728), (1, 7558272)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [0, 2, 2, 2]⟩, (1, 373248), (7, 442368), (1, 1259712)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [2, 0, 2, 2]⟩, (1, 373248), (7, 442368), (1, 1259712)⟩,
    ⟨0, 1, ⟨[1, 1, 1, 2], [2, 2, 1, 1], [1, 1, 1, 2], [2, 2, 2, 1]⟩, (1, 10077696), (11, 2985984), (1, 90699264)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [0, 0, 1, 1]⟩, (1, 186624), (1, 839808), (1, 41472)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (-1, 15116544), (1, 839808), (1, 272097792)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [0, 2, 1, 1]⟩, (1, 5038848), (1, 2519424), (1, 3359232)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 0, 1, 1]⟩, (1, 5038848), (1, 2519424), (1, 3359232)⟩,
    ⟨0, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (1, 22674816), (1, 2519424), (1, 204073344)⟩,
    ⟨1, 1, ⟨[0, 0, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 104976), (1, 104976), (1, 104976)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 0, 2, 2]⟩, (1, 124416), (1, 124416), (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 2, 2, 2]⟩, (1, 373248), (1, 124416), (1, 373248)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 0, 2, 2]⟩, (1, 373248), (1, 373248), (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 2, 2, 2]⟩, (1, 373248), (1, 373248), (1, 373248)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 0, 2, 1]⟩, (1, 746496), (1, 746496), (1, 746496)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 2, 2, 1]⟩, (-1, 3359232), (1, 746496), (1, 5038848)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 0, 2, 1]⟩, (-1, 3359232), (1, 5038848), (1, 746496)⟩,
    ⟨1, 1, ⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 2, 2, 1]⟩, (1, 5038848), (1, 5038848), (1, 5038848)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 0, 1, 1]⟩, (1, 124416), (1, 124416), (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 2, 1, 1]⟩, (-1, 3359232), (1, 124416), (11, 30233088)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 0, 1, 1]⟩, (-1, 3359232), (11, 30233088), (1, 124416)⟩,
    ⟨1, 1, ⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 2, 1, 1]⟩, (11, 30233088), (11, 30233088), (11, 30233088)⟩,
    ⟨1, 1, ⟨[1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]⟩, (1, 93312), (1, 93312), (1, 93312)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [0, 2, 1, 1]⟩, (1, 3359232), (1, 3359232), (1, 3359232)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [2, 0, 1, 1]⟩, (-1, 10077696), (1, 3359232), (1, 3359232)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [0, 2, 1, 1]⟩, (-1, 10077696), (1, 3359232), (1, 3359232)⟩,
    ⟨1, 1, ⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [2, 0, 1, 1]⟩, (1, 3359232), (1, 3359232), (1, 3359232)⟩ ]

/-- Non-vacuity pin. -/
theorem cs_count : csRows.length = 40 := by decide

/-- The half-keys the OS/CS lemma pairs an off-diagonal with:
(n; q, w, top) and (m; q, w, bot). -/
def keyA (r : Nat × Nat × Config × Q × Q × Q) : Key :=
  ⟨r.1, r.2.2.1.q, r.2.2.1.w, r.2.2.1.top⟩

def keyB (r : Nat × Nat × Config × Q × Q × Q) : Key :=
  ⟨r.2.1, r.2.2.1.q, r.2.2.1.w, r.2.2.1.bot⟩

/-- The cited partner value appears in the diagonal ledger at a
D4 image of the demanded key. -/
def locates (k : Key) (v : Q) : Bool :=
  (d4Images k).any (fun img =>
    diagLedger.any (fun row => row.1 == img && row.2 == v))

/-- **The pairing is rederived in Lean**: for every CS row, both
cited diagonal values are located in `diagLedger` through the
D4 action on the keys (n; q, w, top) and (m; q, w, bot). -/
theorem cs_partners_located :
    csRows.all (fun r =>
      locates (keyA r) r.2.2.2.2.1 && locates (keyB r) r.2.2.2.2.2)
      = true := by decide

/-- **The OS/CS inequality, kernel-checked**: N² ≤ D_a · D_b on
every checkable row — the config-level shadow of DP.R1's OS Gram
positivity (work_plan §16h), the inequality that turns landed
diagonals into certified off-diagonal tail collapses. -/
theorem cs_bound_all :
    csRows.all (fun r =>
      qLe (qSq r.2.2.2.1) (qMul r.2.2.2.2.1 r.2.2.2.2.2))
      = true := by decide

/-- The signed case is covered: at least one CS-checked row
carries a strictly negative N (6j interference), so the
inequality is not exercised on positives alone. -/
theorem cs_includes_signed :
    (csRows.filter (fun r => qNeg r.2.2.2.1)).length = 7
      := by decide

end OSCSLedger
