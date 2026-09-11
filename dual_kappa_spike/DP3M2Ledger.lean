/-
  DP3M2Ledger.lean — the DP.3 M = 2 verdict, kernel-checked at the
  coefficient-ledger level.

  GENERATED FILE: emitted by scripts/gen_dp3m2_lean.py from
  computations/dp3_m2_entries.json; upstream computation
  computations/dp3_fixed_tile.py + dp3_m2_driver.py (exact Haar values
  of the pure-character slab networks at activity truncation M = 2, all
  arithmetic Fraction-exact).  Do not edit literals by hand —
  regenerate.

  The verdict this file banks (DP.3-(i) REFUTED at BOTH granularities):

  * ENTRY LEVEL.  The blocked kernel entry T[1,1] carries a NEGATIVE
    coefficient at s^76.  Every configuration at that exponent is
    listed (`e76Configs`), each with its exact network value N and its
    D4 multiplicity; both the exponent and the assembly weight are
    rederived in Lean from the labelling (`configExp`, `configWeight`),
    so the ledger is internally consistent and not merely transcribed.
    `t11_coeff_76_negative` is the Lakatos fence: the cone C_exp of
    coefficientwise-nonnegative dual data is NOT preserved by one
    blocking step at M = 2.

  * AGGREGATED LEVEL.  The DP.6 repair route — "positivity lost at fine
    granularity is restored by aggregation" — is CLOSED here.  The
    blocked image (Bv)_1 at s^79 receives contributions only from
    T[1,1] (via d_1 s^{C(1)}); the sibling channels T[1,0] and T[1,2]
    are exactly zero at the feeding exponents 79 and 71
    (`blocked_79_no_cancellation`), so the sum is -64/3
    (`blocked_79_negative`).  There is nothing to cancel against.

  * WHAT SURVIVES is positivity as a FUNCTION, not coefficientwise.
    Following the DP6Ledger precedent, "positive polynomial on (0,1)"
    is NOT formalized here as a statement about all real s.  What IS
    kernel-checked is evaluation at exact rational couplings
    (`t11_final_positive_at`), which is a partial bridge only: it
    witnesses that the negative coefficient does not make the entry
    negative at those s, and nothing more.

  * eps_slab(1).  The certified truncation exponents E*(n,m,1), each
    far above the naive single-face bound C(2) = 8
    (`eps_star_beats_naive`).  E* itself is produced by exhaustive
    enumeration in computations/eps_slab.py; only the table and its
    comparisons are banked here.

  Rationals are (numerator : Int, denominator : Nat) pairs with
  positive denominators; all comparisons cross-multiply into Int so
  kernel `decide` stays on closed integer arithmetic.

  Provenance caveat (spike-wide): the ledger literals are transported
  from the Python quaternion-Haar machinery; re-deriving them inside
  Lean from the main tree's finite product Haar evaluation is the
  wiring TODO shared with DualKappa.lean, FrozenHub.lean and
  DP6Ledger.lean.

  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace DP3M2Ledger

/-- An exact rational as (numerator, denominator), denominator a
positive `Nat`; comparisons cross-multiply into `Int`. -/
abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)

def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)

def qZero (a : Q) : Bool := decide (a.1 = 0)

def qEq (a b : Q) : Bool := decide (a.1 * qDen b = b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)

def qSum : List Q → Q
  | [] => (0, 1)
  | a :: rest => qAdd a (qSum rest)

/-- 4x Casimir of the spin label n (n = 2j): C(n) = n(n+2). -/
def casimir4 (n : Nat) : Nat := n * (n + 2)

/-- Dimension of the spin label n: d_n = n + 1. -/
def dimOf (n : Nat) : Nat := n + 1

def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0

def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1

def prodDSq (l : List Nat) : Nat :=
  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1

/-- A slab configuration: perimeter-wall classes q (two faces each),
interior walls w, and the two layers' tile spins. -/
structure Config where
  q : List Nat
  w : List Nat
  top : List Nat
  bot : List Nat
  deriving DecidableEq

/-- The s-exponent of a configuration, rederived in Lean:
E = 2 Sum C(q) + Sum C(w) + Sum C(top) + Sum C(bot). -/
def configExp (c : Config) : Nat :=
  2 * sumC c.q + sumC c.w + sumC c.top + sumC c.bot

/-- The assembly weight of a configuration, rederived in Lean:
Prod d_q^2 * Prod d_w * Prod d_top * Prod d_bot.  Strictly positive by
construction — which is exactly why a negative kernel coefficient can
only come from a negative network value N. -/
def configWeight (c : Config) : Nat :=
  prodDSq c.q * prodD c.w * prodD c.top * prodD c.bot


/-- Every configuration of T[1,1] at the fence exponent 76:
(configuration, D4 orbit multiplicity, exact Haar network value N).
All 8 are computed — none unreached — so the assembled
coefficient below is FINAL. -/
def e76Configs : List (Config × Nat × Q) :=
  [ ⟨⟨[0, 1, 2, 1], [1, 1, 1, 1], [1, 0, 1, 2], [1, 2, 1, 2]⟩, 4, (-1, 1492992)⟩,
    ⟨⟨[0, 1, 2, 1], [1, 1, 1, 1], [1, 2, 1, 0], [1, 2, 1, 2]⟩, 4, (-1, 1492992)⟩,
    ⟨⟨[0, 1, 2, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 0, 1, 2]⟩, 4, (-1, 1492992)⟩,
    ⟨⟨[0, 1, 2, 1], [1, 1, 1, 1], [1, 2, 1, 2], [1, 2, 1, 0]⟩, 4, (-1, 1492992)⟩,
    ⟨⟨[1, 2, 1, 2], [1, 1, 1, 1], [0, 1, 0, 1], [0, 1, 2, 1]⟩, 2, (0, 1)⟩,
    ⟨⟨[1, 2, 1, 2], [1, 1, 1, 1], [0, 1, 0, 1], [2, 1, 0, 1]⟩, 2, (0, 1)⟩,
    ⟨⟨[1, 2, 1, 2], [1, 1, 1, 1], [0, 1, 2, 1], [0, 1, 0, 1]⟩, 2, (0, 1)⟩,
    ⟨⟨[1, 2, 1, 2], [1, 1, 1, 1], [2, 1, 0, 1], [0, 1, 0, 1]⟩, 2, (0, 1)⟩ ]

/-- The contribution of one ledger row: mult * weight * N. -/
def rowContribution : Config × Nat × Q → Q
  | (c, mult, n) => qMulNat n (mult * configWeight c)

/-- Every listed configuration really sits at exponent 76 — the
exponent is recomputed in Lean from the labelling, not trusted. -/
theorem e76_exponents_are_76 :
    e76Configs.all (fun t => decide (configExp t.1 = 76)) = true := by
  decide

theorem e76_config_count : e76Configs.length = 8 := by decide

/-- Every assembly weight is strictly positive.  This is what
licenses the whole argument: since dimensions, Casimir powers and
orbit multiplicities are all positive, a negative coefficient in
T[n,m] can ONLY originate in a negative network value N — i.e. in
signed 6j recoupling interference, not in bookkeeping. -/
theorem e76_weights_positive :
    e76Configs.all (fun t => decide (0 < t.2.1 * configWeight t.1))
      = true := by decide

/-- Of the 8 configurations, 4 have vanishing network
value and 4 are strictly negative; none is positive.  The
negativity is 6j interference, not a bookkeeping artefact. -/
theorem e76_signs :
    e76Configs.all (fun t => qNeg t.2.2 || qZero t.2.2) = true := by
  decide

/-- **The entry-level fence** (kernel-checked): the assembled
coefficient of s^76 in T[1,1] is -32/3, hence strictly negative.
Claim DP.3-(i) — preservation of the coefficientwise cone C_exp —
is REFUTED at activity truncation M = 2. -/
theorem t11_coeff_76_value :
    qEq (qSum (e76Configs.map rowContribution)) (-32, 3) = true := by
  decide

theorem t11_coeff_76_negative :
    qNeg (qSum (e76Configs.map rowContribution)) = true := by decide

/-- The final part of T[1,1] at M = 2: every coefficient of
exponent < 78, exact regardless of which high-exponent
configurations exceeded their budget. -/
def t11Final : List (Nat × Q) :=
  [ (24, (5, 1)),
    (30, (12, 1)),
    (36, (2, 1)),
    (38, (24, 1)),
    (46, (72, 1)),
    (52, (48, 1)),
    (54, (144, 1)),
    (56, (34, 1)),
    (60, (48, 1)),
    (62, (232, 1)),
    (68, (84, 1)),
    (70, (848, 3)),
    (72, (64, 1)),
    (76, (-32, 3)) ]

/-- Exactly one coefficient of the final part is negative, and it
is the s^76 fence; every other coefficient is strictly positive. -/
theorem t11_final_unique_negative :
    (t11Final.filter (fun t => qNeg t.2)).map (fun t => t.1) = [76]
      := by decide

/-- Non-vacuity pin: the final-part ledger is not empty, so the
`List.all` verdicts above are not trivially true. -/
theorem t11_final_count : t11Final.length = 14 := by decide

theorem t11_final_others_positive :
    (t11Final.filter (fun t => t.1 != 76)).all
      (fun t => qPos t.2) = true := by decide

/-- The aggregated fence.  For the heat-kernel envelope
v_m = d_m s^{C(m)}, the coefficient of s^79 in (Bv)_1 collects
T[1,m] at exponent 79 - C(m), weighted by d_m.  Entries:
(m, feeding exponent, T[1,m] coefficient there). -/
def blocked79 : List (Nat × Nat × Q) :=
  [ (0, 79, (0, 1)),
    (1, 76, (-32, 3)),
    (2, 71, (0, 1)) ]

def blockedContribution : Nat × Nat × Q → Q
  | (m, _, c) => qMulNat c (dimOf m)

/-- Non-vacuity pin. -/
theorem blocked79_count : blocked79.length = 3 := by decide

/-- The feeding exponents are the arithmetically correct ones:
79 - C(m) for m = 0, 1, 2. -/
theorem blocked79_exponents :
    blocked79.all (fun t => decide (t.2.1 + casimir4 t.1 = 79))
      = true := by decide

/-- **No cancellation is available.**  Both sibling channels
vanish identically at their feeding exponents, so the negative
contribution from T[1,1] stands alone — the DP.6 repair route
(cancellation across m at fixed output exponent) is CLOSED. -/
theorem blocked_79_no_cancellation :
    (blocked79.filter (fun t => t.1 != 1)).all
      (fun t => qZero t.2.2) = true := by decide

/-- **The aggregated fence** (kernel-checked): the coefficient of
s^79 in the blocked image (Bv)_1 is -64/3, strictly negative. -/
theorem blocked_79_value :
    qEq (qSum (blocked79.map blockedContribution)) (-64, 3) = true := by
  decide

theorem blocked_79_negative :
    qNeg (qSum (blocked79.map blockedContribution)) = true := by decide

/-- The final part of T[1,1] with a common denominator cleared:
(exponent, integer coefficient), where the integer is c_E * den.
The scaling is not trusted — `t11_scaled_matches` re-checks every
row against `t11Final` in the kernel. -/
def t11Scaled : List (Nat × Int) :=
  [ (24, 15),
    (30, 36),
    (36, 6),
    (38, 72),
    (46, 216),
    (52, 144),
    (54, 432),
    (56, 102),
    (60, 144),
    (62, 696),
    (68, 252),
    (70, 848),
    (72, 192),
    (76, -32) ]

def scaleDen : Nat := 3

/-- Each scaled coefficient really is c_E * scaleDen. -/
theorem t11_scaled_matches :
    (t11Final.zip t11Scaled).all (fun p =>
      decide (p.1.1 = p.2.1) && qEq (qMulNat p.1.2 scaleDen)
        (p.2.2, 1)) = true := by decide

theorem t11_scaled_length :
    t11Scaled.length = t11Final.length := by decide

/-- Numerator of the value of the scaled ledger at s = a/b:
N = Sum_E k_E * a^E * b^(scale - E).  Since b^scale > 0 and
scaleDen > 0, `0 < N` is equivalent to positivity of the
polynomial at s = a/b. -/
def evalNum (l : List (Nat × Int)) (a b scale : Nat) : Int :=
  l.foldl (fun acc t =>
    acc + t.2 * Int.ofNat (a ^ t.1) * Int.ofNat (b ^ (scale - t.1))) 0

/-- Evaluation pins for the final part of T[1,1] (max exponent
76, common denominator 3).  Despite the negative
coefficient at s^76 the entry is strictly positive at each of
these exact rational couplings.  This is a WITNESS, not a proof
of positivity on all of (0,1) — that statement is certified by
Sturm in computations/, and is deliberately not claimed here. -/
theorem t11_final_positive_at :
    decide (0 < evalNum t11Scaled 1 4 76)
      && decide (0 < evalNum t11Scaled 1 2 76)
      && decide (0 < evalNum t11Scaled 3 4 76)
      = true := by decide

/-- eps_slab(1): certified truncation exponents E*(n,m,1) — the
minimum s-exponent of any admissible slab configuration carrying
spin 2.  Entries: ((n, m), E*). -/
def epsStar : List ((Nat × Nat) × Nat) :=
  [ ((0, 0), 38),
    ((0, 1), 32),
    ((0, 2), 32),
    ((0, 3), 68),
    ((1, 1), 38),
    ((1, 2), 44),
    ((1, 3), 56),
    ((2, 2), 56),
    ((2, 3), 68),
    ((3, 3), 88) ]

/-- The naive single-face bound: one face at spin 2 costs C(2). -/
def naiveBound : Nat := casimir4 2

theorem naive_bound_is_eight : naiveBound = 8 := by decide

/-- Non-vacuity pin. -/
theorem eps_star_count : epsStar.length = 10 := by decide

/-- **Every certified exponent beats the naive bound**, by at
least a factor of four: a spin-2 face cannot appear in isolation,
because the triads at the 4-valent interior edge and at the
corner-linked perimeter classes force companion faces up with
it. -/
theorem eps_star_beats_naive :
    epsStar.all (fun t => decide (4 * naiveBound <= t.2)) = true := by
  decide

/-- The global truncation exponent is 32. -/
theorem eps_star_min :
    (epsStar.all (fun t => decide (32 <= t.2))
      && epsStar.any (fun t => decide (t.2 = 32))) = true := by decide

end DP3M2Ledger
