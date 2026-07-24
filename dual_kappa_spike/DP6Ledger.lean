/-
  DP6Ledger.lean — the DP.6 signed-sector survival verdict,
  kernel-checked at the coefficient-ledger level.

  GENERATED FILE: emitted by lean_out/gen_dp6_lean.py from
  dp6_results.json; upstream computation
  computations/dp6_signed_survival.py (the exact s-weighted channel
  sums over the full C(128,3) = 341,376 triple-surface corpus of the
  4-cube boundary, spin-3 sector included; amplitudes from the
  certified vertex product formula, all arithmetic Fraction-exact).
  Do not edit literals by hand — regenerate.

  The verdict this file banks (DP.6 SPLIT VERDICT):

  * PER-CLASS SURVIVAL FAILS.  Every configuration class (= spin
    profile) has channel sum c · (Σ Z) · s^E, a single monomial, so
    its sign on (0,1) is s-INDEPENDENT — and exactly four classes
    have negative channel sums (`negClasses`, kernel-checked
    negative).  This is the Lakatos fence: the counterexample side
    of the verdict, machine-banked.

  * THE GLOBAL SUM SURVIVES.  All 80 monomial coefficients of the
    global sum with lower sectors folded in (`globalMonomials`), and
    all 75 of the triples-only sum (`globalTriplesMonomials`), are
    strictly positive (kernel-checked), hence each global sum is a
    positive combination of s^E on (0,1) and strictly positive
    there.  Only the coefficient-sign ledger is formalized here;
    "positive polynomial on (0,1)" as a statement about real/rational
    evaluation is NOT formalized in this file (the FrozenHub-style
    evalNum bridge is the natural next step).

  * THE CANCELLATION IS LOCAL IN THE EXPONENT.  At each negative
    class's exponent E ∈ {136, 138, 148, 172}, the positive
    subtotal P_E and negative subtotal N_E of the classes sharing
    that exponent satisfy N_E < 0 < P_E + N_E, and P_E + N_E equals
    the recorded global s^E coefficient (`exponent_ledger_balances`,
    `ledger_matches_global`): positivity is restored class-by-class
    at exponent granularity, not by cross-exponent competition.

  Rationals are (numerator : Int, denominator : Nat) pairs with
  positive denominators; all comparisons cross-multiply into Int so
  kernel `decide` stays on closed integer arithmetic.

  Provenance caveat (spike-wide): the ledger literals are transported
  from the Python quaternion-Haar machinery; re-deriving them inside
  Lean from the main tree's finite product Haar evaluation is the
  wiring TODO shared with DualKappa.lean and FrozenHub.lean.

  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace DP6Ledger

/-- An exact rational as (numerator, denominator) with the denominator
a positive `Nat`; comparisons cross-multiply into `Int` so every proof
below is closed integer arithmetic under kernel `decide`. -/
abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)

def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)

/-- Cross-multiplied equality (valid whenever denominators are
positive, which `qPos`/`qNeg`/`ledgerBalanced` also check). -/
def qEq (a b : Q) : Bool := decide (a.1 * qDen b = b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)

/-- Spin profile as (spin, multiplicity) pairs. -/
abbrev Profile := List (Nat × Nat)

/-- Heat-kernel exponent of a profile: E = Σ n(n+2)·mult
(4C₂(n/2) = n(n+2); in-Lean rederivation of the engine's
`profile_weight`). -/
def profileExp (p : Profile) : Nat :=
  p.foldl (fun acc t => acc + t.1 * (t.1 + 2) * t.2) 0

/-- Dimension coefficient of a profile: c = Π (n+1)^mult. -/
def profileCoeff (p : Profile) : Nat :=
  p.foldl (fun acc t => acc * (t.1 + 1) ^ t.2) 1

/-- The 80-monomial GLOBAL sum with lower sectors folded in (empty + singles + pairs + triples): (exponent E, coefficient of s^E).  Transcribed from dp6_results.json global_with_lower.polynomial. -/
def globalMonomials : List (Nat × Q) :=
  [ (0, (2, 1)),
    (18, (64, 1)),
    (30, (192, 1)),
    (36, (576, 1)),
    (38, (576, 1)),
    (42, (384, 1)),
    (48, (6, 1)),
    (50, (1152, 1)),
    (52, (2304, 1)),
    (58, (6048, 1)),
    (60, (3840, 1)),
    (62, (2304, 1)),
    (64, (648, 1)),
    (66, (7488, 1)),
    (68, (4992, 1)),
    (70, (1920, 1)),
    (72, (648, 1)),
    (74, (14592, 1)),
    (76, (8448, 1)),
    (78, (7488, 1)),
    (80, (3696, 1)),
    (82, (21376, 1)),
    (84, (30592, 1)),
    (86, (19200, 1)),
    (88, (6792, 1)),
    (90, (100736, 3)),
    (92, (20992, 1)),
    (94, (33280, 1)),
    (96, (17740, 1)),
    (98, (21664, 1)),
    (100, (68096, 3)),
    (102, (149408, 3)),
    (104, (29696, 1)),
    (106, (495520, 9)),
    (108, (25728, 1)),
    (110, (935584, 9)),
    (112, (155154530, 2187)),
    (114, (345728, 3)),
    (116, (125696, 3)),
    (118, (2386432, 27)),
    (120, (824872, 9)),
    (122, (34372672, 243)),
    (124, (82560, 1)),
    (126, (293056, 3)),
    (128, (3795856, 81)),
    (130, (3884344, 27)),
    (132, (7940768, 81)),
    (134, (1420736, 9)),
    (136, (64156088, 729)),
    (138, (9308224, 81)),
    (140, (2554304, 27)),
    (142, (540368, 3)),
    (144, (400900, 3)),
    (146, (43222768, 243)),
    (148, (115563136, 2187)),
    (150, (11567608, 81)),
    (152, (9037369, 81)),
    (154, (4135264, 27)),
    (156, (1655552, 27)),
    (158, (8819884, 81)),
    (160, (6910313, 108)),
    (162, (6805058, 81)),
    (164, (984496, 27)),
    (166, (2608297, 54)),
    (168, (3995680, 81)),
    (170, (10865932, 243)),
    (172, (22143808, 2187)),
    (174, (869000, 81)),
    (176, (11632369, 5184)),
    (178, (286898, 9)),
    (180, (335837, 54)),
    (182, (587497, 81)),
    (184, (19520, 729)),
    (186, (3759065, 864)),
    (188, (27056, 9)),
    (190, (20809, 108)),
    (192, (33574115, 196608)),
    (194, (1, 162)),
    (196, (192, 1)),
    (198, (3488, 3)) ]

/-- The 75-monomial triples-only global sum: (exponent E, coefficient of s^E).  Transcribed from dp6_results.json global.polynomial. -/
def globalTriplesMonomials : List (Nat × Q) :=
  [ (36, (64, 1)),
    (38, (288, 1)),
    (50, (576, 1)),
    (52, (1152, 1)),
    (58, (3456, 1)),
    (60, (2304, 1)),
    (62, (1152, 1)),
    (64, (324, 1)),
    (66, (3744, 1)),
    (68, (2496, 1)),
    (70, (960, 1)),
    (72, (648, 1)),
    (74, (10464, 1)),
    (76, (5376, 1)),
    (78, (4608, 1)),
    (80, (3102, 1)),
    (82, (16064, 1)),
    (84, (20480, 1)),
    (86, (15360, 1)),
    (88, (6792, 1)),
    (90, (77152, 3)),
    (92, (17920, 1)),
    (94, (29152, 1)),
    (96, (17736, 1)),
    (98, (19136, 1)),
    (100, (61216, 3)),
    (102, (145472, 3)),
    (104, (29696, 1)),
    (106, (485120, 9)),
    (108, (25728, 1)),
    (110, (935392, 9)),
    (112, (155154529, 2187)),
    (114, (345440, 3)),
    (116, (125696, 3)),
    (118, (2386432, 27)),
    (120, (824872, 9)),
    (122, (34372672, 243)),
    (124, (82560, 1)),
    (126, (293056, 3)),
    (128, (3795856, 81)),
    (130, (3884344, 27)),
    (132, (7940768, 81)),
    (134, (1420736, 9)),
    (136, (64156088, 729)),
    (138, (9308224, 81)),
    (140, (2554304, 27)),
    (142, (540368, 3)),
    (144, (400900, 3)),
    (146, (43222768, 243)),
    (148, (115563136, 2187)),
    (150, (11567608, 81)),
    (152, (9037369, 81)),
    (154, (4135264, 27)),
    (156, (1655552, 27)),
    (158, (8819884, 81)),
    (160, (6910313, 108)),
    (162, (6805058, 81)),
    (164, (984496, 27)),
    (166, (2608297, 54)),
    (168, (3995680, 81)),
    (170, (10865932, 243)),
    (172, (22143808, 2187)),
    (174, (869000, 81)),
    (176, (11632369, 5184)),
    (178, (286898, 9)),
    (180, (335837, 54)),
    (182, (587497, 81)),
    (184, (19520, 729)),
    (186, (3759065, 864)),
    (188, (27056, 9)),
    (190, (20809, 108)),
    (192, (33574115, 196608)),
    (194, (1, 162)),
    (196, (192, 1)),
    (198, (3488, 3)) ]

/-- **Every global coefficient is strictly positive** (kernel-checked):
the full ≤-triples global sum is a positive combination of the
monomials s^E, hence strictly positive at every s ∈ (0,1).  (The
pointwise-evaluation reading is the engine's `coefficient-signs`
certificate; only the coefficient-sign ledger is formalized here.) -/
theorem global_coeffs_pos :
    globalMonomials.all (fun t => qPos t.2) = true := by decide

theorem global_monomial_count : globalMonomials.length = 80 := by decide

/-- Same positivity for the triples-only global sum. -/
theorem global_triples_coeffs_pos :
    globalTriplesMonomials.all (fun t => qPos t.2) = true := by decide

theorem global_triples_count :
    globalTriplesMonomials.length = 75 := by decide

/-- Exponent lists are strictly ascending: the ledgers are honest
single-coefficient-per-exponent normal forms. -/
def expsAscending : List (Nat × Q) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.1 < b.1) && expsAscending (b :: rest)

theorem global_exps_ascending :
    (expsAscending globalMonomials && expsAscending globalTriplesMonomials)
      = true := by decide

/-- The four classes with NEGATIVE channel sums — the counterexample
side of the split verdict (per-class positivity fails; the Lakatos
fence).  Entries: (profile, class sum Σ Z, channel coefficient
c·ΣZ from the cancellation ledger).  Because a class channel is the
single monomial c·(ΣZ)·s^E, each negative sum is negative on ALL of
s ∈ (0,1) — the sign is s-independent. -/
def negClasses : List (Profile × Q × Q) :=
  [ ([(1, 8), (2, 11), (3, 4)], (-1, 60466176), (-192, 1)),
    ([(1, 9), (2, 12), (3, 1)], (-7, 12754584), (-1792, 3)),
    ([(1, 10), (2, 11), (3, 2)], (-11, 76527504), (-11264, 27)),
    ([(1, 11), (2, 11), (3, 1)], (-5, 38263752), (-5120, 27)) ]

/-- Per-entry check: both the class sum and the channel coefficient
are negative, and the channel coefficient really is (Σ Z)·c with c
rederived in Lean from the profile — the "class channels are
monomials" bookkeeping is internally consistent. -/
def negClassCheck : Profile × Q × Q → Bool
  | (prof, zsum, chan) =>
    qNeg zsum && qNeg chan && qEq (qMulNat zsum (profileCoeff prof)) chan

/-- **Per-class survival fails** (kernel-checked): all four recorded
class channel sums are strictly negative. -/
theorem neg_classes_neg : negClasses.all negClassCheck = true := by decide

/-- Cancellation ledger at the negative-class exponents
E ∈ {136, 138, 148, 172} (ledger order follows the sorted negative
profiles: 172, 138, 148, 136).  Entries: (E, positive subtotal P_E,
negative subtotal N_E, recorded global s^E coefficient G_E), each
subtotal summed over every class sharing exponent E. -/
def cancellationLedger : List (Nat × Q × Q × Q) :=
  [ (172, (22563712, 2187), (-192, 1), (22143808, 2187)),
    (138, (9356608, 81), (-1792, 3), (9308224, 81)),
    (148, (116475520, 2187), (-11264, 27), (115563136, 2187)),
    (136, (64294328, 729), (-5120, 27), (64156088, 729)) ]

def ledgerBalanced : Nat × Q × Q × Q → Bool
  | (_, p, n, g) => qPos p && qNeg n && qPos g && qEq (qAdd p n) g

/-- **The cancellation balances at exponent granularity**
(kernel-checked): at each negative-class exponent the negative
subtotal is strictly negative, yet P_E + N_E = G_E > 0 — the spin-3
negativity is beaten inside its own s-exponent, not across
exponents. -/
theorem exponent_ledger_balances :
    cancellationLedger.all ledgerBalanced = true := by decide

/-- Coefficient lookup in a monomial ledger (0 if absent). -/
def coeffAt (l : List (Nat × Q)) (e : Nat) : Q :=
  match l.find? (fun t => t.1 == e) with
  | some t => t.2
  | none => (0, 1)

/-- The ledger's G_E agrees with the triples-only global ledger at
every negative-class exponent — the two JSON records are one. -/
theorem ledger_matches_global :
    cancellationLedger.all
      (fun t => qEq (coeffAt globalTriplesMonomials t.1) t.2.2.2)
      = true := by decide

/-- The negative-class exponents, rederived in Lean from the profiles,
are exactly the ledger's exponents (same order). -/
theorem neg_class_exponents :
    negClasses.map (fun t => profileExp t.1)
      = cancellationLedger.map (fun t => t.1) := by decide

/-- Sanity pins (§15a): corpus size, negative census, minimal
exemplar. -/
def tripleCount : Nat := 341376

def negativeCount : Nat := 32384

def minExemplarZ : Q := (-1, 3981312)

def minExemplarProfile : Profile := [(1, 9), (2, 6), (3, 3)]

theorem sanity_pins :
    (decide (negativeCount < tripleCount)
        && qNeg minExemplarZ
        && (profileExp minExemplarProfile == 120)
        && (profileCoeff minExemplarProfile == 23887872))
      = true := by decide

end DP6Ledger
