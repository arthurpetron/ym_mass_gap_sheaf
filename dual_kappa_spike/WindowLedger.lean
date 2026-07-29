/-
  WindowLedger.lean — the certified X_11 (M -> infinity)
  windows, kernel-checked at the ledger level.

  GENERATED FILE: emitted by scripts/gen_window_lean.py from
  dp3_m2_entries.json + the merged banked value ledgers;
  upstream engines rust/haar_contract (§16j, gated) and
  computations/su2_cut_eval.py.  Do not edit — regenerate.

  WHAT THE KERNEL CHECKS (work_plan §16l):

  * T[n,m](s) is ASSEMBLED in-kernel: census polynomial
    evaluated at the exact rational coupling + resolved-config
    rows with assembly weight W and exponent E rederived from
    the labelling (DP3M2Ledger's evalNum precedent, extended).
  * The unresolved-mass bound U is assembled from the SAME
    labelling: crude rows use the fully-rederived W * cN; CS
    rows use W * min(cN, r) with the cited r kernel-checked
    (r >= 0, r^2 >= D_a * D_b) and the cited partner values
    kernel-LOCATED in the cited diagonal ledger through the
    D4 action (`d4Images`), so no citation is trusted.
  * lo = T - U - tail > 0 at all grid points (all entries),
    and lo11 * lo00 > hi01^2 at the CERT points — i.e.
    X_11 = log(T11 T00 / T01^2) > 0, the blocked one-step
    mass-gap observable exceeds its U(1) mirror value 0.

  TRANSCRIBED (provenance-caveated): census polynomials
  (dp3_m2_entries), landed N values and cited diagonal values
  (the exact engines; independently banked in OSCSLedger with
  OS-positivity + CS checks), tail bounds (level-3 CS tail +
  domination levels >= 4 + Lambda-slop at Lambda = 8, rounded
  UP to 10^-60: still valid upper bounds).  Mathematical
  inputs licensing the bound structure: the OS/CS lemma
  |N| <= sqrt(D_a D_b) (§16h) and D4 value-invariance (gated;
  the ACTION is rederived here).

  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

namespace WindowLedger

abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)

def qNonneg (a : Q) : Bool := decide (0 ≤ a.1) && decide (0 < a.2)

def qLe (a b : Q) : Bool := decide (a.1 * qDen b ≤ b.1 * qDen a)

def qLt (a b : Q) : Bool := decide (a.1 * qDen b < b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qSub (a b : Q) : Q := (a.1 * qDen b - b.1 * qDen a, a.2 * b.2)

def qMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)

def qSq (a : Q) : Q := qMul a a

def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)

def natQ (k : Nat) : Q := (Int.ofNat k, 1)

def qMin (a b : Q) : Q := if qLe a b then a else b

def qSum : List Q → Q
  | [] => (0, 1)
  | a :: rest => qAdd a (qSum rest)

/-- s^e for s = a/b. -/
def qPow (a b e : Nat) : Q := (Int.ofNat (a ^ e), b ^ e)

def casimir4 (n : Nat) : Nat := n * (n + 2)

def dimOf (n : Nat) : Nat := n + 1

def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0

def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1

def prodDSq (l : List Nat) : Nat :=
  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1

structure Config where
  q : List Nat
  w : List Nat
  top : List Nat
  bot : List Nat
  deriving BEq, DecidableEq

structure Key where
  loop : Nat
  q : List Nat
  w : List Nat
  t : List Nat
  deriving BEq, DecidableEq

def rot (r : Nat) (l : List Nat) : List Nat := l.drop r ++ l.take r

def reflAnchored : List Nat → List Nat
  | [] => []
  | x :: rest => x :: rest.reverse

def d4Images (k : Key) : List Key :=
  (List.range 4).flatMap (fun r =>
    let qq := rot r k.q
    let ww := rot r k.w
    let tt := rot r k.t
    [ ⟨k.loop, qq, ww, tt⟩,
      ⟨k.loop, reflAnchored qq, ww.reverse, reflAnchored tt⟩ ])

/-- The s-exponent, rederived from the labelling. -/
def configExp (c : Config) : Nat :=
  2 * sumC c.q + sumC c.w + sumC c.top + sumC c.bot

/-- The assembly weight W (loop dims excluded), rederived. -/
def wdOf (c : Config) : Nat :=
  prodDSq c.q * prodD c.w * prodD c.top * prodD c.bot

/-- The crude |N| bound cN = d_n d_m prod_f d_f, rederived. -/
def cnOf (n m : Nat) (c : Config) : Nat :=
  dimOf n * dimOf m * prodDSq c.q * prodD c.w * prodD c.top
    * prodD c.bot

/-- The cited diagonal values used by the CS rows — the subset
of OSCSLedger's diagLedger that the U bounds below cite;
9 entries, all landed. -/
def citedDiag : List (Key × Q) :=
  [ ⟨⟨0, [0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2]⟩, (1, 6561)⟩,
    ⟨⟨0, [1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2]⟩, (1, 2519424)⟩,
    ⟨⟨1, [1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2]⟩, (1, 93312)⟩,
    ⟨⟨1, [1, 1, 1, 1], [0, 2, 2, 2], [2, 2, 2, 2]⟩, (1, 7558272)⟩,
    ⟨⟨1, [1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2]⟩, (1, 1259712)⟩,
    ⟨⟨1, [1, 1, 1, 2], [2, 2, 1, 1], [2, 2, 2, 1]⟩, (1, 90699264)⟩,
    ⟨⟨1, [1, 1, 2, 2], [0, 1, 2, 1], [2, 2, 1, 1]⟩, (1, 272097792)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1]⟩, (1, 3359232)⟩,
    ⟨⟨1, [1, 1, 2, 2], [2, 1, 2, 1], [2, 2, 1, 1]⟩, (1, 204073344)⟩ ]

theorem cited_count : citedDiag.length = 9 := by decide

theorem cited_nonneg :
    citedDiag.all (fun r => qNonneg r.2) = true := by decide

def locates (k : Key) (v : Q) : Bool :=
  (d4Images k).any (fun img =>
    citedDiag.any (fun row => row.1 == img && row.2 == v))

/-- The M = 2 census polynomial of T[0,0] (dp3_m2_entries). -/
def poly00 : List (Nat × Q) :=
  [ (0, (1, 1)),
    (18, (16, 1)),
    (30, (16, 1)),
    (36, (32, 1)),
    (38, (48, 1)),
    (42, (16, 1)),
    (48, (40, 1)),
    (50, (96, 1)),
    (58, (96, 1)),
    (64, (72, 1)),
    (66, (144, 1)),
    (68, (64, 1)),
    (70, (96, 1)),
    (74, (48, 1)),
    (80, (36, 1)),
    (82, (32, 1)),
    (90, (272, 1)),
    (94, (48, 1)),
    (96, (162, 1)),
    (100, (224, 3)),
    (102, (16, 1)),
    (112, (36, 1)),
    (114, (48, 1)),
    (120, (216, 1)),
    (122, (192, 1)),
    (128, (9, 1)),
    (144, (162, 1)) ]

/-- Resolved configs of T[0,0]: (config, exact N); weight and exponent rederived. -/
def addRows00 : List (Config × Q) :=
  [ ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [0, 1, 1, 1]⟩, (1, 4096)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 73728)⟩,
    ⟨⟨[0, 1, 1, 2], [1, 2, 1, 2], [0, 1, 1, 2], [0, 1, 1, 2]⟩, (1, 20736)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (7, 442368)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [0, 1, 2, 2]⟩, (1, 104976)⟩,
    ⟨⟨[0, 2, 1, 2], [2, 1, 1, 2], [0, 2, 1, 2], [0, 2, 1, 2]⟩, (1, 104976)⟩,
    ⟨⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [1, 1, 2, 2]⟩, (1, 839808)⟩ ]

/-- CS-bounded unresolved configs of T[0,0]: (config, D_a, D_b, r). -/
def csRows00 : List (Config × Q × Q × Q) :=
  [ ⟨⟨[0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]⟩, (1, 6561), (1, 6561), (1524157902758725803993293705227861607, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [1, 1, 2, 2]⟩, (1, 2519424), (1, 2519424), (3969161205100848447899202357364223, 10000000000000000000000000000000000000000)⟩ ]

/-- Crude-bounded unresolved configs of T[0,0]. -/
def crudeRows00 : List Config :=
  [ ⟨[0, 2, 2, 2], [2, 2, 2, 2], [0, 2, 2, 2], [0, 2, 2, 2]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [1, 2, 2, 2], [1, 2, 2, 2]⟩,
    ⟨[2, 2, 2, 2], [0, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]⟩,
    ⟨[2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]⟩ ]

def tVal00 (a b : Nat) : Q :=
  qAdd (qSum (poly00.map (fun t => qMul t.2 (qPow a b t.1))))
       (qSum (addRows00.map (fun r =>
         qMul (qMulNat r.2 (wdOf r.1))
              (qPow a b (configExp r.1)))))

def uVal00 (a b : Nat) : Q :=
  qAdd (qSum (csRows00.map (fun r =>
         qMul (qMulNat (qMin r.2.2.2 (natQ (cnOf 0 0 r.1)))
                       (wdOf r.1))
              (qPow a b (configExp r.1)))))
       (qSum (crudeRows00.map (fun c =>
         qMul (natQ (wdOf c * cnOf 0 0 c))
              (qPow a b (configExp c)))))

/-- Every CS citation of T[0,0] is valid: r >= 0,
r^2 >= D_a * D_b, and both cited values are located in
`citedDiag` at a D4 image of the demanded key. -/
theorem cs_valid00 :
    csRows00.all (fun r =>
      qNonneg r.2.2.2
      && qLe (qMul r.2.1 r.2.2.1) (qSq r.2.2.2)
      && locates ⟨0, r.1.q, r.1.w, r.1.top⟩ r.2.1
      && locates ⟨0, r.1.q, r.1.w, r.1.bot⟩ r.2.2.1)
      = true := by decide

/-- The M = 2 census polynomial of T[1,1] (dp3_m2_entries). -/
def poly11 : List (Nat × Q) :=
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
    (76, (-32, 3)),
    (78, (640, 1)),
    (80, (48, 1)),
    (84, (64, 9)),
    (86, (352, 1)),
    (88, (683, 3)),
    (92, (16, 27)),
    (94, (332, 27)),
    (96, (704, 3)),
    (100, (14, 243)),
    (102, (-32, 27)),
    (104, (350, 1)),
    (112, (24, 1)) ]

/-- Resolved configs of T[1,1]: (config, exact N); weight and exponent rederived. -/
def addRows11 : List (Config × Q) :=
  [ ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 0, 2, 2]⟩, (1, 124416)⟩,
    ⟨⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 0, 2, 1]⟩, (1, 746496)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 0, 1, 1]⟩, (1, 124416)⟩,
    ⟨⟨[0, 0, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩, (1, 104976)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]⟩, (1, 93312)⟩,
    ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 0, 2, 2], [1, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 0, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 0, 2, 1], [1, 2, 2, 1]⟩, (-1, 3359232)⟩,
    ⟨⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 0, 2, 1]⟩, (-1, 3359232)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 0, 1, 1], [1, 2, 1, 1]⟩, (-1, 3359232)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 0, 1, 1]⟩, (-1, 3359232)⟩,
    ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [1, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨[0, 1, 1, 2], [1, 2, 1, 2], [1, 2, 2, 1], [1, 2, 2, 1]⟩, (1, 5038848)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [1, 2, 1, 1], [1, 2, 1, 1]⟩, (11, 30233088)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [0, 2, 1, 1]⟩, (1, 3359232)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [2, 0, 1, 1]⟩, (-1, 10077696)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [0, 2, 1, 1]⟩, (-1, 10077696)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [2, 0, 1, 1]⟩, (1, 3359232)⟩ ]

/-- CS-bounded unresolved configs of T[1,1]: (config, D_a, D_b, r). -/
def csRows11 : List (Config × Q × Q × Q) :=
  [ ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [0, 0, 2, 2], [2, 2, 2, 2]⟩, (1, 93312), (1, 7558272), (11907483615302545343697607072092669, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [2, 2, 2, 2], [0, 0, 2, 2]⟩, (1, 7558272), (1, 93312), (11907483615302545343697607072092669, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [0, 1, 2, 1], [2, 2, 1, 1], [2, 2, 1, 1]⟩, (1, 272097792), (1, 272097792), (287121036248614615733449244601, 78125000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [0, 2, 1, 1], [2, 2, 1, 1]⟩, (1, 3359232), (1, 204073344), (381932715036999041916689939513927, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 0, 1, 1], [2, 2, 1, 1]⟩, (1, 3359232), (1, 204073344), (381932715036999041916689939513927, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 2, 1, 1], [0, 2, 1, 1]⟩, (1, 204073344), (1, 3359232), (381932715036999041916689939513927, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 2, 1, 1], [2, 0, 1, 1]⟩, (1, 204073344), (1, 3359232), (381932715036999041916689939513927, 10000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2], [0, 2, 2, 2]⟩, (1, 1259712), (1, 1259712), (3969161205100848447899202357364223, 5000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2], [2, 0, 2, 2]⟩, (1, 1259712), (1, 1259712), (3969161205100848447899202357364223, 5000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2], [2, 2, 2, 0]⟩, (1, 1259712), (1, 1259712), (3969161205100848447899202357364223, 5000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 0, 2, 2], [0, 2, 2, 2]⟩, (1, 1259712), (1, 1259712), (3969161205100848447899202357364223, 5000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]⟩, (1, 1259712), (1, 1259712), (3969161205100848447899202357364223, 5000000000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 2], [2, 2, 1, 1], [2, 2, 2, 1], [2, 2, 2, 1]⟩, (1, 90699264), (1, 90699264), (861363108745843847200347733803, 78125000000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [2, 2, 1, 1], [2, 2, 1, 1]⟩, (1, 204073344), (1, 204073344), (95707012082871538577816414867, 19531250000000000000000000000000000000)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]⟩, (1, 7558272), (1, 7558272), (2584089326237531541601043201409, 19531250000000000000000000000000000000)⟩ ]

/-- Crude-bounded unresolved configs of T[1,1]. -/
def crudeRows11 : List Config :=
  [ ⟨[1, 2, 2, 2], [1, 2, 2, 1], [0, 1, 1, 1], [0, 1, 1, 1]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [0, 1, 1, 1], [2, 1, 1, 1]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [2, 1, 1, 1], [0, 1, 1, 1]⟩,
    ⟨[0, 2, 2, 2], [2, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [2, 1, 1, 1], [2, 1, 1, 1]⟩,
    ⟨[1, 1, 1, 1], [2, 2, 2, 2], [0, 2, 2, 2], [2, 2, 2, 2]⟩,
    ⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 0, 2, 2], [2, 2, 2, 2]⟩,
    ⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 2, 2, 2], [0, 2, 2, 2]⟩,
    ⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 2, 2, 2], [2, 0, 2, 2]⟩,
    ⟨[2, 2, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩,
    ⟨[1, 1, 1, 1], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]⟩,
    ⟨[2, 2, 2, 2], [2, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1]⟩ ]

def tVal11 (a b : Nat) : Q :=
  qAdd (qSum (poly11.map (fun t => qMul t.2 (qPow a b t.1))))
       (qSum (addRows11.map (fun r =>
         qMul (qMulNat r.2 (wdOf r.1))
              (qPow a b (configExp r.1)))))

def uVal11 (a b : Nat) : Q :=
  qAdd (qSum (csRows11.map (fun r =>
         qMul (qMulNat (qMin r.2.2.2 (natQ (cnOf 1 1 r.1)))
                       (wdOf r.1))
              (qPow a b (configExp r.1)))))
       (qSum (crudeRows11.map (fun c =>
         qMul (natQ (wdOf c * cnOf 1 1 c))
              (qPow a b (configExp c)))))

/-- Every CS citation of T[1,1] is valid: r >= 0,
r^2 >= D_a * D_b, and both cited values are located in
`citedDiag` at a D4 image of the demanded key. -/
theorem cs_valid11 :
    csRows11.all (fun r =>
      qNonneg r.2.2.2
      && qLe (qMul r.2.1 r.2.2.1) (qSq r.2.2.2)
      && locates ⟨1, r.1.q, r.1.w, r.1.top⟩ r.2.1
      && locates ⟨1, r.1.q, r.1.w, r.1.bot⟩ r.2.2.1)
      = true := by decide

/-- The M = 2 census polynomial of T[0,1] (dp3_m2_entries). -/
def poly01 : List (Nat × Q) :=
  [ (12, (2, 1)),
    (24, (8, 1)),
    (30, (8, 1)),
    (32, (24, 1)),
    (36, (14, 1)),
    (44, (24, 1)),
    (46, (72, 1)),
    (52, (108, 1)),
    (54, (48, 1)),
    (56, (48, 1)),
    (60, (168, 1)),
    (62, (48, 1)),
    (64, (40, 1)),
    (68, (262, 1)),
    (72, (72, 1)),
    (76, (200, 3)),
    (78, (200, 1)),
    (80, (48, 1)),
    (84, (336, 1)),
    (86, (32, 1)),
    (88, (88, 1)),
    (92, (332, 3)),
    (94, (24, 1)),
    (96, (80, 3)),
    (100, (692, 27)),
    (102, (-16, 3)),
    (104, (104, 1)),
    (108, (102, 1)),
    (112, (-32, 3)),
    (124, (72, 1)) ]

/-- Resolved configs of T[0,1]: (config, exact N); weight and exponent rederived. -/
def addRows01 : List (Config × Q) :=
  [ ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 0, 2, 2]⟩, (1, 27648)⟩,
    ⟨⟨[0, 1, 1, 1], [1, 2, 2, 1], [0, 1, 1, 1], [1, 2, 2, 2]⟩, (1, 41472)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [0, 0, 2, 2]⟩, (1, 82944)⟩,
    ⟨⟨[0, 0, 2, 2], [0, 2, 2, 2], [0, 0, 2, 2], [1, 1, 1, 1]⟩, (1, 26244)⟩,
    ⟨⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [0, 0, 1, 1]⟩, (1, 186624)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 0, 1, 1]⟩, (1, 139968)⟩,
    ⟨⟨[1, 1, 1, 1], [0, 2, 2, 2], [1, 1, 1, 1], [2, 2, 2, 2]⟩, (1, 746496)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [0, 2, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [2, 0, 2, 2]⟩, (1, 373248)⟩,
    ⟨⟨[0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 2], [1, 2, 1, 1]⟩, (1, 1259712)⟩,
    ⟨⟨[1, 1, 1, 2], [2, 2, 1, 1], [1, 1, 1, 2], [2, 2, 2, 1]⟩, (1, 10077696)⟩,
    ⟨⟨[1, 1, 2, 2], [0, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (-1, 15116544)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [0, 2, 1, 1]⟩, (1, 5038848)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 0, 1, 1]⟩, (1, 5038848)⟩,
    ⟨⟨[1, 1, 2, 2], [2, 1, 2, 1], [1, 1, 2, 2], [2, 2, 1, 1]⟩, (1, 22674816)⟩ ]

/-- CS-bounded unresolved configs of T[0,1]: (config, D_a, D_b, r). -/
def csRows01 : List (Config × Q × Q × Q) :=
  []

/-- Crude-bounded unresolved configs of T[0,1]. -/
def crudeRows01 : List Config :=
  [ ⟨[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [2, 2, 2, 2]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [1, 2, 2, 2], [0, 1, 1, 1]⟩,
    ⟨[0, 2, 2, 2], [2, 2, 2, 2], [0, 2, 2, 2], [1, 1, 1, 1]⟩,
    ⟨[1, 2, 2, 2], [1, 2, 2, 1], [1, 2, 2, 2], [2, 1, 1, 1]⟩,
    ⟨[2, 2, 2, 2], [0, 2, 2, 2], [2, 2, 2, 2], [1, 1, 1, 1]⟩,
    ⟨[2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2], [1, 1, 1, 1]⟩ ]

def tVal01 (a b : Nat) : Q :=
  qAdd (qSum (poly01.map (fun t => qMul t.2 (qPow a b t.1))))
       (qSum (addRows01.map (fun r =>
         qMul (qMulNat r.2 (wdOf r.1))
              (qPow a b (configExp r.1)))))

def uVal01 (a b : Nat) : Q :=
  qAdd (qSum (csRows01.map (fun r =>
         qMul (qMulNat (qMin r.2.2.2 (natQ (cnOf 0 1 r.1)))
                       (wdOf r.1))
              (qPow a b (configExp r.1)))))
       (qSum (crudeRows01.map (fun c =>
         qMul (natQ (wdOf c * cnOf 0 1 c))
              (qPow a b (configExp c)))))

/-- Every CS citation of T[0,1] is valid: r >= 0,
r^2 >= D_a * D_b, and both cited values are located in
`citedDiag` at a D4 image of the demanded key. -/
theorem cs_valid01 :
    csRows01.all (fun r =>
      qNonneg r.2.2.2
      && qLe (qMul r.2.1 r.2.2.1) (qSq r.2.2.2)
      && locates ⟨0, r.1.q, r.1.w, r.1.top⟩ r.2.1
      && locates ⟨1, r.1.q, r.1.w, r.1.bot⟩ r.2.2.1)
      = true := by decide

/-- lo/hi per entry: T -+ (U + tail). -/
def lo00 (a b : Nat) (tl : Q) : Q :=
  qSub (tVal00 a b) (qAdd (uVal00 a b) tl)
def hi01 (a b : Nat) (tl : Q) : Q :=
  qAdd (tVal01 a b) (qAdd (uVal01 a b) tl)
def lo01 (a b : Nat) (tl : Q) : Q :=
  qSub (tVal01 a b) (qAdd (uVal01 a b) tl)
def lo11 (a b : Nat) (tl : Q) : Q :=
  qSub (tVal11 a b) (qAdd (uVal11 a b) tl)

/-- One grid row: (a, b, tail00, tail11, tail01) for s = a/b;
tails are Lambda = 8 bounds rounded UP to 10^-60. -/
abbrev Row := Nat × Nat × Q × Q × Q

def posAt (g : Row) : Bool :=
  qPos (lo00 g.1 g.2.1 g.2.2.1)
  && qPos (lo11 g.1 g.2.1 g.2.2.2.1)
  && qPos (lo01 g.1 g.2.1 g.2.2.2.2)

def certAt (g : Row) : Bool :=
  posAt g
  && qLt (qSq (hi01 g.1 g.2.1 g.2.2.2.2))
         (qMul (lo11 g.1 g.2.1 g.2.2.2.1)
               (lo00 g.1 g.2.1 g.2.2.1))

/-- The ratio-certified grid: X_11 > 0 kernel-checked at each
s = a/b.  Certified X_11 lower bounds (float, for the reader):
    s = 1/2: X_11 >= +0.258392
    s = 11/20: X_11 >= +0.282612
    s = 9/16: X_11 >= +0.289793
    s = 4/7: X_11 >= +0.294655
    s = 3/5: X_11 >= +0.274282
    s = 61/100: X_11 >= +0.177639
    s = 8/13: X_11 >= +0.028179
-/
def certGrid : List Row :=
  [ (1, 2, (10675937976548279690562003523580883332616576714647, 1000000000000000000000000000000000000000000000000000000000000), (22676085403243198386734270159948439181576445057, 500000000000000000000000000000000000000000000000000000000000), (17158162744445177149997399153146620342300642401, 500000000000000000000000000000000000000000000000000000000000)),
    (11, 20, (7654658750600462032484407597148969622941183826439061, 500000000000000000000000000000000000000000000000000000000000), (218736694518274813301438448065845828597948626713497, 1000000000000000000000000000000000000000000000000000000000000), (740527924935707495895041801206802380459451013637, 12500000000000000000000000000000000000000000000000000000000)),
    (9, 16, (89810563759562645960585495960123871260664814193296679, 1000000000000000000000000000000000000000000000000000000000000), (424285487528062794450147854375482534436807719862299, 250000000000000000000000000000000000000000000000000000000000), (208293620684150111920379125829412303677113758159379, 500000000000000000000000000000000000000000000000000000000000)),
    (4, 7, (157207563678453125324463417394800149282719360741471049, 500000000000000000000000000000000000000000000000000000000000), (290226100160102406153486850241382982189732501707027, 40000000000000000000000000000000000000000000000000000000000), (858639182696065350253251018007450490859156211361697, 500000000000000000000000000000000000000000000000000000000000)),
    (3, 5, (4085156854548329128365770296470940215242138930477152723, 250000000000000000000000000000000000000000000000000000000000), (732746628023877024268435043928279848762375978155392759, 1000000000000000000000000000000000000000000000000000000000000), (175370062634771821591637524248648331308087966392086819, 1000000000000000000000000000000000000000000000000000000000000)),
    (61, 100, (3189371219061899512345474887052663557197694536715998389, 50000000000000000000000000000000000000000000000000000000000), (366531702311865271724482828182040106798821543522409487, 100000000000000000000000000000000000000000000000000000000000), (900407130813881933800576001494688548911689315533811639, 1000000000000000000000000000000000000000000000000000000000000)),
    (8, 13, (33056758244722116860046934629490501193699066676470705993, 250000000000000000000000000000000000000000000000000000000000), (544941136147907903792620156241266929254847274287686309, 62500000000000000000000000000000000000000000000000000000000), (2173501176636684478708855638956682471742016421782847643, 1000000000000000000000000000000000000000000000000000000000000)) ]

/-- The positivity-only grid (window positive; ratio open). -/
def posGrid : List Row :=
  [ (31, 50, (9855978609114127443972457562439167692861587356524521827, 40000000000000000000000000000000000000000000000000000000000), (286329148469805733449453842906600721334003521130024869, 15625000000000000000000000000000000000000000000000000000000), (2311906606993366815349391096878693057736236376583590337, 500000000000000000000000000000000000000000000000000000000000)),
    (5, 8, (60301718360415994785979361922383063903328380448691338603, 125000000000000000000000000000000000000000000000000000000000), (8194647231595859090106196204145704748033298591457849179, 200000000000000000000000000000000000000000000000000000000000), (5232682379975248276679124268627494774080311764776331633, 500000000000000000000000000000000000000000000000000000000000)) ]

theorem cert_grid_count : certGrid.length = 7 := by decide

theorem pos_grid_count : posGrid.length = 2 := by decide

theorem grid_tails_nonneg :
    (certGrid ++ posGrid).all (fun g =>
      qNonneg g.2.2.1 && qNonneg g.2.2.2.1 && qNonneg g.2.2.2.2)
      = true := by decide

/-- **The certified windows are positive** at every grid
point: T - U - tail > 0 entrywise. -/
theorem windows_positive :
    (certGrid ++ posGrid).all posAt = true := by decide

/-- **The X_11 ratio certificate**: lo11 * lo00 > hi01^2 at
every CERT grid point, i.e. the blocked one-step observable
X_11 = log(T11 T00 / T01^2) is strictly positive in the
M -> infinity limit — the SU(2) instrument reads a gap where
its U(1) mirror reads exactly 0 — now with the whole
assembly's arithmetic replayed by the Lean kernel. -/
theorem x11_ratio_certified :
    certGrid.all certAt = true := by decide

end WindowLedger
