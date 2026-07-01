/-
# The divided-difference → Lipschitz bridge and the cos-node residual bundle
# (`CosNodeBracket` — reducing the four `RootEnclosurePoly` fields)

`RootEnclosureGen.RootEnclosurePoly k` carries FOUR honest fields feeding the
general-`M` off-diagonal OS2 Gram positivity via a POLYNOMIAL `T`-branch budget
`(k+2)²`:

  * `loSign` / `hiSign` — the rational-`π` `U`-sign facts (the `cos`-bridge wall);
  * `lipTpoly` — the polynomial Markov `T`-secant `LipBound (T_{k+2}) lo hi
    (ofNat ((k+2)²))`;
  * `tsign` — the co-located `T`-sign certificate against the polynomial budget.

This module isolates the *self-contained, π-free* structural core of the
`lipTpoly` field — the **divided-difference (variation-of-parameters) route** —
as a clean, reusable bridge, and repackages the whole residual so that the
`lipTpoly` `LipBound` is REPLACED by the strictly more primitive
**divided-difference witness** `DDBound`.

## The decisive move (part (a) of the plan, its step 3, PROVED)

The polynomial Markov constant `(k+2)²` is unreachable from the `QB_all`
majorant engine (`LocatedBracketGen.lipBound_T_of_QB` yields only the EXPONENTIAL
`Amaj(k+2)+Amaj k`), because bounding the two `U`-secants apart loses the Markov
cancellation.  The sharp constant comes from the exact divided-difference
identity `T_n(b) − T_n(a) = (b−a)·B_n(a,b)` together with the two-sided
term-by-term bound `−C ≤ B_n ≤ C`.  This module proves, ONCE AND FOR ALL, that

    a divided-difference witness `DDBound f lo hi C`  ⟹  `LipBound f lo hi C`.

That is exactly the read-off (via `b − a ≥ 0`) of both `LipBound` directions from
the two-sided divided-difference bound — the honest, reusable content of the
Markov secant.  It removes the `LipBound` obligation and leaves in its place the
sharper, structural `DDBound` obligation (the DD identity + the closed
convolution `B_n` bound), which hits the hardcoded `(k+2)²` exactly.

## What is PROVED here (axiom-clean)

  * `DDBound f lo hi C` — the `Type`-level divided-difference witness: a secant
    field `B : Q' → Q' → Q'`, the identity `f b − f a ≈ (b−a)·B a b`, and the
    two-sided `−C ≤ B a b ≤ C` on the subbox.
  * `lipBound_of_ddBound` — **the bridge**: `DDBound f lo hi C → LipBound f lo hi
    C`, both directions read off with `b − a ≥ 0`.  Genuine reusable lemma.
  * `ddBound_mono` — a `DDBound` constant may be enlarged (`C ≤ C'`), the analogue
    of `RootEnclosureGen.LipBound_mono` at the DD level.
  * `rootEnclosurePoly_of_residual` — the assembly: from a `CosNodeResidual k`
    (interval bounds + the DD Markov witness + the three sign facts) build a
    `RootEnclosureGen.RootEnclosurePoly k`, discharging `lipTpoly` through the
    bridge.
  * `deMoivreNode_of_residual` — hence a fully inhabited `DeMoivreNode (k+1)`
    (general-`M` off-diagonal OS2 Gram positivity downstream), conditional ONLY
    on the `CosNodeResidual` walls.

## The honest residual (NOT closed here)

`CosNodeResidual k` carries as `Type`-level data the DD Markov witness `dd`
(supplying `lipTpoly` via the bridge — this is the part-(a) reframing: the sharp
quadratic secant identity + closed `B_n` bound) together with the three genuine
rational-`π` walls `loSign` / `hiSign` / `tsign`.  Neither the DD witness nor the
`π`-sign facts are constructed here; the module proves the *bridge* and the *full
assembly*, so the four `RootEnclosurePoly` fields are reduced to (DD Markov
witness) + (the three sign facts), with all glue proved and axiom-clean.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  `DDBound` /
`CosNodeResidual` are `Type`-level records (witnesses as data, not `Prop`-∃).
-/

import YMGap.Continuum.RootEnclosureGen

namespace YMGap.Continuum.CosNodeBracket

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebRoot

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The divided-difference witness -/

/-- **The divided-difference (secant) witness** for `f` on `[lo,hi]` with
two-sided constant `C ≥ 0`.  `B a b` is the exact divided difference
`(f b − f a)/(b − a)` presented as a `Q'`-polynomial datum; `ddId` is the exact
identity `f b − f a ≈ (b − a)·B a b`; `Bub`/`Blb` are the two-sided
term-by-term bound `−C ≤ B a b ≤ C`.  This is strictly more primitive than a
`LipBound`: the sharp Markov constant lives in `B`'s closed convolution form, and
the `LipBound` is read off (below) purely by `b − a ≥ 0`. -/
structure DDBound (f : Q' → Q') (lo hi C : Q') where
  /-- The divided difference `B a b = (f b − f a)/(b − a)` as a `Q'` datum. -/
  B : Q' → Q' → Q'
  /-- The constant is nonnegative. -/
  Cnn : (0 : Q') ≤ C
  /-- The exact divided-difference identity `f b − f a ≈ (b − a)·B a b`. -/
  ddId : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi → f b + -(f a) ≈ (b + -a) * B a b
  /-- Upper term-by-term bound `B a b ≤ C`. -/
  Bub : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi → B a b ≤ C
  /-- Lower term-by-term bound `−C ≤ B a b`. -/
  Blb : ∀ a b : Q', lo ≤ a → a ≤ b → b ≤ hi → -C ≤ B a b

/-! ## 2. The bridge `DDBound → LipBound` (the honest reusable core) -/

/-- **The divided-difference → Lipschitz bridge.**  From a `DDBound f lo hi C`,
build a `LipBound f lo hi C`.  Both directions are read off from the exact
identity `f b − f a ≈ (b − a)·B a b` together with `b − a ≥ 0`:

* `bound`  : `f b − f a ≈ (b−a)·B ≤ (b−a)·C ≈ C·(b−a)`  (using `B ≤ C`);
* `bound'` : `f a − f b ≈ (b−a)·(−B) ≤ (b−a)·C ≈ C·(b−a)`  (using `−B ≤ C`).

This is the sole place the polynomial Markov constant becomes a genuine
`LipBound`; the sharpness is carried entirely inside `B`. -/
theorem lipBound_of_ddBound (f : Q' → Q') (lo hi C : Q') (d : DDBound f lo hi C) :
    LipBound f lo hi C where
  nonneg := d.Cnn
  bound := by
    intro a b ha hab hb
    have hnn : (0 : Q') ≤ b + -a := LocatedBracketGen.sub_nonneg a b hab
    -- f b − f a ≈ (b−a)·B a b
    have hId : f b + -(f a) ≈ (b + -a) * d.B a b := d.ddId a b ha hab hb
    -- (b−a)·B ≤ (b−a)·C
    have hmul : (b + -a) * d.B a b ≤ (b + -a) * C :=
      Q'.mul_le_mul_of_nonneg_left (d.B a b) C (b + -a) (d.Bub a b ha hab hb) hnn
    -- (b−a)·C ≈ C·(b−a)
    have hcomm : (b + -a) * C ≈ C * (b + -a) := Q'.mul_comm_eqv (b + -a) C
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hId)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcomm))
  bound' := by
    intro a b ha hab hb
    have hnn : (0 : Q') ≤ b + -a := LocatedBracketGen.sub_nonneg a b hab
    have hId : f b + -(f a) ≈ (b + -a) * d.B a b := d.ddId a b ha hab hb
    -- f a − f b ≈ (b−a)·(−B a b)
    have hflipR : -(f b + -(f a)) ≈ f a + -(f b) :=
      Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (f b) (-(f a)))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (-(f b)) (-(-(f a))) (f a) (Q'.neg_neg_eqv (f a)))
          (Q'.add_comm_eqv (-(f b)) (f a)))
    have heqv : f a + -(f b) ≈ (b + -a) * (-(d.B a b)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hflipR)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hId)
          (Q'.eqv_symm (Q'.mul_neg_eqv (b + -a) (d.B a b))))
    -- −B ≤ C  from  −C ≤ B
    have hnegB : -(d.B a b) ≤ C :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (d.Blb a b ha hab hb))
        (Q'.le_of_eqv (Q'.neg_neg_eqv C))
    have hmul : (b + -a) * (-(d.B a b)) ≤ (b + -a) * C :=
      Q'.mul_le_mul_of_nonneg_left (-(d.B a b)) C (b + -a) hnegB hnn
    have hcomm : (b + -a) * C ≈ C * (b + -a) := Q'.mul_comm_eqv (b + -a) C
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcomm))

/-! ## 3. Monotonicity of the DD constant (DD-level analogue of `LipBound_mono`) -/

/-- **A `DDBound` constant may be enlarged.**  From `C ≤ C'` and `DDBound f lo hi
C` conclude `DDBound f lo hi C'` (same secant field, the two-sided bounds widen).
The DD-level analogue of `RootEnclosureGen.LipBound_mono`. -/
def ddBound_mono {f : Q' → Q'} {lo hi C C' : Q'} (hCC : C ≤ C')
    (d : DDBound f lo hi C) : DDBound f lo hi C' where
  B := d.B
  Cnn := Q'.le_trans' _ _ _ d.Cnn hCC
  ddId := d.ddId
  Bub := by
    intro a b ha hab hb
    exact Q'.le_trans' _ _ _ (d.Bub a b ha hab hb) hCC
  Blb := by
    intro a b ha hab hb
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hCC) (d.Blb a b ha hab hb)

/-! ## 4. The cos-node residual bundle and the assembly -/

/-- **The cos-node residual.**  Everything the polynomial-budget root enclosure
needs, with the `lipTpoly` `LipBound` replaced by the strictly more primitive
divided-difference Markov witness `dd`:

* `hlo1`/`hhi1`/`hle` — the interval bounds `−1 ≤ lo ≤ hi ≤ 1`;
* `dd` — the DD Markov witness `DDBound (T_{k+2}) lo hi (ofNat ((k+2)²))`; through
  the bridge this supplies `lipTpoly`.  This is the part-(a) reframing: the sharp
  quadratic secant identity + closed `B_n` bound, hitting `(k+2)²` exactly;
* `loSign`/`hiSign`/`tsign` — the three genuine rational-`π` walls (unchanged). -/
structure CosNodeResidual (k : Nat) where
  /-- Rational left endpoint. -/
  lo : Q'
  /-- Rational right endpoint. -/
  hi : Q'
  /-- `−1 ≤ lo`. -/
  hlo1 : (-1 : Q') ≤ lo
  /-- `hi ≤ 1`. -/
  hhi1 : hi ≤ (1 : Q')
  /-- `lo ≤ hi`. -/
  hle : lo ≤ hi
  /-- The polynomial Markov divided-difference witness (supplies `lipTpoly`). -/
  dd : DDBound (Cheb.T (k + 2)) lo hi (Q'.ofNat ((k + 2) ^ 2))
  /-- `U_{k+1}(lo) ≤ 0` (left sign, the rational-`π` fact). -/
  loSign : Ueval (k + 1) lo ≤ (0 : Q')
  /-- `0 ≤ U_{k+1}(hi)` (right sign, the rational-`π` fact). -/
  hiSign : (0 : Q') ≤ Ueval (k + 1) hi
  /-- The co-located `T`-sign certificate against the polynomial budget. -/
  tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')

/-- **The assembly.**  From a `CosNodeResidual k` build the polynomial-budget root
enclosure `RootEnclosureGen.RootEnclosurePoly k`, discharging the `lipTpoly`
field through the divided-difference bridge `lipBound_of_ddBound`. -/
def rootEnclosurePoly_of_residual (k : Nat) (r : CosNodeResidual k) :
    RootEnclosureGen.RootEnclosurePoly k where
  lo := r.lo
  hi := r.hi
  hlo1 := r.hlo1
  hhi1 := r.hhi1
  hle := r.hle
  loSign := r.loSign
  hiSign := r.hiSign
  lipTpoly :=
    lipBound_of_ddBound (Cheb.T (k + 2)) r.lo r.hi (Q'.ofNat ((k + 2) ^ 2)) r.dd
  tsign := r.tsign

/-- A fully inhabited de Moivre node from the cos-node residual (branch collapse
and the `lipU` field already proved upstream), hence general-`M` off-diagonal
OS2 Gram positivity downstream — conditional ONLY on the `CosNodeResidual`
walls. -/
def deMoivreNode_of_residual (k : Nat) (r : CosNodeResidual k) :
    ChebRotationPair.DeMoivreNode (k + 1) :=
  RootEnclosureGen.deMoivreNodePoly k (rootEnclosurePoly_of_residual k r)

end YMGap.Continuum.CosNodeBracket

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CosNodeBracket.lipBound_of_ddBound
#print axioms YMGap.Continuum.CosNodeBracket.ddBound_mono
#print axioms YMGap.Continuum.CosNodeBracket.rootEnclosurePoly_of_residual
#print axioms YMGap.Continuum.CosNodeBracket.deMoivreNode_of_residual
