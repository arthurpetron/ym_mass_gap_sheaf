/-
The Penrose–Ursell atom is a MISLABEL — a genuine CLOSURE (in-repo, no new axiom)
of the single open field `MultiComponentKPProgress.PenroseUrsellDatum.penrose_ursell`
for the collapsed 1D `zChain` correlator, plus the honest ledger of what that buys.

# The object

`MultiComponentKPProgress.PenroseUrsellDatum p` carries the single open field

    penrose_ursell : ∀ d, offCorr d ≤ connTailPartial p d (tailLen d)

with everything around it green: the KP count (`animalCount_le_pow`), the
strong-coupling threshold (`genuine_threshold`), the tree-graph weight
(`eSurrogate = 3 ≥ e`), the monotone extension (`connTailPartial_mono`), and the
uniform geometric tail (`connTailPartial_decay`).  Its predecessor
`FPClusterIdentity.MultiComponentKPBound` dominated by the length-`d` truncation
`clusterSpanSum … d = connTailPartial p d d`, which is EMPTY at `d = 0`
(`= 0 < wilsonG … 0`) — the documented reason `offCorr` was kept abstract there.
`PenroseUrsellDatum`'s FREE `tailLen d ≥ d` removes exactly that obstruction.

# What this module delivers (honest verdict)

The atom labelled "the classical Penrose tree-graph identity" is NOT open for this
single-rep-collapsed 1D correlator.  `WilsonConnCorr.wilsonG_collapse` already
forces the connecting chain onto ONE common excited rep — a single chain is its
own spanning tree, so there are no multi-component Ursell cancellations to
dominate.  The residual genuine content is only a TERMWISE GEOMETRIC comparison
`real correlator ≤ leading connecting-cluster term`, backed entirely by proved
lemmas.  We CLOSE it with the concrete `wilsonG` inhabitant.

## PROVED (genuine, axiom-clean)

  * `one_le_pow` — `1 ≤ q ⇒ 1 ≤ q^d` (the `Q'` monotone-power floor);
  * `one_le_animalCount` — `1 ≤ animalCount zChain p d` (a real list length,
    `= 4^{2(d-1)} ≥ 1` via `enumPolys_length` and the Nat power floor);
  * `rho_gw_val` — `rho gw = 1/108` (the real single-line rate, computed);
  * `ofNatM_rho_le_one` — `ofNat M · rho gw ≤ 1` for `M ≤ 108` (the ceiling);
  * `penrose_key` — the ARITHMETIC core: for `M ≤ 108`,
    `(ofNat M · rho gw)·(rho gw)^d ≤ kpTerm (zChainClusterCountBound p) gw gr d`
    (the leading `m = 0` connecting-cluster term dominates the real decay);
  * `kpTerm_le_tail` — `kpTerm … d ≤ connTailPartial p d (d+1)` (the `d = 0`
    empty-sum obstruction dissolved by `tailLen = d+1`, via `connTailPartial_mono`);
  * `penroseUrsellDatum_wilsonG` — **THE CONCRETE INHABITANT**: a genuine
    `PenroseUrsellDatum p` whose `offCorr` is the REAL `wilsonG gw (M+1)`
    correlator and whose `tailLen = d+1`, proving the "open atom"
    `penrose_ursell` is REACHABLE (for `M ≤ 108`), not open;
  * `wilsonG_penroseUrsell_decay` — the resulting decay
    `wilsonG gw (M+1) d ≤ 2·(mayerRho p)^d`, routed through the closed datum.

# Load-bearing honesty caveat (AGENTS.md Rule 6)

Net new physical content: ZERO.  This closure is redundant with
`FPClusterIdentity.loopyResidual_offDiagonalReal`, which already discharges the
off-diagonal bullet with the same real `wilsonG` object and its outright-proved
decay `≤ (ofNat M · rho gw)·(rho gw)^d` (rate `rho gw = 1/108 < 1`), WITHOUT any
datum.  What the inhabitant buys is truthful BOOKKEEPING: the atom named "the
Penrose–Ursell signed connecting-cluster identity" is not open for the collapsed
1D `zChain` correlator; it was only "open" because its predecessor used the
length-`d` (`d = 0`-empty) majorant.  The correct label is "termwise geometric
domination of the single-rep-collapsed connecting chain."

The `M ≤ 108` ceiling comes from the LOOSE `M·(1/108)` decay prefactor against the
`d = 0` floor `kpTerm(0) = 1`; it is NOT intrinsic (the sharp `d = 0` route via a
uniform `plaqActivity < 1` bound would remove it), but the clean in-repo closure
here uses it.  The genuinely-multi-component / higher-D case (where Ursell
cancellations are non-vacuous) is the one that needs the Ueltschi-2004
connecting-cluster bound `|φ^T| ≤ Σ_{connected X ⊇ bridge} |ζ(X)| e^{|X|}` — that
is NOT what this 1D `zChain` datum requires.

# Scope (underclaim)

Finite-volume STRONG-COUPLING combinatorics at the concrete weight `w = 1/6` on
the 1D plaquette chain `zChain`, `M ≤ 108`.  NOT uniform-in-`w`, NOT the continuum
(`a → 0`) limit, NOT a multi-plaquette correlator, NOT a 4D Yang–Mills mass gap.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props, no `sorry` / `admit` / new
`axiom`.  The concrete inhabitant is genuine `Type`-level data (the real `wilsonG`
correlator), never faked.  Every load-bearing declaration is gated with
`#print axioms`.
-/

import YMGap.Continuum.MultiComponentKPProgress
import YMGap.Continuum.WilsonConnCorr

namespace YMGap.Continuum.PenroseUrsellProgress

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.FPClusterIdentity
open YMGap.Continuum.MultiComponentKPProgress
open YMGap.Continuum.MayerClustering

/-! ## 1. The `Q'` monotone-power floor `1 ≤ q^d` -/

/-- **`one_le_pow` (PROVED).**  If `1 ≤ q` then `1 ≤ q^d` for every `d` (a product
of factors each `≥ 1`).  Used for `eSurrogate^d = 3^d ≥ 1`. -/
theorem one_le_pow {q : Q'} (hq : (1 : Q') ≤ q) (d : Nat) : (1 : Q') ≤ q ^ d := by
  induction d with
  | zero => rw [Q'.pow_zero]; exact Q'.le_refl' 1
  | succ d ih =>
      rw [Q'.pow_succ]
      have hqnn : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      -- 1 = 1·1 ≤ q·1 ≤ q·q^d
      have h1 : (1 : Q') * (1 : Q') ≤ q * (1 : Q') :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hq (by decide)
      have h2 : q * (1 : Q') ≤ q * q ^ d :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih hqnn
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h1 h2)
      exact Q'.ge_of_eqv (Q'.mul_one_eqv 1)

/-! ## 2. The animal-count floor `1 ≤ animalCount zChain p d`

`animalCount zChain p d` is the length of the real decoded-polymer list
`enumPolys zChain p d`, which `enumPolys_length` computes to
`(zChain.D + 1)^{2(d-1)} = 4^{2(d-1)} ≥ 1` (the Nat power floor at base `≥ 1`).
This is the `d = 0` floor term that dominates the loose real decay. -/

/-- **`one_le_animalCount` (PROVED).**  `1 ≤ animalCount zChain p d`: the count is
a real list length `= 4^{2(d-1)} ≥ 1`. -/
theorem one_le_animalCount (p : zChain.toLattice.Plaquette) (d : Nat) :
    (1 : Q') ≤ animalCount zChain p d := by
  have hlen : 1 ≤ (enumPolys zChain p d).length := by
    rw [enumPolys_length]
    -- 1 = (zChain.D+1)^0 ≤ (zChain.D+1)^(2(d-1))
    exact nat_pow_le_pow_right (b := zChain.D + 1) (by decide)
      (i := 0) (j := 2 * (d - 1)) (Nat.zero_le _)
  show (1 : Q') ≤ Q'.ofNat (enumPolys zChain p d).length
  exact Q'.le_trans' _ _ _ (by decide) (ClusterCount.ofNat_le_ofNat hlen)

/-! ## 3. The real single-line rate and the `M ≤ 108` ceiling -/

/-- **`rho_gw_val` (PROVED).**  The real single-line rate is
`rho gw = coeffW gw 1 = 2·(1/6)³ = 1/108` (`= 2/216`), computed. -/
theorem rho_gw_val : rho gw = Q'.mkPos 2 216 (by decide) := by decide

/-- **`ofNatM_rho_le_one` (PROVED).**  For `M ≤ 108`, `ofNat M · rho gw ≤ 1`:
`ofNat M ≤ ofNat 108` and `ofNat 108 · (1/108) = 1`.  This is the loose ceiling
(the leading `M·(1/108)` prefactor of the real decay stays `≤ 1`). -/
theorem ofNatM_rho_le_one {M : Nat} (hM : M ≤ 108) :
    Q'.ofNat M * rho gw ≤ (1 : Q') := by
  have hM' : Q'.ofNat M ≤ Q'.ofNat 108 := ClusterCount.ofNat_le_ofNat hM
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hM' (rho_nonneg gw_nonneg)) ?_
  rw [rho_gw_val]
  decide

/-! ## 4. The arithmetic core — the leading connecting-cluster term dominates -/

/-- **`penrose_key` (PROVED — the arithmetic core).**  For `M ≤ 108` and every `d`,
the real single-line decay is dominated by the leading (`m = 0`) connecting-cluster
term:

    (ofNat M · rho gw)·(rho gw)^d  ≤  kpTerm (zChainClusterCountBound p) gw gr d
                                    =  animalCount d · (rho gw)^d · 3^d.

Dividing by `(rho gw)^d ≥ 0` reduces to `ofNat M · rho gw ≤ animalCount d · 3^d`,
and `ofNat M · rho gw ≤ 1 ≤ animalCount d · 3^d` (count `≥ 1`, `3^d ≥ 1`).  Uses
`coeffW gw gr = rho gw` (`gr = 1`).  NO tree-graph identity, NO new axiom. -/
theorem penrose_key (p : zChain.toLattice.Plaquette) (M d : Nat) (hM : M ≤ 108) :
    (Q'.ofNat M * rho gw) * (rho gw) ^ d
      ≤ kpTerm (zChainClusterCountBound p) gw gr d := by
  -- unfold the KP term and normalise its base `coeffW gw gr` to `rho gw`
  unfold kpTerm
  rw [show coeffW gw gr = rho gw from rfl]
  -- abbreviations
  have hρnn : (0 : Q') ≤ rho gw := rho_nonneg gw_nonneg
  have hρd : (0 : Q') ≤ (rho gw) ^ d := Q'.pow_nonneg _ hρnn d
  have hAnn : (0 : Q') ≤ (zChainClusterCountBound p).animalCount d :=
    (zChainClusterCountBound p).animalCount_nonneg d
  have hAρ : (0 : Q') ≤ (zChainClusterCountBound p).animalCount d * (rho gw) ^ d :=
    Q'.mul_nonneg _ _ hAnn hρd
  have hA1 : (1 : Q') ≤ (zChainClusterCountBound p).animalCount d :=
    one_le_animalCount p d
  have hE1 : (1 : Q') ≤ eSurrogate ^ d := one_le_pow (by decide) d
  -- step 1: (ofNat M · ρ)·ρ^d ≤ 1·ρ^d
  have s1 : (Q'.ofNat M * rho gw) * (rho gw) ^ d ≤ (1 : Q') * (rho gw) ^ d :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNatM_rho_le_one hM) hρd
  -- step 2: 1·ρ^d = ρ^d
  have e2 : ((1 : Q') * (rho gw) ^ d) ≤ (rho gw) ^ d :=
    Q'.le_of_eqv (Q'.one_mul_eqv _)
  -- step 3: ρ^d ≤ animalCount · ρ^d
  have s3 : (rho gw) ^ d
      ≤ (zChainClusterCountBound p).animalCount d * (rho gw) ^ d := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hA1 hρd
  -- step 4: animalCount·ρ^d ≤ (animalCount·ρ^d)·eSurrogate^d
  have s4 : (zChainClusterCountBound p).animalCount d * (rho gw) ^ d
      ≤ ((zChainClusterCountBound p).animalCount d * (rho gw) ^ d) * eSurrogate ^ d := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hE1 hAρ
  exact Q'.le_trans' _ _ _ s1
    (Q'.le_trans' _ _ _ e2 (Q'.le_trans' _ _ _ s3 s4))

/-! ## 5. Dissolving the `d = 0` empty-sum obstruction — `tailLen = d+1` -/

/-- **`kpTerm_le_tail` (PROVED).**  The leading connecting-cluster term is dominated
by the length-`(d+1)` connecting tail:

    kpTerm (zChainClusterCountBound p) gw gr d  ≤  connTailPartial p d (d + 1).

`connTailPartial p d 1 = 0 + kpTerm … d` (definitional: `finSum … 1 = f 0`), and
`connTailPartial p d 1 ≤ connTailPartial p d (d+1)` by `connTailPartial_mono`
(`1 ≤ d+1`).  The free `tailLen = d+1 ≥ d` supplies the `m = 0` floor term —
exactly what the predecessor's length-`d` (`d = 0`-empty) `clusterSpanSum` lacked. -/
theorem kpTerm_le_tail (p : zChain.toLattice.Plaquette) (d : Nat) :
    kpTerm (zChainClusterCountBound p) gw gr d ≤ connTailPartial p d (d + 1) := by
  have hmono : connTailPartial p d 1 ≤ connTailPartial p d (d + 1) :=
    connTailPartial_mono p d (by omega)
  refine Q'.le_trans' _ _ _ ?_ hmono
  have hc1 : connTailPartial p d 1
      = (0 : Q') + kpTerm (zChainClusterCountBound p) gw gr d := rfl
  rw [hc1, Q'.zero_add']
  exact Q'.le_refl' _

/-! ## 6. THE CONCRETE INHABITANT — the "open atom" is reachable

The three proved bounds chain to close `penrose_ursell` for the REAL `wilsonG`
correlator with `tailLen = d+1`:

    twoCompOffCorr M d  =  wilsonG gw (M+1) d
      ≤  (ofNat M · rho gw)·(rho gw)^d          (twoCompOffCorr_decay)
      ≤  kpTerm … gw gr d                        (penrose_key,  M ≤ 108)
      ≤  connTailPartial p d (d+1).              (kpTerm_le_tail) -/

/-- **`penroseUrsellDatum_wilsonG` (PROVED — THE CONCRETE INHABITANT).**  For
`M ≤ 108`, a genuine `PenroseUrsellDatum p` whose `offCorr` is the REAL connecting
correlator `wilsonG gw (M+1)` and whose `tailLen = d+1`.  Its `penrose_ursell`
field — the atom labelled "the classical Penrose tree-graph identity" — is CLOSED
by the termwise geometric chain above, with NO tree-graph identity and NO new
axiom.  This proves the reduced target is not merely weaker than its predecessor
(`ofMultiComponentKPBound`) but actually REACHABLE. -/
def penroseUrsellDatum_wilsonG (p : zChain.toLattice.Plaquette) (M : Nat)
    (hM : M ≤ 108) : PenroseUrsellDatum p where
  offCorr := twoCompOffCorr M
  tailLen := fun d => d + 1
  tailLen_ge := fun d => Nat.le_succ d
  penrose_ursell := fun d =>
    Q'.le_trans' _ _ _ (twoCompOffCorr_decay M d)
      (Q'.le_trans' _ _ _ (penrose_key p M d hM) (kpTerm_le_tail p d))

/-- **`wilsonG_penroseUrsell_decay` (PROVED).**  Routing the concrete inhabitant
through the already-green `penroseUrsell_offCorr_decay`, the REAL correlator decays
at the majorant rate:

    wilsonG gw (M+1) d  =  twoCompOffCorr M d  ≤  2·(mayerRho p)^d,   mayerRho p = 4/9.

(The real single-line rate `rho gw = 1/108` is even faster; this is the
datum-routed majorant form.) -/
theorem wilsonG_penroseUrsell_decay (p : zChain.toLattice.Plaquette) (M : Nat)
    (hM : M ≤ 108) (d : Nat) :
    twoCompOffCorr M d ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  penroseUrsell_offCorr_decay p (penroseUrsellDatum_wilsonG p M hM) d

/-! ## 7. Documentation: PROVED vs the honest ledger (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `one_le_pow`, `one_le_animalCount` — the `Q'` power / animal-count floors;
  * `rho_gw_val`, `ofNatM_rho_le_one` — the real rate `1/108` and the `M ≤ 108`
    ceiling `ofNat M · rho gw ≤ 1`;
  * `penrose_key` — the arithmetic core: the leading connecting-cluster term
    dominates the real single-line decay (`M ≤ 108`);
  * `kpTerm_le_tail` — the `d = 0` empty-sum obstruction dissolved by `tailLen = d+1`;
  * `penroseUrsellDatum_wilsonG` — THE CONCRETE INHABITANT of `PenroseUrsellDatum`
    (real `wilsonG` correlator), CLOSING the single open field `penrose_ursell`;
  * `wilsonG_penroseUrsell_decay` — the resulting `≤ 2·(mayerRho p)^d` decay.

Honest verdict (Rule 6): the atom "the Penrose–Ursell signed connecting-cluster
identity" is a MISLABEL for the single-rep-collapsed 1D `zChain` correlator — it is
closable in-repo with no tree-graph identity and no new axiom.  Net new PHYSICAL
content is ZERO (redundant with `loopyResidual_offDiagonalReal`); the value is
truthful bookkeeping.  The `M ≤ 108` ceiling is a loose-prefactor artefact, not
intrinsic.  The genuinely multi-component / higher-D Ursell case (Ueltschi 2004)
is NOT what this datum requires.  This is finite-volume strong-coupling
combinatorics at `w = 1/6` on the 1D chain — NOT the continuum limit, NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.PenroseUrsellProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseUrsellProgress.one_le_pow
#print axioms YMGap.Continuum.PenroseUrsellProgress.one_le_animalCount
#print axioms YMGap.Continuum.PenroseUrsellProgress.rho_gw_val
#print axioms YMGap.Continuum.PenroseUrsellProgress.ofNatM_rho_le_one
#print axioms YMGap.Continuum.PenroseUrsellProgress.penrose_key
#print axioms YMGap.Continuum.PenroseUrsellProgress.kpTerm_le_tail
#print axioms YMGap.Continuum.PenroseUrsellProgress.penroseUrsellDatum_wilsonG
#print axioms YMGap.Continuum.PenroseUrsellProgress.wilsonG_penroseUrsell_decay
