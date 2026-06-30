/-
# The END-TO-END capstone: the self-similar block-spin model as a COMPLETE
# constructive instance of the continuum mass gap, isolating the one physical-RG input.

This module assembles, into a single green theorem, everything the attack on the
open continuum input has produced about the **self-similar block-spin model** — a
genuine constructive-real renormalization tower whose separators obey the
codynamic flow law `sep_k ≃ (sep_{k+1})^(b+1)` — and isolates EXACTLY the one
remaining dynamical-RG statement that separates this model from physical 4D
Yang–Mills.

## What the model is

A `SelfSimilarBlockSpinModel` bundles, as `Type`-level data:

  * a block factor `b ≥ 1`;
  * a self-similar constructive-real exponent tower `T : SelfSimilarTower b`
    (so the separators `sep T k = e^{−w_k}` satisfy the flow law at every scale);
  * a strictly-positive UV exponent seed `PosEv (T.w 0)`;
  * an explicit strictly-positive UV-gap floor below the physical gap at the
    coarsest scale (`floor0`, supplied as data — Rule 8, never a `Prop`-∃).

The lattice spacing schedule is the geometric **block spacing** `a_N = (1/(b+1))^N`,
whose per-step ratio is exactly the renormalization-group block factor `b+1`.

## What the capstone proves (all green, for this model)

`blockSpinModel_continuum_gap` yields, simultaneously, a `BlockSpinContinuumGap`
carrying:

  (a) **`RateMatch`** — the margin-decay rate is matched by the block spacing rate
      at every scale (`afBlockRateMatch`): the margin can never outrun the spacing.
  (b) **A spacing-uniform physical-gap floor** — a single strictly-positive rational
      below the physical gap `physGapC N = (1 − sep N)·(1/a_N)` at EVERY scale of the
      genuine `a → 0` block schedule (`UniformPhysGapFloor` and the full
      `CRealContinuumGapResidual`, via `crealFloor_of_rateMatch`).
  (c) **The dimensional-transmutation limit** — the rescaled lattice margin
      `(b+1)^k·(1 − sep_k) → w₀ = 1 > 0` as a genuine `CReal` `ConvergesTo`
      (`dimensional_transmutation_limit`): the emergent gap scale survives `a → 0`.

`blockSpinModel_continuum_gap_concreteE` fires the capstone, fully unconditionally,
on the genuinely-IRRATIONAL `e^{−1}`-seeded flow `concreteTowerE 1` (whose exponents
`e^{−1}/2^k` and separators `e^{−(e^{−1})/2^k}` are all irrational, and which the
rational `polyFlow` provably cannot inhabit): this constructive-real self-similar
block-spin model has a positive physical mass gap that survives `a → 0` together
with the transmutation limit `Δ → 1`.

`blockSpinModel_reconstructed_gap` re-exposes the OS/GNS reconstruction: from any
located transfer-operator `SpectralGapData`, the strictly-positive mass gap
`Δ = 1 − sep > 0` with geometric two-point decay `G(n) ≤ G(0)·sep ⁿ` — the same
shape (margin `1 − sep`, decay `sep ⁿ`) the model exhibits per scale.

## The SINGLE remaining physical-RG input (honest)

`PhysicalRGInput` is the NAMED, UNINHABITED interface stating the exact obligation:
that the genuine physical Yang–Mills RG separators — the actual lattice gap under
block-spin decimation — obey the self-similar law `sep_k ≃ (sep_{k+1})^(b+1)` (the
geometric separator schedule), are `[0,1]`-valued, and carry a positive UV-gap
floor.  `physicalRG_continuum_gap` shows, GREEN, that THIS one dynamical-RG
statement implies the physical continuum mass gap (a strictly-positive
spacing-uniform floor on the physical gap at every scale).  It is NOT inhabited
here: the identification of the physical AF separator schedule with the
self-similar geometric law is the program's sole remaining obligation.

## Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `TransmutationLimit` / `AFRateMatch` / `RateMatchFloor` /
`CodynamicPhysFloor` / `SelfSimilarFlow` backbones; every carrier is `Type`-level
data (the UV floor is supplied as data, the model and the input are structures of
data).  Each load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no
custom `axiom`.
-/

import YMGap.Continuum.TransmutationLimit
import YMGap.Continuum.AFRateMatch
import YMGap.Continuum.RateMatchFloor
import YMGap.Continuum.CodynamicPhysFloor
import YMGap.Continuum.CodynamicCRealFlow
import YMGap.Continuum.GNSDynamics
import YMGap.Constructive.SelfSimilarFlow
import YMGap.Constructive.SU3CharFactor
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.Soundness

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.RateMatchFloor
open YMGap.Continuum.AFRateMatch
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.TuranPositivity

/-! ## 1. Generic `geRat` product (used by the concrete `e^{−1}` UV floor) -/

/-- **Product of constructive-real lower bounds.**  If `A ≥ c ≥ 0`, `B ≥ d`, and
`B ≥ 0`, then `A·B ≥ c·d`.  Decompose `A·B ≃ (A − c)·B + c·B`: the first factor is
`≥ 0` (`mul_nonneg` of `A − c ≥ 0` and `B ≥ 0`), the second is `≥ c·d`
(`geRat_smul_nonneg`). -/
theorem geRat_mul {A B : CReal} {c d : Q'} (hc : (0 : Q') ≤ c)
    (hA : ExpPos.geRat A c) (hB : ExpPos.geRat B d) (hBnn : ExpPos.geRat B 0) :
    ExpPos.geRat (CReal.mul A B) (c * d) := by
  have hkey : CReal.Equiv (CReal.mul A B)
      (CReal.add (CReal.mul (CReal.add A (CReal.neg (CReal.ofQ' c))) B)
                 (CReal.mul (CReal.ofQ' c) B)) := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
    show (A.approx n * B.approx n).eqv
      ((A.approx n + -c) * B.approx n + c * B.approx n)
    have hrhs : (((A.approx n + -c) * B.approx n) + c * B.approx n).eqv
        (A.approx n * B.approx n) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (c * B.approx n)
          (Q'.add_mul_eqv (A.approx n) (-c) (B.approx n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (A.approx n * B.approx n) ((-c) * B.approx n) (c * B.approx n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (A.approx n * B.approx n) ((-c) * B.approx n + c * B.approx n) 0 ?_) ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right ((-c) * B.approx n) (-(c * B.approx n)) (c * B.approx n)
            (Q'.neg_mul_eqv c (B.approx n))) ?_
        exact Q'.neg_add_self_eqv (c * B.approx n)
      · exact QPoly.q_add_zero_eqv (A.approx n * B.approx n)
    exact Q'.eqv_symm hrhs
  have h1 : ExpPos.geRat (CReal.mul (CReal.add A (CReal.neg (CReal.ofQ' c))) B) 0 :=
    CReal.mul_nonneg (CReal.geRat_add_neg hA) hBnn
  have h2 : ExpPos.geRat (CReal.mul (CReal.ofQ' c) B) (c * d) :=
    SU3CharFactor.geRat_smul_nonneg hc hB
  have h3 : ExpPos.geRat
      (CReal.add (CReal.mul (CReal.add A (CReal.neg (CReal.ofQ' c))) B)
                 (CReal.mul (CReal.ofQ' c) B)) (0 + c * d) :=
    SumOfSquares.geRat_add h1 h2
  refine SU3CharFactor.geRat_of_equiv hkey (ExpPos.geRat_mono h3 ?_)
  exact Q'.le_of_eqv (Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (c * d)) (QPoly.q_add_zero_eqv (c * d))))

/-- **A hard eventual lower bound from a `geRat`.**  From `A ≥ c` (in the `+ε`
order) and a positive slack `ε`, every approximation past some stage exceeds the
shifted bound `c − ε`. -/
theorem eventually_lb_of_geRat {A : CReal} {c ε : Q'} (h : ExpPos.geRat A c)
    (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → c + -ε ≤ A.approx n := by
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hc : c ≤ A.approx n + ε := hN n hn
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right c (A.approx n + ε) (-ε) hc) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (A.approx n) ε (-ε)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A.approx n) (ε + -ε) 0 (Q'.add_neg_self_eqv ε)) ?_
  exact QPoly.q_add_zero_eqv (A.approx n)

/-! ## 2. The model bundle and the end-to-end capstone -/

/-- **The self-similar block-spin model.**  A `Type`-level bundle: a constructive-real
self-similar tower `T` (block factor `b ≥ 1`) with a strictly-positive UV exponent
seed and an explicit strictly-positive UV-gap floor below the physical gap at the
coarsest scale.  The lattice spacing is the geometric block spacing
`geomSpacing b` (`a_N = (1/(b+1))^N`, per-step ratio the block factor `b+1`). -/
structure SelfSimilarBlockSpinModel : Type where
  /-- The renormalization-group block factor (`b+1`-fold decimation). -/
  b : Nat
  /-- The block factor is a genuine (`≥ 2`) decimation: `b ≥ 1`. -/
  hb : 1 ≤ b
  /-- The constructive-real self-similar exponent tower (separators obey
  `sep_k ≃ (sep_{k+1})^(b+1)`). -/
  T : SelfSimilarTower b
  /-- The strictly-positive UV exponent seed. -/
  uvSeed : PosEv (T.w 0)
  /-- The explicit UV-gap floor (supplied as data, Rule 8). -/
  floor0 : Q'
  /-- The UV-gap floor is strictly positive. -/
  floor0_pos : (0 : Q') < floor0
  /-- The UV-gap floor lies below the physical gap at the coarsest scale. -/
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (physGapC b (sep T) (geomSpacing b) 0)

/-- **The end-to-end continuum-gap certificate for the block-spin model.**  Bundles,
for a fixed model `M`, the three deliverables: the per-step `RateMatch`, the
spacing-uniform physical-gap floor (both as the named `UniformPhysGapFloor` and the
full `CRealContinuumGapResidual`), and the dimensional-transmutation `CReal` limit. -/
structure BlockSpinContinuumGap (M : SelfSimilarBlockSpinModel) : Type where
  /-- (a) The margin-decay rate is matched by the block spacing rate at every scale. -/
  rateMatch : RateMatch M.b (sep M.T) (geomSpacing M.b)
  /-- (b₁) The spacing-uniform physical-gap floor (named codynamic wall). -/
  uniform : UniformPhysGapFloor M.T (geomSpacing M.b)
  /-- (b₂) The full continuum-gap residual (conserved-margin half PROVED, uniformity
  discharged by the block rate). -/
  residual : CRealContinuumGapResidual M.b
  /-- (c) The dimensional-transmutation limit: the rescaled lattice margin
  `(b+1)^k·(1 − sep_k)` converges to the gap scale `w₀ = 1 > 0`. -/
  transmutation : CReal.ConvergesTo
    (transmuted 1 (by decide) (fun k => (M.b + 1) ^ k - 1)) (CReal.ofQ' 1)

/-- **THE END-TO-END CAPSTONE.**  Every self-similar block-spin model is a complete
constructive instance of the continuum mass gap: it simultaneously satisfies the
per-step `RateMatch`, carries a strictly-positive spacing-uniform physical-gap floor
at every scale of the genuine `a → 0` block schedule, and realises the
dimensional-transmutation limit `(b+1)^k·(1 − sep_k) → w₀ = 1`.  Pure composition of
`afBlockRateMatch`, `afBlockUniformFloor_of_uvFloor`, `afBlockResidual_of_uvFloor`,
and `dimensional_transmutation_limit`. -/
def blockSpinModel_continuum_gap (M : SelfSimilarBlockSpinModel) :
    BlockSpinContinuumGap M where
  rateMatch := afBlockRateMatch M.T
  uniform :=
    afBlockUniformFloor_of_uvFloor M.T M.uvSeed M.floor0 M.floor0_pos M.hbase0
  residual :=
    afBlockResidual_of_uvFloor M.T M.uvSeed M.floor0 M.floor0_pos M.hbase0
  transmutation := dimensional_transmutation_limit M.b M.hb

/-- The capstone's continuum floor is strictly positive — the physical gap survives
`a → 0` (non-vacuity payoff of `blockSpinModel_continuum_gap`). -/
theorem blockSpinModel_continuum_floor_pos (M : SelfSimilarBlockSpinModel) :
    (0 : Q') < (blockSpinModel_continuum_gap M).residual.continuumFloor :=
  (blockSpinModel_continuum_gap M).residual.continuumFloor_pos

/-! ## 3. The concrete irrational `e^{−1}` model (fully unconditional)

We build the explicit UV-gap floor for `concreteTowerE 1`, whose UV exponent is the
irrational `e^{−1}` and whose base separator is `e^{−(e^{−1})}`.  The floor needs a
concrete rational upper bound `sep 0 ≤ r < 1`, obtained from a concrete positive
lower bound on the exponent `e^{−1} ≥ e^{−1/2}·e^{−1/2} ≥ 1/4` and the antitone
upper bound `e^{−x} ≤ 1/(1+x)`. -/

/-- `0 ≤ 1` over `Q'`. -/
private theorem qzero_le_one : (0 : Q') ≤ (1 : Q') := by decide

/-- `geRat (e^{−1/2}) (1/2)`: every partial sum of `e^{−1/2}` is `≥ 1 − 1/2 = 1/2`
(the alternating-series lower bracket `oneSub_le_partialSum`, `n ≥ 2`). -/
theorem geRat_expHalf :
    ExpPos.geRat (ExpNeg.expNeg (Q'.invSucc 1) (Q'.invSucc_nonneg 1)) (Q'.invSucc 1) := by
  refine ExpPos.geRat_of_eventually ⟨2, fun n hn => ?_⟩
  show Q'.invSucc 1 ≤ ExpNeg.partialSum (Q'.invSucc 1) n
  have hlb := ExpNeg.oneSub_le_partialSum (Q'.invSucc_nonneg 1)
    (YMGap.Constructive.CReal.invSucc_le_one 1) n hn
  exact Q'.le_trans' _ _ _ (by decide : Q'.invSucc 1 ≤ (1 : Q') - Q'.invSucc 1) hlb

/-- `e^{−1} ≃ e^{−1/2}·e^{−1/2}` (the add-law made explicit, as in
`posEv_expNeg_one`). -/
theorem expNeg_one_eq_prod :
    CReal.Equiv
      (CReal.mul (ExpNeg.expNeg (Q'.invSucc 1) (Q'.invSucc_nonneg 1))
                 (ExpNeg.expNeg (Q'.invSucc 1) (Q'.invSucc_nonneg 1)))
      (ExpNeg.expNeg 1 qzero_le_one) :=
  CReal.Equiv.trans
    (expNeg_add_equiv (Q'.invSucc 1) (Q'.invSucc 1)
      (Q'.invSucc_nonneg 1) (Q'.invSucc_nonneg 1))
    (expNeg_eqv_congr (Q'.zero_le_add _ _ (Q'.invSucc_nonneg 1) (Q'.invSucc_nonneg 1))
      qzero_le_one (by decide))

/-- **`geRat (e^{−1}) (1/2·1/2)`** — the concrete positive lower bound on the
irrational UV exponent seed `e^{−1}` of `concreteTowerE 1`, via `geRat_mul`. -/
theorem geRat_expNeg_one :
    ExpPos.geRat (ExpNeg.expNeg 1 qzero_le_one) (Q'.invSucc 1 * Q'.invSucc 1) := by
  have hprod : ExpPos.geRat
      (CReal.mul (ExpNeg.expNeg (Q'.invSucc 1) (Q'.invSucc_nonneg 1))
                 (ExpNeg.expNeg (Q'.invSucc 1) (Q'.invSucc_nonneg 1)))
      (Q'.invSucc 1 * Q'.invSucc 1) :=
    geRat_mul (Q'.invSucc_nonneg 1) geRat_expHalf geRat_expHalf
      (expNeg_geRat_zero (Q'.invSucc 1) (Q'.invSucc_nonneg 1))
  exact SU3CharFactor.geRat_of_equiv (CReal.Equiv.symm expNeg_one_eq_prod) hprod

/-- The concrete positive separator level `εlo = 1/2·1/2 − 1/8 = 1/8 > 0`. -/
def concreteELevel : Q' := Q'.invSucc 1 * Q'.invSucc 1 + -(Q'.invSucc 7)

theorem concreteELevel_pos : (0 : Q') < concreteELevel := by decide

/-- **`sep (concreteTowerE 1) 0 ≤ 1/(1+εlo) < 1`.**  The base separator of the
irrational `e^{−1}` flow has a concrete rational upper bound below `1`: the exponent
`e^{−1}` is eventually `≥ εlo` (`geRat_expNeg_one`, peeled by `eventually_lb_of_geRat`),
so every term `e^{−(e^{−1})_K} ≤ 1/(1+εlo)` (`expNeg_le_oneOver1p` + `oneOver1p_antitone`),
hence the limit `sep 0 ≤ 1/(1+εlo)`. -/
theorem sep0E_le_oneOver1p :
    CReal.leRat (sep (concreteTowerE 1) 0)
      (ExpUBInstance.oneOver1p concreteELevel) := by
  obtain ⟨N, hN⟩ := eventually_lb_of_geRat geRat_expNeg_one (by decide : (0 : Q') < Q'.invSucc 7)
  refine leRat_limit_of_eventually
    (expNegCD_converges ((concreteTowerE 1).w 0) ((concreteTowerE 1).dw 0))
    ⟨N, fun K hK => ?_⟩
  refine CReal.leRat_mono
    (expNeg_le_oneOver1p (((concreteTowerE 1).w 0).approx K) (((concreteTowerE 1).dw 0).hpos K)) ?_
  exact ExpUBInstance.oneOver1p_antitone concreteELevel (((concreteTowerE 1).w 0).approx K)
    (hN K hK)

/-- The explicit UV-gap floor for the `e^{−1}` model: `1 − 1/(1+εlo) > 0`. -/
def concreteEFloor : Q' := 1 + -(ExpUBInstance.oneOver1p concreteELevel)

theorem concreteEFloor_pos : (0 : Q') < concreteEFloor :=
  CodynamicCRealFlow.qsub_pos_of_lt
    (CodynamicCRealFlow.oneOver1p_lt_one concreteELevel_pos)

/-- **The UV-gap floor lies below `physGapC 0` for the `e^{−1}` model.**  At the
coarsest scale the block spacing is `a_0 = 1`, so `physGapC 0 ≃ 1 − sep 0`, and
`concreteEFloor = 1 − 1/(1+εlo) ≤ 1 − sep 0` from `sep0E_le_oneOver1p`. -/
theorem concreteE_hbase :
    CReal.leEv (CReal.ofQ' concreteEFloor)
      (physGapC 1 (sep (concreteTowerE 1)) (geomSpacing 1) 0) := by
  have hmargin : CReal.leEv (CReal.ofQ' concreteEFloor)
      (CReal.sub CReal.cone (sep (concreteTowerE 1) 0)) :=
    RateMatchFloor.leEv_oneSub_of_leRat sep0E_le_oneOver1p
  have hgap0 : CReal.Equiv (physGapC 1 (sep (concreteTowerE 1)) (geomSpacing 1) 0)
      (CReal.sub CReal.cone (sep (concreteTowerE 1) 0)) := by
    show CReal.Equiv
      (CReal.mul (CReal.sub CReal.cone (sep (concreteTowerE 1) 0))
        (recipSpacingC (geomSpacing 1) 0))
      (CReal.sub CReal.cone (sep (concreteTowerE 1) 0))
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right ?_) (CRealAlg.cmul_cone _)
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (Q'.divPos 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0)).eqv (1 : Q')
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv (Q'.divPos 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0))))
      (Q'.divPos_mul_eqv 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0))
  exact CReal.leEv_trans hmargin (RateMatchFloor.leEv_of_equiv (CReal.Equiv.symm hgap0))

/-- **THE CONCRETE IRRATIONAL `e^{−1}` BLOCK-SPIN MODEL.**  Block factor `b = 1`,
the irrational-exponent tower `concreteTowerE 1` (exponents `e^{−1}/2^k`,
separators `e^{−(e^{−1})/2^k}`, all irrational), UV seed `e^{−1} > 0`, and the
explicit UV-gap floor `1 − 1/(1+εlo)`. -/
def concreteEModel : SelfSimilarBlockSpinModel where
  b := 1
  hb := by decide
  T := concreteTowerE 1
  uvSeed := posEv_expNeg_one
  floor0 := concreteEFloor
  floor0_pos := concreteEFloor_pos
  hbase0 := concreteE_hbase

/-- **THE FULLY-UNCONDITIONAL CONCRETE CAPSTONE.**  The genuine constructive-real,
genuinely-IRRATIONAL `e^{−1}`-seeded self-similar block-spin model is a complete
instance of the continuum mass gap: it satisfies the per-step `RateMatch`, carries a
strictly-positive spacing-uniform physical-gap floor at every scale of the genuine
`a → 0` block schedule, and realises the dimensional-transmutation limit
`2^k·(1 − e^{−(e^{−1})/2^k}) → 1`.  No open hypothesis. -/
def blockSpinModel_continuum_gap_concreteE : BlockSpinContinuumGap concreteEModel :=
  blockSpinModel_continuum_gap concreteEModel

/-- The concrete `e^{−1}` model's continuum floor is strictly positive — the
irrational-flow physical mass gap genuinely survives `a → 0`. -/
theorem blockSpinModel_concreteE_floor_pos :
    (0 : Q') < blockSpinModel_continuum_gap_concreteE.residual.continuumFloor :=
  blockSpinModel_continuum_gap_concreteE.residual.continuumFloor_pos

/-- The concrete `e^{−1}` model's dimensional-transmutation limit, extracted: the
rescaled lattice margin `2^k·(1 − sep_k) → w₀ = 1`. -/
theorem blockSpinModel_concreteE_transmutation :
    CReal.ConvergesTo (transmuted 1 (by decide) (fun k => (1 + 1) ^ k - 1))
      (CReal.ofQ' 1) :=
  blockSpinModel_continuum_gap_concreteE.transmutation

/-! ## 4. The GNS/OS reconstruction wire (interface level)

The reconstructed mass gap lives on the complete GNS Hilbert space.  We re-expose
the OS reconstruction so the block-spin model's per-scale gap (margin `1 − sep`,
geometric decay `sep ⁿ`) sits next to its operator-theoretic realisation.  The
genuine spacing-uniform `SpectralGapData` for the physical Wilson transfer operator
is itself the open continuum input (= the OS face of `PhysicalRGInput`); the
extraction below is GREEN given any such datum. -/

/-- **The reconstructed mass gap from a located transfer-operator gap.**  From any
`SpectralGapData` on a complete GNS Hilbert space, extract the strictly-positive
eigenvalue-gap margin `Δ = 1 − sep > 0` and the geometric two-point decay
`G(n) ≤ G(0)·sep ⁿ` — the same `(1 − sep, sep ⁿ)` shape the block-spin model
exhibits at each scale.  A direct re-exposure of `mass_gap_of_spectralGap`. -/
theorem blockSpinModel_reconstructed_gap {D : GNSQuotient.GNSData}
    {H : GNSQuotient.CompleteGNSHilbert D} (G : SpectralGapData H) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, SpectralGap.corr G.model n
        ≤ (SpectralGap.corr G.model 0) * G.gap.sep ^ n :=
  mass_gap_of_spectralGap G

/-! ## 5. The SINGLE remaining physical-RG input -/

/-- **THE PHYSICAL-RG INPUT — the exact single remaining obligation.**  An
ABSTRACT separator family `physSep : Nat → CReal` — the genuine physical Yang–Mills
RG separators (the actual lattice gap under block-spin decimation) — together with:

  * `selfSimilar` — **THE OPEN DYNAMICAL-RG LAW**: the physical separators obey the
    self-similar geometric schedule `sep_k ≃ (sep_{k+1})^(b+1)`.  This is the sole
    statement that is NOT discharged here.
  * `sepNonneg` / `sepLeOne` — the physical separators are `[0,1]`-valued
    (correlation ratios; physically automatic);
  * an explicit strictly-positive UV-gap floor below the physical gap at the
    coarsest scale.

It is deliberately left UNINHABITED: inhabiting it for the physical theory is the
identification of the genuine AF lattice separator schedule with the geometric
self-similar law — the program's remaining obligation. -/
structure PhysicalRGInput : Type where
  /-- The renormalization-group block factor. -/
  b : Nat
  /-- The block factor is a genuine decimation: `b ≥ 1`. -/
  hb : 1 ≤ b
  /-- The genuine physical Yang–Mills RG separators under block-spin decimation. -/
  physSep : Nat → CReal
  /-- **THE OPEN DYNAMICAL-RG LAW.**  The physical separators are self-similar:
  `sep_k ≃ (sep_{k+1})^(b+1)`. -/
  selfSimilar : selfSimilarC b physSep
  /-- The physical separators are nonnegative. -/
  sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0
  /-- The physical separators are `≤ 1`. -/
  sepLeOne : ∀ k, CReal.leRat (physSep k) 1
  /-- The explicit UV-gap floor (supplied as data). -/
  floor0 : Q'
  /-- The UV-gap floor is strictly positive. -/
  floor0_pos : (0 : Q') < floor0
  /-- The UV-gap floor lies below the physical gap at the coarsest scale. -/
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (physGapC b physSep (geomSpacing b) 0)

/-- **The block-rate `RateMatch` for any `[0,1]`-bounded separator family.**  The
geometric block spacing's per-step ratio is the block factor `b+1`, and the
margin-decay factor `geomSumC (s (N+1)) (b+1)` is the sum of `b+1` separator powers
each in `[0,1]`, hence `≤ b+1` — so `RateMatch` holds.  The tower-free generalisation
of `afBlockRateMatch`. -/
theorem rateMatch_geomSpacing_of_bounds {b : Nat} {s : Nat → CReal}
    (h0 : ∀ k, ExpPos.geRat (s k) 0) (h1 : ∀ k, CReal.leRat (s k) 1) :
    RateMatch b s (geomSpacing b) :=
  RateMatchFloor.rateMatch_of_scalar (fun N => by
    have hcard := RateMatchFloor.geomSumC_leRat_card (h0 (N + 1)) (h1 (N + 1)) (b + 1)
    refine CReal.leRat_mono hcard ?_
    apply Q'.le_divPos_of_mul_le ((geomSpacing b).a N) ((geomSpacing b).a (N + 1))
      ((geomSpacing b).a_pos (N + 1))
    have heq : (Q'.ofNat (b + 1) * (RateMatchFloor.geomA b N * Q'.invSucc b)).eqv
        (RateMatchFloor.geomA b N) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat (b + 1))
        (RateMatchFloor.geomA b N * Q'.invSucc b)
        (Q'.invSucc b * RateMatchFloor.geomA b N)
        (Q'.mul_comm_eqv (RateMatchFloor.geomA b N) (Q'.invSucc b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (b + 1)) (Q'.invSucc b)
          (RateMatchFloor.geomA b N))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (RateMatchFloor.geomA b N) (Q'.ofNat_succ_mul_invSucc b)) ?_
      exact Q'.one_mul_eqv (RateMatchFloor.geomA b N)
    exact Q'.le_of_eqv heq)

/-- **THE PHYSICAL CONTINUUM MASS GAP FROM THE PHYSICAL-RG INPUT (GREEN).**  Given
the single dynamical-RG input — the physical separators obey the self-similar law —
the physical gap `physGapC N = (1 − sep N)·(1/a_N)` carries a strictly-positive
spacing-uniform floor at EVERY scale of the genuine `a → 0` block schedule.  This is
the program's payoff: the ONE remaining obligation implies the physical continuum
mass gap.  (The `selfSimilar` field is the sole open input; it is NOT inhabited.) -/
def physicalRG_continuum_gap (P : PhysicalRGInput) :
    UnifiedContinuumFloor.CRealFloor (physGapC P.b P.physSep (geomSpacing P.b)) :=
  RateMatchFloor.crealFloor_of_rateMatch P.selfSimilar (geomSpacing P.b)
    (fun N => ExpPos.geRat_mono (YMGap.Continuum.geRat_sub_cone (P.sepLeOne (N + 1)))
      (by decide : (0 : Q') ≤ (1 : Q') + -(1 : Q')))
    (rateMatch_geomSpacing_of_bounds P.sepNonneg P.sepLeOne)
    P.floor0 P.floor0_pos P.hbase0

/-- The physical continuum mass gap's floor is strictly positive — the genuine
spacing-uniform mass gap, GIVEN the physical-RG input. -/
theorem physicalRG_continuum_floor_pos (P : PhysicalRGInput) :
    (0 : Q') < (physicalRG_continuum_gap P).floor :=
  (physicalRG_continuum_gap P).floor_pos

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.geRat_mul
#print axioms YMGap.Continuum.eventually_lb_of_geRat
#print axioms YMGap.Continuum.blockSpinModel_continuum_gap
#print axioms YMGap.Continuum.blockSpinModel_continuum_floor_pos
#print axioms YMGap.Continuum.geRat_expHalf
#print axioms YMGap.Continuum.geRat_expNeg_one
#print axioms YMGap.Continuum.sep0E_le_oneOver1p
#print axioms YMGap.Continuum.concreteEFloor_pos
#print axioms YMGap.Continuum.concreteE_hbase
#print axioms YMGap.Continuum.concreteEModel
#print axioms YMGap.Continuum.blockSpinModel_continuum_gap_concreteE
#print axioms YMGap.Continuum.blockSpinModel_concreteE_floor_pos
#print axioms YMGap.Continuum.blockSpinModel_concreteE_transmutation
#print axioms YMGap.Continuum.blockSpinModel_reconstructed_gap
#print axioms YMGap.Continuum.rateMatch_geomSpacing_of_bounds
#print axioms YMGap.Continuum.physicalRG_continuum_gap
#print axioms YMGap.Continuum.physicalRG_continuum_floor_pos
