/-
The `H = −log T` interface: the eigenvalue-level constructive mass gap on the
Hamiltonian side.

OS reconstruction gives `T = e^{−aH}`, i.e. (setting `a = 1`) `H = −log T`.  On
`vac⊥` the transfer spectrum lies in `[0, sep]` with the located separator
`sep < 1`; the vacuum is the eigenvalue `1`.  Under the monotone-decreasing map
`f = −log`:

  * the vacuum `1 ↦ −log 1 = 0` (`CRealLog.logRat_one`), so `H`'s vacuum energy
    is genuinely `0`;
  * the located top-of-excited-spectrum `sep ↦ −log sep` = the located BOTTOM of
    `spec(H | vac⊥)`.

So the H-side mass gap is `Δ = (−log sep) − 0 = −log sep > 0`.  There is NO
unbounded-operator theory, NO Stone theorem, NO spectral measure here: the gap is
the monotone `−log` image of the already-LOCATED compact-transfer-operator
separator `LocatedSpectralGap.sep`.

# What is PROVED here (axiom-clean, `[propext]`/`[propext, Quot.sound]`)

The entire EIGENVALUE-level transport
  `T-gap (sep < 1)  ⟹  H-gap (−log sep > 0)`
as a genuine `CReal` `Δ = −log sep` with `CReal.IsPositive Δ`, on the decidable
artanh window `|yOf sep| ≤ 1/3` (equivalently `sep ∈ [1/2, 1)`):

  * `sepPlusOne_pos`   : `0 < sep + 1`   (from `LocatedSpectralGap.sep_nonneg`);
  * `yOf_sep_neg`      : `yOf sep < 0`   (from `sep_lt_one`);
  * `isPositive_neg_logRat` : the load-bearing transport `IsPositive (−log sep)`;
  * `hamiltonian_vacuum_energy_zero` : `−log 1 ≃ 0`.

# What is NAMED (honest residuals, Type-level, Rule 8)

  * `HGapBelowWindowResidual`      — separators `sep < 1/2` (the gap is LARGER,
    physically the easier case) fall outside the directly-reducible artanh
    window; closing them needs `CRealLog.CRealLogRangeReduction`.
  * `SelfAdjointHamiltonianResidual` — the actual OPERATOR `H = −log T` on the
    completed carrier (Bridges–Ishihara constructive continuous functional
    calculus, `f(T) = lim pₙ(T)`).  NOT needed for the eigenvalue-level gap; the
    `TransferOperator` carrier has no vector-space operations yet.
  * `SpectrumInfResidual`          — identifying `Δ = inf spec(H | vac⊥)` as a
    located infimum ON THE OPERATOR (vs. the finite `SpectralModel` eigenvalue
    image).

Reference: D. Bridges & H. Ishihara, *Spectra and the compact operators in a
general Hilbert space* (1994); H. Ishihara, constructive functional calculus
(2001).
-/

import YMGap.Continuum.GNSDynamics
import YMGap.Constructive.CRealLog

namespace YMGap.Constructive.Q'

/-! ## Two `Q'` sign helpers (num-level, `omega`) -/

/-- If `a < 0` then `0 < -a`. -/
theorem neg_pos_of_neg {a : Q'} (h : a < (0 : Q')) : (0 : Q') < -a := by
  have ha : a.num < 0 := by
    have h' : a.num * (1 : Int) < (0 : Int) * (a.den : Int) := h
    omega
  show (0 : Int) * ((-a).den : Int) < (-(a.num)) * (1 : Int)
  omega

/-- Sum of two negatives is negative. -/
theorem add_neg {a b : Q'} (ha : a < (0 : Q')) (hb : b < (0 : Q')) :
    a + b < (0 : Q') := by
  have ha' : a.num < 0 := by
    have h : a.num * (1 : Int) < (0 : Int) * (a.den : Int) := ha; omega
  have hb' : b.num < 0 := by
    have h : b.num * (1 : Int) < (0 : Int) * (b.den : Int) := hb; omega
  have had : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have t1 : a.num * (b.den : Int) < 0 := Int.mul_neg_of_neg_of_pos ha' hbd
  have t2 : b.num * (a.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hb' had
  show (a.num * (b.den : Int) + b.num * (a.den : Int)) * (1 : Int)
      < (0 : Int) * ((a + b).den : Int)
  omega

end YMGap.Constructive.Q'

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Constructive.CRealLog

/-! ## Separator arithmetic -/

/-- `0 < sep + 1` — from `LocatedSpectralGap.sep_nonneg`.  (`yOf sep` needs it.) -/
theorem sepPlusOne_pos {S : SpectralModel} (g : LocatedSpectralGap S) :
    (0 : Q') < g.sep + 1 := by
  have h : (0 : Int) * (g.sep.den : Int) ≤ g.sep.num * (1 : Int) := g.sep_nonneg
  have hn : (0 : Int) ≤ g.sep.num := by omega
  have hd : (0 : Int) < (g.sep.den : Int) := by exact_mod_cast g.sep.den_pos
  show (0 : Int) * ((g.sep + 1).den : Int)
      < (g.sep.num * (1 : Int) + (1 : Int) * (g.sep.den : Int)) * (1 : Int)
  omega

/-- `yOf sep < 0` — the artanh argument of a separator strictly below `1`.
`yOf sep = (sep − 1)/(sep + 1)` and `sep < 1 ⟹ sep − 1 < 0`, `sep + 1 > 0`. -/
theorem yOf_sep_neg (sep : Q') (hsep1 : (0 : Q') < sep + 1) (hlt : sep < (1 : Q')) :
    yOf sep hsep1 < (0 : Q') := by
  have hnd : sep.num < (sep.den : Int) := by
    have h : sep.num * (1 : Int) < (1 : Int) * (sep.den : Int) := hlt
    omega
  show ((sep + -1).num * (Q'.recipPos (sep + 1) hsep1).num) * (1 : Int)
      < (0 : Int) * ((yOf sep hsep1).den : Int)
  rw [Q'.recipPos_num]
  have hsn : (sep + -1).num = sep.num - (sep.den : Int) := by
    show sep.num * (1 : Int) + (-1 : Int) * (sep.den : Int) = sep.num - (sep.den : Int)
    omega
  rw [hsn]
  have hdpos : (0 : Int) < ((sep + 1).den : Int) := by exact_mod_cast (sep + 1).den_pos
  have hlhs : (sep.num - (sep.den : Int)) * ((sep + 1).den : Int) < 0 :=
    Int.mul_neg_of_neg_of_pos (by omega) hdpos
  rw [Int.mul_one, Int.zero_mul]
  exact hlhs

/-! ## The load-bearing transport: `T-gap ⟹ H-gap positivity`

`Δ := −log sep = CReal.neg (logRat sep …)`.  Its approximations are
`−(partialSum (yOf sep) n + partialSum (yOf sep) n)`.  We exhibit the positive
rational witness `ε = −(term (yOf sep) 0 + term (yOf sep) 0) > 0`:

  * for `n ≥ 1`, `partialSum (yOf sep) n ≤ term (yOf sep) 0` (monotone-decreasing
    partial sums for a nonpositive argument), so `Δ.approx n ≥ ε`;
  * for `n = 0`, the one-slack `invSucc 0 = 1` carries it (`ε ≤ 2/3 ≤ 1`).
-/

/-- **`IsPositive (−log sep)`** for a separator with `sep < 1` inside the artanh
window.  This is the eigenvalue-level Hamiltonian mass gap: `−log sep > 0`. -/
theorem isPositive_neg_logRat
    (sep : Q') (hsep1 : (0 : Q') < sep + 1) (hlt : sep < (1 : Q'))
    (hwin : Q'.abs (yOf sep hsep1) ≤ recipOdd 1) :
    CReal.IsPositive (CReal.neg (logRat sep hsep1 hwin)) := by
  -- signs
  have hyneg_lt : yOf sep hsep1 < (0 : Q') := yOf_sep_neg sep hsep1 hlt
  have hyneg : yOf sep hsep1 ≤ (0 : Q') := Q'.le_of_lt hyneg_lt
  have hm_lt : term (yOf sep hsep1) 0 < (0 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_of_eqv (term_zero_eqv_self (yOf sep hsep1))) hyneg_lt
  have hmm_lt : term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0 < (0 : Q') :=
    Q'.add_neg hm_lt hm_lt
  have hb_pos : (0 : Q') < -(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0) :=
    Q'.neg_pos_of_neg hmm_lt
  -- window lower bound `−1/3 ≤ term (yOf sep) 0`
  have hm_lb : -(recipOdd 1) ≤ term (yOf sep hsep1) 0 := by
    have h1 : -(yOf sep hsep1) ≤ Q'.abs (yOf sep hsep1) := Q'.neg_le_abs (yOf sep hsep1)
    have h2 : -(yOf sep hsep1) ≤ recipOdd 1 := Q'.le_trans' _ _ _ h1 hwin
    have h3 : -(recipOdd 1) ≤ -(-(yOf sep hsep1)) := Q'.neg_le_neg h2
    have h4 : -(recipOdd 1) ≤ yOf sep hsep1 :=
      Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (Q'.neg_neg_eqv (yOf sep hsep1)))
    exact Q'.le_trans' _ _ _ h4 (Q'.ge_of_eqv (term_zero_eqv_self (yOf sep hsep1)))
  -- hence `ε ≤ 1` (needed only for the `n = 0` slack)
  have hb_le_one : -(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0) ≤ (1 : Q') := by
    have hmm_lb : (-(recipOdd 1)) + (-(recipOdd 1))
        ≤ term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0 := Q'.add_le_add hm_lb hm_lb
    have hcst : -(1 : Q') ≤ (-(recipOdd 1)) + (-(recipOdd 1)) := by decide
    have hmm_lb2 : -(1 : Q') ≤ term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0 :=
      Q'.le_trans' _ _ _ hcst hmm_lb
    have h5 : -(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0) ≤ -(-(1 : Q')) :=
      Q'.neg_le_neg hmm_lb2
    exact Q'.le_trans' _ _ _ h5 (Q'.le_of_eqv (Q'.neg_neg_eqv (1 : Q')))
  refine ⟨-(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0), hb_pos, ?_⟩
  intro n
  show -(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0)
      ≤ (CReal.neg (logRat sep hsep1 hwin)).approx n + Q'.invSucc n
  rw [CReal.neg_approx, logRat_approx]
  cases n with
  | zero =>
    rw [partialSum_zero]
    have hrhs : -((0 : Q') + 0) + Q'.invSucc 0 = (1 : Q') := by decide
    rw [hrhs]
    exact hb_le_one
  | succ k =>
    have hstep0 : partialSum (yOf sep hsep1) (1 + k) ≤ partialSum (yOf sep hsep1) 1 :=
      partialSum_anti_of_nonpos (yOf sep hsep1) hyneg 1 k
    have h1k : 1 + k = k + 1 := by omega
    rw [h1k] at hstep0
    have hps1 : partialSum (yOf sep hsep1) 1 = term (yOf sep hsep1) 0 := by
      rw [partialSum_succ, partialSum_zero, Q'.zero_add']
    rw [hps1] at hstep0
    have hsum : partialSum (yOf sep hsep1) (k + 1) + partialSum (yOf sep hsep1) (k + 1)
        ≤ term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0 := Q'.add_le_add hstep0 hstep0
    have hneg : -(term (yOf sep hsep1) 0 + term (yOf sep hsep1) 0)
        ≤ -(partialSum (yOf sep hsep1) (k + 1) + partialSum (yOf sep hsep1) (k + 1)) :=
      Q'.neg_le_neg hsum
    refine Q'.le_trans' _ _ _ hneg ?_
    exact Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg (k + 1))

/-! ## The vacuum energy is genuinely `0` -/

/-- `Equiv (neg x) 0` from `Equiv x 0`: negation is pointwise, so it fixes `0`. -/
theorem neg_equiv_czero {x : CReal} (h : CReal.Equiv x CReal.czero) :
    CReal.Equiv (CReal.neg x) CReal.czero := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have hz : CReal.czero.approx n = (0 : Q') := rfl
  rw [hz] at h1 h2
  refine ⟨?_, ?_⟩
  · show (CReal.neg x).approx n ≤ CReal.czero.approx n + ε
    rw [CReal.neg_approx, hz]
    have hk : -(x.approx n) ≤ -(0 : Q') + ε := Q'.neg_le_neg_add h2
    refine Q'.le_trans' _ _ _ hk ?_
    exact Q'.add_le_add_right _ _ ε (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
  · show CReal.czero.approx n ≤ (CReal.neg x).approx n + ε
    rw [CReal.neg_approx, hz]
    have hk : -(0 : Q') ≤ -(x.approx n) + ε := Q'.neg_le_neg_add h1
    refine Q'.le_trans' _ _ _ ?_ hk
    exact Q'.ge_of_eqv (by decide : (-(0 : Q')).eqv 0)

/-- **The Hamiltonian vacuum energy is `0`.**  `H`'s vacuum is `−log 1 ≃ 0`. -/
theorem hamiltonian_vacuum_energy_zero :
    CReal.Equiv (CReal.neg (logRat (1 : Q') (by decide) yOf_one_window)) CReal.czero :=
  neg_equiv_czero logRat_one

/-! ## The Hamiltonian mass-gap interface -/

/-- The reconstructed Hamiltonian mass gap `Δ = −log sep` as a genuine `CReal`,
built from the transfer separator inside the artanh window. -/
def SpectralGapData.hamiltonianGapReal {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) : CReal :=
  CReal.neg (logRat G.gap.sep (sepPlusOne_pos G.gap) hwin)

/-- **`Δ = −log sep` is strictly positive** — the eigenvalue-level H-mass-gap. -/
theorem SpectralGapData.hamiltonianGapReal_pos {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) :
    CReal.IsPositive (G.hamiltonianGapReal hwin) :=
  isPositive_neg_logRat G.gap.sep (sepPlusOne_pos G.gap) G.gap.sep_lt_one hwin

/-- The **Hamiltonian gap datum** reconstructed from a `SpectralGapData` on the
decidable artanh window.  `Type`-level (Rule 8). -/
structure HamiltonianGap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- The decidable window certificate for the transfer separator. -/
  hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1
  /-- The physical mass gap `Δ = −log sep`, a genuine `CReal`. -/
  Δ : CReal
  /-- `Δ` really is `−log sep`. -/
  hΔ : Δ = CReal.neg (logRat G.gap.sep (sepPlusOne_pos G.gap) hwin)
  /-- `Δ` is strictly positive — the located H-gap. -/
  Δ_pos : CReal.IsPositive Δ

/-- **Constructor**: from a window certificate, produce the `HamiltonianGap`. -/
def SpectralGapData.hamiltonianGap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) :
    HamiltonianGap G where
  hwin := hwin
  Δ := G.hamiltonianGapReal hwin
  hΔ := rfl
  Δ_pos := G.hamiltonianGapReal_pos hwin

/-- **Capstone: `mass_gap_hamiltonian`.**  From a located transfer gap
(`sep < 1`) inside the artanh window, the reconstructed Hamiltonian `H = −log T`
has a strictly positive mass gap `Δ = −log sep`. -/
theorem mass_gap_hamiltonian {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) :
    ∃ Δ : CReal, CReal.IsPositive Δ ∧
      Δ = CReal.neg (logRat G.gap.sep (sepPlusOne_pos G.gap) hwin) :=
  ⟨G.hamiltonianGapReal hwin, G.hamiltonianGapReal_pos hwin, rfl⟩

/-! ## Honest named residuals (Type-level, Rule 8) -/

/-- **Below-window residual.**  Separators `sep < 1/2` (the gap `−log sep` is
LARGER, physically the easier case) fall outside the directly-reducible artanh
window `|yOf sep| ≤ 1/3`.  Closing them needs the named binary range reduction
`CRealLog.CRealLogRangeReduction` of the separator; the in-window `sep ∈ [1/2, 1)`
case is the genuine deliverable above.  Not faked. -/
structure HGapBelowWindowResidual (sep : Q') (hsep1 : (0 : Q') < sep + 1) : Type where
  /-- The range-reduction datum for `sep` that would extend `logRat` off-window. -/
  reduction : CRealLogRangeReduction (CReal.ofQ' sep)

/-- **Self-adjoint operator residual.**  The eigenvalue-level gap above never
forms the OPERATOR `H = −log T` on the completed carrier: the `TransferOperator`
carrier has no vector-space operations, so no operator polynomials `pₙ(T)`.  The
genuine self-adjoint `H` with `e^{−H} = T` is the Bridges–Ishihara constructive
continuous functional calculus `f(T) = lim pₙ(T)`, deferred here. -/
structure SelfAdjointHamiltonianResidual {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- The operator `H` on the completed carrier. -/
  op : H.hilbert.carrier → H.hilbert.carrier
  /-- Self-adjointness of `H` w.r.t. the completed inner product. -/
  selfAdjoint : ∀ x y, H.hilbert.cinner (op x) y = H.hilbert.cinner x (op y)

/-- **Spectrum-infimum residual.**  Identifying `Δ = inf spec(H | vac⊥)` as a
located infimum ON THE OPERATOR (as opposed to the finite `SpectralModel`
eigenvalue image whose monotone `−log` picture is proved above).  Deferred with
the operator `H` itself. -/
structure SpectrumInfResidual {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- The claimed located operator infimum, a `CReal`. -/
  infSpec : CReal
  /-- It agrees with the reconstructed eigenvalue-level gap. -/
  agrees : ∀ (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1),
    CReal.Equiv infSpec (G.hamiltonianGapReal hwin)

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.neg_pos_of_neg
#print axioms YMGap.Constructive.Q'.add_neg
#print axioms YMGap.Continuum.sepPlusOne_pos
#print axioms YMGap.Continuum.yOf_sep_neg
#print axioms YMGap.Continuum.isPositive_neg_logRat
#print axioms YMGap.Continuum.neg_equiv_czero
#print axioms YMGap.Continuum.hamiltonian_vacuum_energy_zero
#print axioms YMGap.Continuum.SpectralGapData.hamiltonianGapReal_pos
#print axioms YMGap.Continuum.mass_gap_hamiltonian
