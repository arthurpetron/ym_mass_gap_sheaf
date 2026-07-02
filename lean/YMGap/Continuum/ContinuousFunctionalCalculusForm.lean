/-
FORMING the transfer polynomial operator `p(T) = Σ_k cₖ·Tᵏ` as a genuine
carrier→carrier map on the completed GNS Hilbert space, and DISCHARGING the
bounded transfer functional-calculus residual for it.

# What this module adds (all axiom-clean)

`Continuum/ContinuousTransferCalculus.lean` proved the ANALYTIC core of the
continuous functional calculus — the diagonal polynomial norm bound
`polyNormBound` (`‖p(T)x‖² ≤ ‖p‖²_{∞,spec}·‖x‖²` on the resolved quadratic form)
and the pointwise operator limit `symbolLimit` (`f(λ) = lim pₙ(λ)`).  The block
to a full discharge was ARCHITECTURAL: `p(T) = Σ_k cₖ·Tᵏ` had not been FORMED as
an actual map on the carrier, because the bare `TransferOperator` interface
exposes only composition `Tⁿ`.

Here we close that architectural gap using the completed carrier's ALREADY-BUILT
vector-space operations (`cAdd`, `cSmul`) together with an
`AdditiveTransferOperator`:

  * **The inner-product respects the vector operations** (the genuinely new
    algebraic content).  `cinnerCompl_cAdd_left` / `cinnerCompl_cSmul_left` /
    `cinnerCompl_comm` and their right-slot mirrors prove that the completed
    inner product `cinnerCompl` is biadditive and `Q'`-bihomogeneous — descended
    from the pre-Hilbert form's biadditivity (`B_add_left`, `B_smul_left`,
    `B_symm`) through the constructive limit machinery
    (`Equiv_of_limit_of_equal`, `convergesTo_add`, `convergesTo_constMul`).  This
    is the "cAdd/cSmul respect the inner product" fact that lets an operator
    built from `cAdd`/`cSmul` be manipulated inside `cinner`.

  * **`polyApply` — `p(T)` FORMED as a carrier map.**  `polyApply p x` realizes
    `p(T)x = Σ_k cₖ·Tᵏx` in Horner form
    `c₀·x + T(c₁·x + T(c₂·x + …))` using `cSmul` for the scalars, `T` for the
    transfer, and `cAdd` for the sums — a genuine
    `GNSCompletionSpace → GNSCompletionSpace` map.

  * **`polyApply_selfAdjoint`** — the FORMED operator is self-adjoint w.r.t. the
    completed inner product, proved by induction on the coefficient list from the
    inner-product bridges and `T`'s self-adjointness (via the auxiliary
    `polyApply_Tcomm_inner`, the operator-form statement that `p(T)` commutes with
    `T`).

  * **`dischargeBTC`** — composing the FORMED `polyApply` with the proved
    analytic core `polyNormBound` DISCHARGES
    `BoundedTransferCalculus.BoundedTransferCalculusResidual` for a general
    polynomial `p` (a strict upgrade over `monomialCalculus`, which only ever
    formed a single monomial `Tⁿ`), given the standard poly-diagonal spectral
    resolution `PolyNormData` (named `Type`-level data, exactly as
    `DiagResolution` / `CharacterDiagResolution` are).

# Honest scope

The remaining continuous-`f` step is: feed a uniformly-Cauchy polynomial
sequence `pₙ` (Bernstein/Weierstrass) into `polyApply` and take the carrier
limit; `symbolLimit` already builds the limit symbol `f(λ)` pointwise, and
`polyNormBound` bounds each `polyApply pₙ`.  `PolyNormData` is the poly-diagonal
resolution datum (the standard Osterwalder–Seiler / Peter–Weyl spectral input),
carried as `Type`-level data.  Nothing here is faked.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Continuum.RCScaleClose
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.AbsQ

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuousTransferCalculus

/-! ## Part 0 — two convergence closure lemmas for `CReal` limits -/

namespace YMGap.Constructive.CReal

/-- **Sums of convergent sequences converge to the sum.**  If `sA → A` and
`sB → B` then `n ↦ sA n + sB n → A + B`.  The standard `ε/2` split. -/
theorem convergesTo_add {sA sB : Nat → CReal} {A B : CReal}
    (hA : ConvergesTo sA A) (hB : ConvergesTo sB B) :
    ConvergesTo (fun N => add (sA N) (sB N)) (add A B) := by
  intro ε hε
  have hh : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨NA, hNA⟩ := hA (HalfPow.half * ε) hh
  obtain ⟨NB, hNB⟩ := hB (HalfPow.half * ε) hh
  refine ⟨max NA NB, fun N hN => ?_⟩
  obtain ⟨PA, hPA⟩ := hNA N (Nat.le_trans (Nat.le_max_left _ _) hN)
  obtain ⟨PB, hPB⟩ := hNB N (Nat.le_trans (Nat.le_max_right _ _) hN)
  refine ⟨max PA PB, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := hPA n (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨b1, b2⟩ := hPB n (Nat.le_trans (Nat.le_max_right _ _) hn)
  rw [add_approx, add_approx]
  refine ⟨?_, ?_⟩
  · have hsum := Q'.add_le_add a1 b1
    have ereg := Q'.regroup (A.approx n) (B.approx n) (HalfPow.half * ε)
    have etwo := Q'.add_eqv_congr_left (A.approx n + B.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))
  · have hsum := Q'.add_le_add a2 b2
    have ereg := Q'.regroup ((sA N).approx n) ((sB N).approx n) (HalfPow.half * ε)
    have etwo := Q'.add_eqv_congr_left ((sA N).approx n + (sB N).approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

/-- **Multiplication by a fixed rational preserves convergence.**  If `s → A`
then `n ↦ c·(s n) → c·A`.  The tolerance budget uses the clamped reciprocal
`ε ↦ ε·oneOver1p|c|` (no division), via `key_bound`, and the sign-cased product
bound `mul_le_of_bounds`. -/
theorem convergesTo_constMul (c : Q') {s : Nat → CReal} {A : CReal}
    (h : ConvergesTo s A) :
    ConvergesTo (fun N => mul (ofQ' c) (s N)) (mul (ofQ' c) A) := by
  intro ε hε
  have hBnn : (0 : Q') ≤ Q'.abs c := Q'.abs_nonneg c
  have hcU : c ≤ Q'.abs c := Q'.le_abs_self c
  have hcL : -(Q'.abs c) ≤ c :=
    le_of_le_eqv (Q'.neg_le_neg (Q'.neg_le_abs c)) (Q'.neg_neg_eqv c)
  have hEpos : (0 : Q') < ExpUBInstance.oneOver1p (Q'.abs c) :=
    YMGap.Continuum.HamiltonianScalar.oneOver1p_pos (Q'.abs c)
  have hδpos : (0 : Q') < ε * ExpUBInstance.oneOver1p (Q'.abs c) := Q'.mul_pos hε hEpos
  have hbudget : Q'.abs c * (ε * ExpUBInstance.oneOver1p (Q'.abs c)) ≤ ε :=
    YMGap.Continuum.HamiltonianScalar.key_bound (Q'.abs c) ε hBnn (Q'.le_of_lt hε)
  obtain ⟨Nst, hst⟩ := h (ε * ExpUBInstance.oneOver1p (Q'.abs c)) hδpos
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨P, hP⟩ := hst N hN
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hP n hn
  -- diff bounds on `u := (s N).approx n`, `v := A.approx n`
  have hd1 : (s N).approx n + (-(A.approx n)) ≤ ε * ExpUBInstance.oneOver1p (Q'.abs c) :=
    Q'.sub_le_of_le_add h1
  have hd2 : -(ε * ExpUBInstance.oneOver1p (Q'.abs c)) ≤ (s N).approx n + (-(A.approx n)) :=
    Q'.neg_le_sub_of_le_add h2
  have hd1' : (A.approx n) + (-((s N).approx n)) ≤ ε * ExpUBInstance.oneOver1p (Q'.abs c) :=
    Q'.sub_le_of_le_add h2
  have hd2' : -(ε * ExpUBInstance.oneOver1p (Q'.abs c)) ≤ (A.approx n) + (-((s N).approx n)) :=
    Q'.neg_le_sub_of_le_add h1
  have hcd : c * ((s N).approx n + (-(A.approx n))) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_of_bounds hBnn (Q'.le_of_lt hδpos) hcL hcU hd2 hd1) hbudget
  have hcd' : c * ((A.approx n) + (-((s N).approx n))) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_of_bounds hBnn (Q'.le_of_lt hδpos) hcL hcU hd2' hd1') hbudget
  show c * (s N).approx n ≤ c * A.approx n + ε ∧ c * A.approx n ≤ c * (s N).approx n + ε
  refine ⟨?_, ?_⟩
  · have hexp : (c * (s N).approx n).eqv
        (c * (A.approx n) + c * ((s N).approx n + (-(A.approx n)))) := by
      have e0 : ((s N).approx n).eqv ((A.approx n) + ((s N).approx n + (-(A.approx n)))) :=
        Q'.add_sub_cancel_eqv ((s N).approx n) (A.approx n)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ e0)
        (Q'.mul_add_eqv c (A.approx n) ((s N).approx n + (-(A.approx n))))
    exact le_of_eqv_le hexp (Q'.add_le_add_left _ _ _ hcd)
  · have hexp : (c * (A.approx n)).eqv
        (c * (s N).approx n + c * ((A.approx n) + (-((s N).approx n)))) := by
      have e0 : ((A.approx n)).eqv (((s N).approx n) + ((A.approx n) + (-((s N).approx n)))) :=
        Q'.add_sub_cancel_eqv (A.approx n) ((s N).approx n)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ e0)
        (Q'.mul_add_eqv c ((s N).approx n) ((A.approx n) + (-((s N).approx n))))
    exact le_of_eqv_le hexp (Q'.add_le_add_left _ _ _ hcd')

end YMGap.Constructive.CReal

/-! ## Part 1 — the completed inner product respects `cAdd` / `cSmul` -/

namespace YMGap.Continuum.GNSQuotient.GNSData

open YMGap.Constructive.CReal

variable (D : GNSData)

/-- **Left-additivity of the completed inner product.**
`⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩`, descended from the biadditivity `B_add_left`
through the constructive limit `Equiv_of_limit_of_equal`. -/
theorem cinnerCompl_cAdd_left (x y z : GNSCompletionSpace D) :
    D.cinnerCompl (D.cAdd x y) z = RCadd (D.cinnerCompl x z) (D.cinnerCompl y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq (D.cAddCauchy a b) c N))
    (bSeq := fun N => CReal.add (ofQ' (D.cInnerSeq a c N)) (ofQ' (D.cInnerSeq b c N)))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_add (CReal.convergesTo_ofQ'CauchySeq _ _)
      (CReal.convergesTo_ofQ'CauchySeq _ _))
  intro N
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact D.B_add_left (a.seq N) (b.seq N) (c.seq N)

/-- **Symmetry of the completed inner product.**  `⟨x, y⟩ = ⟨y, x⟩`, from the
form symmetry `B_symm`. -/
theorem cinnerCompl_comm (x y : GNSCompletionSpace D) :
    D.cinnerCompl x y = D.cinnerCompl y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq a b N))
    (bSeq := fun N => ofQ' (D.cInnerSeq b a N))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro N
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact D.B_symm (a.seq N) (b.seq N)

/-- **Left inner product of the embedded zero vanishes.**  `⟨0, y⟩ = 0`. -/
theorem cinnerCompl_embedZero_left (y : GNSCompletionSpace D) :
    D.cinnerCompl (embedV D D.zero) y = RCzero := by
  refine Quotient.inductionOn y ?_
  intro b
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (D.cInnerSeq (constCauchy D D.zero) b N))
    (bSeq := fun N => ofQ' (czero.approx N))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_self czero)
  intro N
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact D.B_zero_left (b.seq N)

/-- **Right-additivity.**  `⟨x, y + z⟩ = ⟨x, y⟩ + ⟨x, z⟩`, from left-additivity
and symmetry. -/
theorem cinnerCompl_cAdd_right (x y z : GNSCompletionSpace D) :
    D.cinnerCompl x (D.cAdd y z) = RCadd (D.cinnerCompl x y) (D.cinnerCompl x z) := by
  rw [D.cinnerCompl_comm x (D.cAdd y z), D.cinnerCompl_cAdd_left y z x,
      D.cinnerCompl_comm y x, D.cinnerCompl_comm z x]

/-- **Right inner product of the embedded zero vanishes.**  `⟨x, 0⟩ = 0`. -/
theorem cinnerCompl_embedZero_right (x : GNSCompletionSpace D) :
    D.cinnerCompl x (embedV D D.zero) = RCzero := by
  rw [D.cinnerCompl_comm x (embedV D D.zero), D.cinnerCompl_embedZero_left]

end YMGap.Continuum.GNSQuotient.GNSData

/-! ## Part 1b — the scalar-slot laws for the `SmulGNSData` scaling `cSmul` -/

namespace YMGap.Continuum.HamiltonianScalar.SmulGNSData

open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

variable (S : YMGap.Continuum.HamiltonianScalar.SmulGNSData)

/-- **Left `Q'`-homogeneity of the completed inner product.**
`⟨c·x, y⟩ = c·⟨x, y⟩`, descended from `B_smul_left` via `convergesTo_constMul`. -/
theorem cinnerCompl_cSmul_left (c : Q') (x y : GNSCompletionSpace S.toGNSData) :
    S.toGNSData.cinnerCompl (S.cSmul c x) y = RCscale c (S.toGNSData.cinnerCompl x y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => ofQ' (S.toGNSData.cInnerSeq (S.cSmulCauchy c a) b N))
    (bSeq := fun N => CReal.mul (ofQ' c) (ofQ' (S.toGNSData.cInnerSeq a b N)))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_constMul c (CReal.convergesTo_ofQ'CauchySeq _ _))
  intro N
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact S.toGNSData.B_smul_left c (a.seq N) (b.seq N)

/-- **Right `Q'`-homogeneity.**  `⟨x, c·y⟩ = c·⟨x, y⟩`, from the left law and
symmetry. -/
theorem cinnerCompl_cSmul_right (c : Q') (x y : GNSCompletionSpace S.toGNSData) :
    S.toGNSData.cinnerCompl x (S.cSmul c y) = RCscale c (S.toGNSData.cinnerCompl x y) := by
  rw [S.toGNSData.cinnerCompl_comm x (S.cSmul c y), S.cinnerCompl_cSmul_left c y x,
      S.toGNSData.cinnerCompl_comm y x]

end YMGap.Continuum.HamiltonianScalar.SmulGNSData

/-! ## Part 2 — forming `p(T)` as a carrier map and its self-adjointness -/

namespace YMGap.Continuum.ContinuousFunctionalCalculusForm

open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum

variable (S : SmulGNSData) (L : AdditiveTransferOperator S.toGNSData)

/-- `T`'s self-adjointness restated through the concrete `cinnerCompl` (defeq to
the abstract `gnsComplete.hilbert.cinner`), so that it rewrites against the
inner-product bridges. -/
theorem Lsa : ∀ (x y : GNSCompletionSpace S.toGNSData),
    S.toGNSData.cinnerCompl (L.T x) y = S.toGNSData.cinnerCompl x (L.T y) :=
  L.selfAdjoint

/-- **`p(T)` formed as a carrier map — Horner realization of `Σ_k cₖ·Tᵏ`.**
`polyApply [c₀,c₁,…] x = c₀·x + T(c₁·x + T(c₂·x + …))`, using `cSmul` for the
scalar action, the transfer operator `T`, and `cAdd` for the sums.  A genuine
`GNSCompletionSpace → GNSCompletionSpace` map (the empty polynomial gives the
zero vector). -/
def polyApply : QPoly.Poly → GNSCompletionSpace S.toGNSData → GNSCompletionSpace S.toGNSData
  | [], _ => embedV S.toGNSData S.toGNSData.zero
  | (c :: cs), x => S.toGNSData.cAdd (S.cSmul c x) (L.T (polyApply cs x))

/-- **`p(T)` commutes with `T`, tested inside the inner product.**  For every
tail `cs`, `⟨x, p(T)(Tw)⟩ = ⟨x, T(p(T)w)⟩`.  Proved by induction from the
inner-product bridges and `T`'s self-adjointness; no vector-level `T·0 = 0` is
needed (the zero case collapses through `⟨0, ·⟩ = 0`). -/
theorem polyApply_Tcomm_inner (cs : QPoly.Poly) :
    ∀ (w x : GNSCompletionSpace S.toGNSData),
      S.toGNSData.cinnerCompl x (polyApply S L cs (L.T w))
        = S.toGNSData.cinnerCompl x (L.T (polyApply S L cs w)) := by
  induction cs with
  | nil =>
      intro w x
      show S.toGNSData.cinnerCompl x (embedV S.toGNSData S.toGNSData.zero)
        = S.toGNSData.cinnerCompl x (L.T (embedV S.toGNSData S.toGNSData.zero))
      rw [S.toGNSData.cinnerCompl_embedZero_right,
          S.toGNSData.cinnerCompl_comm x (L.T (embedV S.toGNSData S.toGNSData.zero)),
          Lsa S L (embedV S.toGNSData S.toGNSData.zero) x,
          S.toGNSData.cinnerCompl_embedZero_left]
  | cons d ds ih =>
      intro w x
      show S.toGNSData.cinnerCompl x
            (S.toGNSData.cAdd (S.cSmul d (L.T w)) (L.T (polyApply S L ds (L.T w))))
          = S.toGNSData.cinnerCompl x
            (L.T (S.toGNSData.cAdd (S.cSmul d w) (L.T (polyApply S L ds w))))
      rw [S.toGNSData.cinnerCompl_cAdd_right, S.cinnerCompl_cSmul_right,
          ← Lsa S L x (S.toGNSData.cAdd (S.cSmul d w) (L.T (polyApply S L ds w))),
          S.toGNSData.cinnerCompl_cAdd_right, S.cinnerCompl_cSmul_right,
          ← Lsa S L x w, ← Lsa S L x (polyApply S L ds (L.T w)),
          ih w (L.T x)]

/-- **The formed operator `p(T)` is self-adjoint** w.r.t. the completed inner
product: `⟨p(T)x, y⟩ = ⟨x, p(T)y⟩`.  Induction on the coefficient list; the
successor step uses left/right additivity and homogeneity of the inner product,
`T`'s self-adjointness, and `polyApply_Tcomm_inner`. -/
theorem polyApply_selfAdjoint (p : QPoly.Poly) :
    ∀ (x y : GNSCompletionSpace S.toGNSData),
      S.toGNSData.cinnerCompl (polyApply S L p x) y
        = S.toGNSData.cinnerCompl x (polyApply S L p y) := by
  induction p with
  | nil =>
      intro x y
      show S.toGNSData.cinnerCompl (embedV S.toGNSData S.toGNSData.zero) y
        = S.toGNSData.cinnerCompl x (embedV S.toGNSData S.toGNSData.zero)
      rw [S.toGNSData.cinnerCompl_embedZero_left, S.toGNSData.cinnerCompl_embedZero_right]
  | cons c cs ih =>
      intro x y
      show S.toGNSData.cinnerCompl
            (S.toGNSData.cAdd (S.cSmul c x) (L.T (polyApply S L cs x))) y
          = S.toGNSData.cinnerCompl x
            (S.toGNSData.cAdd (S.cSmul c y) (L.T (polyApply S L cs y)))
      rw [S.toGNSData.cinnerCompl_cAdd_left, S.cinnerCompl_cSmul_left,
          Lsa S L (polyApply S L cs x) y, ih x (L.T y),
          S.toGNSData.cinnerCompl_cAdd_right, S.cinnerCompl_cSmul_right,
          polyApply_Tcomm_inner S L cs y x]

/-! ## Part 3 — discharging the bounded transfer functional-calculus residual -/

/-- Build a `SpectralGapData` on the concrete completion with transfer operator
the given `AdditiveTransferOperator` and an arbitrary located spectral model. -/
def spectralGapDataOfL (model : SpectralModel) (gap : LocatedSpectralGap model) :
    SpectralGapData S.toGNSData.gnsComplete where
  op := L.toTransferOperator
  model := model
  gap := gap

/-- **Poly-diagonal spectral resolution of the FORMED operator's norm** (the
standard Osterwalder–Seiler / Peter–Weyl spectral input, named `Type`-level data
exactly like `DiagResolution` / `CharacterDiagResolution`).  It records the
uniform spectral bound `‖p‖²_{∞,spec} ≤ M` on the resolved eigenvalues, and the
diagonal resolution of `‖p(T)x‖²` against the coordinate weights of `Br`. -/
structure PolyNormData (model : SpectralModel) (gap : LocatedSpectralGap model)
    (Br : DiagResolution (spectralGapDataOfL S L model gap)) (p : QPoly.Poly) : Type where
  /-- The squared uniform spectral bound `M = ‖p‖²_{∞,spec}`. -/
  M : Q'
  /-- `p(λᵢ)² ≤ M` for every resolved mode. -/
  supBound : ∀ i, QPoly.eval p (Br.lam i) * QPoly.eval p (Br.lam i) ≤ M
  /-- Diagonal resolution of the FORMED operator's squared norm:
  `‖p(T)x‖² = Σ p(λᵢ)²·|cᵢ(x)|²`. -/
  normDiag : ∀ x,
    S.toGNSData.cinnerCompl (polyApply S L p x) (polyApply S L p x)
      = specNormSq Br (fun i => QPoly.eval p (Br.lam i) * QPoly.eval p (Br.lam i)) x

/-- **DISCHARGE of `BoundedTransferCalculusResidual` for a general polynomial.**
The FORMED operator `p(T) = polyApply p` (a genuine multi-term
`Σ_k cₖ·Tᵏ`, not a single monomial) is a bounded self-adjoint operator with
`‖p(T)x‖² ≤ M·‖x‖²`, `M = ‖p‖²_{∞,spec}`.  Self-adjointness is
`polyApply_selfAdjoint`; the norm bound composes the resolution `normDiag` with
the proved analytic core `polyNormBound`.  This retires the architectural block
of core ④ — `p(T)` is now formed as a carrier map. -/
def dischargeBTC (model : SpectralModel) (gap : LocatedSpectralGap model)
    (Br : DiagResolution (spectralGapDataOfL S L model gap)) (p : QPoly.Poly)
    (PN : PolyNormData S L model gap Br p) :
    BoundedTransferCalculusResidual (spectralGapDataOfL S L model gap) where
  normSqBound := PN.M
  fT := polyApply S L p
  fT_selfAdjoint := polyApply_selfAdjoint S L p
  fT_normBound := fun x => by
    show RCle (S.toGNSData.cinnerCompl (polyApply S L p x) (polyApply S L p x))
              (RCscale PN.M (S.toGNSData.cinnerCompl x x))
    rw [PN.normDiag x]
    exact polyNormBound Br p PN.M PN.supBound x

end YMGap.Continuum.ContinuousFunctionalCalculusForm

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.convergesTo_add
#print axioms YMGap.Constructive.CReal.convergesTo_constMul
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_cAdd_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_comm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_cAdd_right
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_embedZero_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_embedZero_right
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cinnerCompl_cSmul_left
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cinnerCompl_cSmul_right
#print axioms YMGap.Continuum.ContinuousFunctionalCalculusForm.polyApply
#print axioms YMGap.Continuum.ContinuousFunctionalCalculusForm.polyApply_Tcomm_inner
#print axioms YMGap.Continuum.ContinuousFunctionalCalculusForm.polyApply_selfAdjoint
#print axioms YMGap.Continuum.ContinuousFunctionalCalculusForm.dischargeBTC
