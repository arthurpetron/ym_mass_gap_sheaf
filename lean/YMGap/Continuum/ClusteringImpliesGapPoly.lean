/-
Clustering ⇒ spectral gap with a POLYNOMIAL prefactor, family form, and two
negative controls.  Status: infrastructure, not gap evidence; U(1)-true.

# Contents

* `clustering_poly_implies_coupled_le` — if `corr S n ≤ C·(n+1)^p·μ^n` for all
  `n`, every coupled mode (`wᵢ > 0`, `i < k`) satisfies `λᵢ ≤ μ`.  This is the
  polynomial-prefactor version of
  `ClusteringImpliesGap.clustering_implies_coupled_le`.  The proof absorbs
  `(n+1)^p` into a slightly larger exponential (`PolyEnvelope`): for every
  `d > 0` there are explicit `A, B > 0` with `A·(n+1)^p·μ^n ≤ B·(μ+d)^n`.  The
  exponential converse is then run at the intermediate rate `μ + d/2`.
* `family_clustering_implies_gapBound` — a family of observables (spectral
  models sharing `k` and `lam` with a reference model `S`) with a COMMON rate
  `μ`, whose coupled modes cover every live mode (the cover is given as data),
  plus the base file's unused-slot bound `hdead`, gives `SpectralGapBound S μ`.
  `family_clustering_implies_located` packages this as `LocatedSpectralGap S`
  when `μ < 1`.
* Negative control (a): `missObs_counterexample`.  An observable that misses
  the slow mode clusters at the fast rate `1/2`, satisfies `hdead`, and still
  `¬ SpectralGapBound missObs (1/2)`.  So the covering hypothesis is necessary.
* Negative control (b): the toy `ρ(a) = 1 − a²`.  Proved: `a² + ρ(a) ≃ 1`, so the
  per-lattice gap `1 − ρ(a) = a² > 0` for `a > 0`; and `1 ≤ ε·a + ρ(a)` whenever
  `0 ≤ a ≤ ε`, i.e. `(1 − ρ(a))/a ≤ ε` with modulus `a₀(ε) = ε`.  This is the
  division- and subtraction-free surrogate for `−log ρ(a)/a → 0`; the
  logarithmic statement itself is NOT formalized here (it would follow from the
  elementary `−log ρ ≤ (1 − ρ)/ρ`, which is not proved in this module).

# Scope (no overstatement)

Abstract finite `SpectralModel` level only, exactly like the base file.
Connecting `corr` to a Wilson correlator, and producing the cover for 4D
Yang–Mills observables, are separate open obligations.  Every hypothesis here is
satisfiable by U(1) / free-field spectral data, so nothing in this module is
evidence for a non-abelian mass gap.  No frontier bundle is touched.

Axiom gate: `propext` / `Quot.sound` only (checked out of tree).
-/

import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.ClusteringImpliesGapPoly

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap

/-! ## Small helpers -/

/-- The rational `1/2`. -/
def hlf : Q' := Q'.mkPos 1 2 (by decide)

theorem hlf_pos : (0 : Q') < hlf := by decide

theorem hlf_add_hlf : (hlf + hlf).eqv (1 : Q') := by decide

/-- `d·½ + d·½ ≃ d`. -/
theorem halves_eqv (d : Q') : (d * hlf + d * hlf).eqv d :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv d hlf hlf))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left d _ 1 hlf_add_hlf) (Q'.mul_one_eqv d))

/-- `0 ≤ μ → 0 < d → 0 < μ + d`. -/
theorem add_pos_of_nonneg_of_pos {μ d : Q'} (hμ : (0 : Q') ≤ μ) (hd : (0 : Q') < d) :
    (0 : Q') < μ + d :=
  ClusteringImpliesGap.lt_of_lt_of_le hd
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg d μ hμ) (Q'.le_of_eqv (Q'.add_comm_eqv d μ)))

/-- `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem mul4_eqv (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (ClusteringImpliesGap.mul_comm_assoc b c d))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))))

/-- Base monotonicity of powers: `0 ≤ a ≤ b → aⁿ ≤ bⁿ`. -/
theorem pow_le_pow_of_base {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => by
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | n + 1 => by
      show a * a ^ n ≤ b * b ^ n
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ a (pow_le_pow_of_base ha hab n) ha)
        (Q'.mul_le_mul_of_nonneg_right _ _ (b ^ n) hab
          (Q'.pow_nonneg b (Q'.le_trans' _ _ _ ha hab) n))

/-- `0·y ≃ 0`. -/
theorem zero_mul_eqv' (y : Q') : ((0 : Q') * y).eqv 0 := by
  show ((0 : Int) * y.num) * ((0 : Q').den : Int) = (0 : Int) * (((0 : Q') * y).den : Int)
  rw [Int.zero_mul, Int.zero_mul, Int.zero_mul]

/-! ## Polynomial prefactor ⇒ slightly larger exponential -/

/-- **Linear envelope.**  `e·((n+1)·μⁿ) ≤ (μ+e)·(μ+e)ⁿ` (Bernoulli, division-free). -/
theorem linear_envelope (μ e : Q') (hμ : (0 : Q') ≤ μ) (he : (0 : Q') ≤ e) (n : Nat) :
    e * (Q'.ofNat (n + 1) * μ ^ n) ≤ (μ + e) * (μ + e) ^ n :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ClusteringImpliesGap.mul_comm_assoc e (Q'.ofNat (n + 1)) (μ ^ n)))
    (ClusteringImpliesGap.pow_ge_linear μ e hμ he n)

/-- Witness-bearing envelope (Rule 2): explicit `A, B > 0` with
`A·(n+1)^p·μⁿ ≤ B·(μ+d)ⁿ` for every `n`. -/
structure PolyEnvelope (p : Nat) (μ d : Q') : Type where
  A : Q'
  B : Q'
  A_pos : (0 : Q') < A
  B_pos : (0 : Q') < B
  bound : ∀ n : Nat, A * (Q'.ofNat (n + 1) ^ p * μ ^ n) ≤ B * (μ + d) ^ n

/-- Inductive step of the envelope: one extra factor `(n+1)` costs the step
from `μ + h` to `(μ + h) + h ≃ D`, with constants `h·A` and `B·D`. -/
theorem envelope_step (p : Nat) (μ h D A B : Q') (hμ : (0 : Q') ≤ μ) (hh : (0 : Q') < h)
    (hB : (0 : Q') ≤ B) (hZ : ((μ + h) + h).eqv D)
    (hbound : ∀ n : Nat, A * (Q'.ofNat (n + 1) ^ p * μ ^ n) ≤ B * (μ + h) ^ n) (n : Nat) :
    (h * A) * (Q'.ofNat (n + 1) ^ (p + 1) * μ ^ n) ≤ (B * D) * D ^ n := by
  show (h * A) * ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1) ^ p) * μ ^ n) ≤ (B * D) * D ^ n
  have hN : (0 : Q') ≤ Q'.ofNat (n + 1) := Q'.le_of_lt (Q'.ofNat_succ_pos n)
  have e1 := Q'.mul_eqv_congr_left (h * A) _ _
    (Q'.mul_assoc_eqv (Q'.ofNat (n + 1)) (Q'.ofNat (n + 1) ^ p) (μ ^ n))
  have e2 := mul4_eqv h A (Q'.ofNat (n + 1)) (Q'.ofNat (n + 1) ^ p * μ ^ n)
  have s3 := Q'.mul_le_mul_of_nonneg_left _ _ (h * Q'.ofNat (n + 1)) (hbound n)
    (Q'.mul_nonneg h _ (Q'.le_of_lt hh) hN)
  have e4 : ((h * Q'.ofNat (n + 1)) * (B * (μ + h) ^ n)).eqv
      (B * (h * (Q'.ofNat (n + 1) * (μ + h) ^ n))) :=
    Q'.eqv_trans _ _ _ (mul4_eqv h (Q'.ofNat (n + 1)) B ((μ + h) ^ n))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (h * B) (B * h) _ (Q'.mul_comm_eqv h B))
        (Q'.mul_assoc_eqv B h _))
  have s5 := Q'.mul_le_mul_of_nonneg_left _ _ B
    (linear_envelope (μ + h) h (Q'.zero_le_add μ h hμ (Q'.le_of_lt hh)) (Q'.le_of_lt hh) n) hB
  have e6 : (B * (((μ + h) + h) * ((μ + h) + h) ^ n)).eqv ((B * D) * D ^ n) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left B _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ D _ hZ)
          (Q'.mul_eqv_congr_left D _ _ (ClusteringImpliesGap.pow_eqv_congr _ D hZ n))))
      (Q'.eqv_symm (Q'.mul_assoc_eqv B D (D ^ n)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ e1 e2))
    (Q'.le_trans' _ _ _ s3 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e4)
      (Q'.le_trans' _ _ _ s5 (Q'.le_of_eqv e6))))

/-- **Polynomial envelope (witness-bearing).**  Recursion on the degree `p`,
halving the rate excess at each step. -/
def polyEnvelope : (p : Nat) → (μ d : Q') → (0 : Q') ≤ μ → (0 : Q') < d → PolyEnvelope p μ d
  | 0, μ, d, hμ, hd =>
    { A := 1, B := 1, A_pos := by decide, B_pos := by decide,
      bound := fun n => by
        show (1 : Q') * ((1 : Q') * μ ^ n) ≤ (1 : Q') * (μ + d) ^ n
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)))
          (Q'.le_trans' _ _ _
            (pow_le_pow_of_base hμ (Q'.add_le_self_of_nonneg μ d (Q'.le_of_lt hd)) n)
            (Q'.ge_of_eqv (Q'.one_mul_eqv _))) }
  | p + 1, μ, d, hμ, hd =>
    let E := polyEnvelope p μ (d * hlf) hμ (Q'.mul_pos hd hlf_pos)
    { A := (d * hlf) * E.A, B := E.B * (μ + d),
      A_pos := Q'.mul_pos (Q'.mul_pos hd hlf_pos) E.A_pos,
      B_pos := Q'.mul_pos E.B_pos (add_pos_of_nonneg_of_pos hμ hd),
      bound := envelope_step p μ (d * hlf) (μ + d) E.A E.B hμ (Q'.mul_pos hd hlf_pos)
        (Q'.le_of_lt E.B_pos)
        (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv μ _ _)
          (Q'.add_eqv_congr_left μ _ _ (halves_eqv d)))
        E.bound }

/-! ## (1) Polynomial clustering ⇒ coupled-mode bound -/

/-- **Polynomial clustering ⇒ coupled-mode bound.**  If
`corr S n ≤ C·(n+1)^p·μⁿ` for all `n` (`C, μ > 0`), every coupled live mode
satisfies `λᵢ ≤ μ`. -/
theorem clustering_poly_implies_coupled_le
    (S : SpectralModel) (C μ : Q') (p : Nat) (hC : (0 : Q') < C) (hμ : (0 : Q') < μ)
    (hcluster : ∀ n, corr S n ≤ C * (Q'.ofNat (n + 1) ^ p * μ ^ n)) :
    ∀ i, i < S.k → (0 : Q') < S.w i → S.lam i ≤ μ := by
  intro j hj hwj
  by_cases hle : S.lam j ≤ μ
  · exact hle
  · exfalso
    have hlt : μ < S.lam j := by
      show μ.num * ((S.lam j).den : Int) < (S.lam j).num * (μ.den : Int)
      have h' : ¬ ((S.lam j).num * (μ.den : Int) ≤ μ.num * ((S.lam j).den : Int)) := hle
      exact Int.not_le.mp h'
    let d : Q' := S.lam j - μ
    have hdpos : (0 : Q') < d := ClusteringImpliesGap.sub_pos_of_lt hlt
    let h : Q' := d * hlf
    have hh : (0 : Q') < h := Q'.mul_pos hdpos hlf_pos
    let E := polyEnvelope p μ h (Q'.le_of_lt hμ) hh
    have hAw : (0 : Q') < E.A * S.w j := Q'.mul_pos E.A_pos hwj
    obtain ⟨n, hn⟩ := ClusteringImpliesGap.term_exceeds_envelope (E.A * S.w j) (C * E.B)
      (μ + h) h hAw (Q'.mul_pos hC E.B_pos) (add_pos_of_nonneg_of_pos (Q'.le_of_lt hμ) hh) hh
    have hZ : ((μ + h) + h).eqv (S.lam j) :=
      Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv μ h h)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left μ _ _ (halves_eqv d))
          (Q'.eqv_symm (Q'.add_sub_cancel_eqv (S.lam j) μ)))
    have lo : (E.A * S.w j) * ((μ + h) + h) ^ n ≤ (E.A * S.w j) * (S.lam j) ^ n :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_of_eqv (ClusteringImpliesGap.pow_eqv_congr _ _ hZ n)) (Q'.le_of_lt hAw)
    have up1 : (E.A * S.w j) * (S.lam j) ^ n ≤ E.A * corr S n :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ E.A
          (ClusteringImpliesGap.corr_ge_term S n j hj) (Q'.le_of_lt E.A_pos))
    have up2 := Q'.mul_le_mul_of_nonneg_left _ _ E.A (hcluster n) (Q'.le_of_lt E.A_pos)
    have up3 : E.A * (C * (Q'.ofNat (n + 1) ^ p * μ ^ n)) ≤ C * (E.B * (μ + h) ^ n) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (ClusteringImpliesGap.mul_comm_assoc _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ C (E.bound n) (Q'.le_of_lt hC))
    have up4 : C * (E.B * (μ + h) ^ n) ≤ (C * E.B) * (μ + h) ^ n :=
      Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)
    have hcontr : (C * E.B) * (μ + h) ^ n < (C * E.B) * (μ + h) ^ n :=
      ClusteringImpliesGap.lt_of_lt_of_le hn
        (Q'.le_trans' _ _ _ lo (Q'.le_trans' _ _ _ up1
          (Q'.le_trans' _ _ _ up2 (Q'.le_trans' _ _ _ up3 up4))))
    exact ClusteringImpliesGap.lt_irrefl' _ hcontr

/-! ## (2) Family clustering ⇒ gap bound -/

/-- **Family clustering ⇒ `SpectralGapBound`.**  Observables `obs a` share the
spectrum (`k`, `lam`) of `S`; each clusters polynomially at the COMMON rate
`μ`; `cover` names, for every live mode, an observable coupled to it; `hdead`
bounds the unused slots exactly as in `clustering_implies_gapBound`. -/
theorem family_clustering_implies_gapBound
    (S : SpectralModel) {ι : Type} (obs : ι → SpectralModel)
    (hk : ∀ a, (obs a).k = S.k) (hlam : ∀ a i, (obs a).lam i = S.lam i)
    (C : ι → Q') (p : ι → Nat) (μ : Q') (hC : ∀ a, (0 : Q') < C a) (hμ : (0 : Q') < μ)
    (hcluster : ∀ a n, corr (obs a) n ≤ C a * (Q'.ofNat (n + 1) ^ p a * μ ^ n))
    (cover : (i : Nat) → i < S.k → ι)
    (hcover : ∀ i (hi : i < S.k), (0 : Q') < (obs (cover i hi)).w i)
    (hdead : ∀ i, S.k ≤ i → S.lam i ≤ μ) :
    SpectralGapBound S μ := by
  intro i
  by_cases hik : i < S.k
  · have hik' : i < (obs (cover i hik)).k := by rw [hk]; exact hik
    have hb := clustering_poly_implies_coupled_le (obs (cover i hik)) (C (cover i hik)) μ
      (p (cover i hik)) (hC _) hμ (hcluster _) i hik' (hcover i hik)
    rw [hlam] at hb
    exact hb
  · exact hdead i (Nat.not_lt.mp hik)

/-- **Corollary (`μ < 1`): family clustering ⇒ located spectral gap, `sep = μ`.** -/
def family_clustering_implies_located
    (S : SpectralModel) {ι : Type} (obs : ι → SpectralModel)
    (hk : ∀ a, (obs a).k = S.k) (hlam : ∀ a i, (obs a).lam i = S.lam i)
    (C : ι → Q') (p : ι → Nat) (μ : Q') (hC : ∀ a, (0 : Q') < C a) (hμ : (0 : Q') < μ)
    (hμ1 : μ < (1 : Q'))
    (hcluster : ∀ a n, corr (obs a) n ≤ C a * (Q'.ofNat (n + 1) ^ p a * μ ^ n))
    (cover : (i : Nat) → i < S.k → ι)
    (hcover : ∀ i (hi : i < S.k), (0 : Q') < (obs (cover i hi)).w i)
    (hdead : ∀ i, S.k ≤ i → S.lam i ≤ μ) :
    LocatedSpectralGap S where
  sep := μ
  sep_lt_one := hμ1
  bound := family_clustering_implies_gapBound S obs hk hlam C p μ hC hμ hcluster
    cover hcover hdead

/-! ## (3a) Negative control: an observable that misses the slow mode -/

/-- Two live modes: fast `1/2` (index 0) and slow `9/10` (index 1); unused slots `0`. -/
def twoLam : QSeq
  | 0 => hlf
  | 1 => Q'.mkPos 9 10 (by decide)
  | _ + 2 => 0

/-- Weights of an observable coupled ONLY to the fast mode. -/
def missW : QSeq
  | 0 => 1
  | _ + 1 => 0

/-- The slow-mode-missing observable. -/
def missObs : SpectralModel where
  k := 2
  w := missW
  lam := twoLam
  w_nonneg := fun i => match i with
    | 0 => by decide
    | _ + 1 => Q'.le_refl' 0
  lam_nonneg := fun i => match i with
    | 0 => by decide
    | 1 => by decide
    | _ + 2 => Q'.le_refl' 0

/-- **Negative control (a).**  `missObs` clusters at rate `1/2` (degree 0,
`C = 1`), satisfies `hdead` at `1/2`, does NOT couple to live mode 1, and the gap
bound at `1/2` FAILS: rate-bounds from observables that miss a mode say nothing
about it, so the cover hypothesis of `family_clustering_implies_gapBound` is
necessary. -/
theorem missObs_counterexample :
    (∀ n, corr missObs n ≤ 1 * (Q'.ofNat (n + 1) ^ 0 * hlf ^ n)) ∧
    (∀ i, missObs.k ≤ i → missObs.lam i ≤ hlf) ∧
    ¬ ((0 : Q') < missObs.w 1) ∧
    ¬ SpectralGapBound missObs hlf := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro n
    show ((0 : Q') + (1 : Q') * hlf ^ n) + (0 : Q') * (Q'.mkPos 9 10 (by decide)) ^ n
      ≤ (1 : Q') * ((1 : Q') * hlf ^ n)
    have e : (((0 : Q') + (1 : Q') * hlf ^ n) + (0 : Q') * (Q'.mkPos 9 10 (by decide)) ^ n).eqv
        ((1 : Q') * ((1 : Q') * hlf ^ n)) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (zero_mul_eqv' _))
        (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
          (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
            (Q'.mul_eqv_congr_left 1 _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)))))
    exact Q'.le_of_eqv e
  · intro i hi
    match i, hi with
    | _ + 2, _ => show (0 : Q') ≤ hlf; decide
  · intro h
    have h1 : Q'.mkPos 9 10 (by decide) ≤ hlf := h 1
    exact absurd h1 (by decide)

/-! ## (3b) Negative control: `ρ(a) = 1 − a²` (per-spacing gap vanishes) -/

/-- The toy transfer eigenvalue at lattice spacing `a`. -/
def rhoToy (a : Q') : Q' := 1 - a * a

/-- Exact identity `a² + ρ(a) ≃ 1`: the per-lattice gap `1 − ρ(a)` is `a²`. -/
theorem rhoToy_add_sq (a : Q') : (a * a + rhoToy a).eqv 1 :=
  Q'.eqv_symm (Q'.add_sub_cancel_eqv 1 (a * a))

/-- The per-lattice gap `a²` is strictly positive for every `a > 0`. -/
theorem rhoToy_lattice_gap_pos (a : Q') (ha : (0 : Q') < a) : (0 : Q') < a * a :=
  Q'.mul_pos ha ha

/-- **Negative control (b).**  `1 ≤ ε·a + ρ(a)` whenever `0 ≤ a ≤ ε`, i.e.
`(1 − ρ(a))/a ≤ ε` with explicit modulus `a₀(ε) = ε`: the gap per unit lattice
spacing tends to `0`, although every lattice gap is positive.  (Surrogate for
`−log ρ(a)/a → 0`; the logarithmic form is not formalized here.) -/
theorem rhoToy_gap_per_spacing_le (ε a : Q') (ha : (0 : Q') ≤ a) (haε : a ≤ ε) :
    (1 : Q') ≤ ε * a + rhoToy a :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (rhoToy_add_sq a))
    (Q'.add_le_add_right (a * a) (ε * a) (rhoToy a)
      (Q'.mul_le_mul_of_nonneg_right a ε a haε ha))

end YMGap.Continuum.ClusteringImpliesGapPoly
