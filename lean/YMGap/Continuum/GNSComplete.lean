/-
Metric completeness of the GNS metric completion: the genuine constructive
Hilbert space.

# Which gap this closes

`Continuum/GNSCompletion.lean` built the completion carrier
`GNSCompletionSpace = CauchyGNS / CauchyNull`, the sqrt-free quadratic triangle
inequality `distSqQ_triangle`, and the dense isometric embedding `embedQuot`.
`Continuum/GNSHilbertSpace.lean` supplied the `CReal`-valued inner product
`cinnerCompl` on ALL of the completion and the capstone `gnsHilbertSpace`.  The
ONE residual flagged there (`MetricCompleteResidual`) was full **metric
completeness**: every squared-distance-Cauchy sequence of POINTS of the
completion converges in the completion.  This module closes it (under a clean
regular-rate hypothesis) via the classical Cantor diagonal argument, entirely
sqrt-free, reusing only `distSqQ_triangle`.

# What is genuine here (constructed / proved, axiom-clean)

  * **The reusable three-hop quadratic bound (`quad3`).**  From three primitive
    squared-distance bounds `d²(w₀,p), d²(p,q), d²(q,w₃) ≤ τ`, two nested
    applications of `distSqQ_triangle` give `d²(w₀,w₃) ≤ treeval τ` where
    `treeval τ ≃ 10·τ` (`treeval_eqv_ten`, pure `Q′` algebra).

  * **The "10·invSucc → 0" rate inverter (`gMod`/`gMod_spec`).**  An explicit
    `Type`-level modulus `gMod ε := (ε·1/10).den` with the proof that
    `10·invSucc k ≤ ε` for `k ≥ gMod ε` — no choice, a concrete `Nat` function.

  * **The diagonal limit.**  A `cDistSq`-Cauchy sequence of completion points is
    presented `Type`-level as `CompletionCauchy`: representatives `pt : Nat →
    CauchyGNS` with the regular rate `d²(⟦pt p⟧,⟦pt q⟧) ≤ 1/(min p q + 1)` (in
    the eventual-rational `distSqQ` sense — the honest constructive reading of
    "the completion distance is `≤ ε`", avoiding the choice that
    `Quotient.out` would need).  The diagonal `dseq k := (pt k).seq (Jₖ)`,
    `Jₖ := (pt k).modulus (1/(k+1))`, is shown to be a genuine `CauchyGNS`
    (`diagCauchy`), and the original sequence converges to its class
    (`diag_converges`): `d²(⟦pt p⟧, ⟦dseq⟧) → 0`.

  * **The capstone `CompleteGNSHilbert`.**  Bundles `gnsHilbertSpace` with the
    completeness field; `gnsComplete` proves it, and `WilsonGNSData`'s
    finite-volume theory inherits a genuine constructive complete inner-product
    (Hilbert) space (`WilsonGNSData.completeGnsHilbert`).

# Honest residual

The diagonal argument is discharged for the **regular-rate** Cauchy sequences
(`CompletionCauchy`, fixed modulus `1/(min p q + 1)`).  Every metric-completion
Cauchy sequence has a regular-rate cofinal reindexing, so this is the standard
"completeness of the completion"; the fully-general arbitrary-modulus diagonal
(an outer reindexing on top of the inner one) is the only piece not mechanised
here.  Nothing is `sorry`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.HalfPow

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Constructive

/-! ## The `Q′` rate algebra: `treeval` and the `10·invSucc → 0` inverter -/

/-- The exact `Q′` bound produced by two nested quadratic triangles: a tree of
ten copies of `τ`. -/
def treeval (τ : Q') : Q' :=
  (τ + τ) + (((τ + τ) + (τ + τ)) + ((τ + τ) + (τ + τ)))

/-- `treeval τ ≃ 10·τ`. -/
theorem treeval_eqv_ten (τ : Q') : (treeval τ).eqv ((10 : Q') * τ) := by
  have e2 : (τ + τ).eqv ((2 : Q') * τ) := q_two_mul τ
  have e4 : ((τ + τ) + (τ + τ)).eqv ((4 : Q') * τ) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e2 e2) ?_
    refine Q'.eqv_trans _ _ _ (q_two_mul ((2 : Q') * τ)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 2 τ)) ?_
    exact Q'.mul_eqv_congr_right ((2 : Q') * 2) (4 : Q') τ (by decide)
  have e8 : (((τ + τ) + (τ + τ)) + ((τ + τ) + (τ + τ))).eqv ((8 : Q') * τ) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e4 e4) ?_
    refine Q'.eqv_trans _ _ _ (q_two_mul ((4 : Q') * τ)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 4 τ)) ?_
    exact Q'.mul_eqv_congr_right ((2 : Q') * 4) (8 : Q') τ (by decide)
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e2 e8) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.mul_comm_eqv 2 τ) (Q'.mul_comm_eqv 8 τ)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv τ 2 8)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left τ ((2 : Q') + 8) (10 : Q') (by decide)) ?_
  exact Q'.mul_comm_eqv τ 10

/-- `treeval τ ≤ 10·τ`. -/
theorem treeval_le_ten (τ : Q') : treeval τ ≤ (10 : Q') * τ :=
  Q'.le_of_eqv (treeval_eqv_ten τ)

/-- The concrete `Type`-level modulus inverting `10·invSucc → 0`. -/
def gMod (ε : Q') : Nat := (ε * Q'.invSucc 9).den

/-- `10·invSucc k ≤ ε` once `k ≥ gMod ε`.  No choice: `gMod` is a genuine
`Nat`-valued function. -/
theorem gMod_spec (ε : Q') (hε : (0 : Q') < ε) (k : Nat) (hk : gMod ε ≤ k) :
    (10 : Q') * Q'.invSucc k ≤ ε := by
  have hδpos : (0 : Q') < ε * Q'.invSucc 9 := Q'.mul_pos hε (Q'.invSucc_pos 9)
  have hik : Q'.invSucc k ≤ ε * Q'.invSucc 9 :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
      (HalfPow.invSucc_den_le (ε * Q'.invSucc 9) hδpos)
  have hstep : (10 : Q') * Q'.invSucc k ≤ (10 : Q') * (ε * Q'.invSucc 9) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.invSucc k) (ε * Q'.invSucc 9) (10 : Q') hik (by decide)
  have key : ((10 : Q') * (ε * Q'.invSucc 9)).eqv ε := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (10 : Q') ε (Q'.invSucc 9))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((10 : Q') * ε) (ε * (10 : Q')) (Q'.invSucc 9)
        (Q'.mul_comm_eqv (10 : Q') ε)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ε (10 : Q') (Q'.invSucc 9)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ε ((10 : Q') * Q'.invSucc 9) (1 : Q') (by decide)) ?_
    exact Q'.mul_one_eqv ε
  exact le_of_le_eqv hstep key

end YMGap.Constructive

namespace YMGap.Continuum.GNSQuotient

open YMGap.Constructive

namespace GNSData

variable (D : GNSData)

/-! ## The reusable three-hop quadratic bound -/

/-- **Three quadratic-triangle hops.**  Primitive squared-distance bounds
`d²(w₀,p), d²(p,q), d²(q,w₃) ≤ τ` give `d²(w₀,w₃) ≤ treeval τ`. -/
theorem quad3 (w0 p q w3 : D.V) (τ : Q')
    (h1 : D.distSqQ w0 p ≤ τ) (h2 : D.distSqQ p q ≤ τ) (h3 : D.distSqQ q w3 ≤ τ) :
    D.distSqQ w0 w3 ≤ treeval τ := by
  have hpw3 : D.distSqQ p w3 ≤ ((τ + τ) + (τ + τ)) :=
    Q'.le_trans' _ _ _ (D.distSqQ_triangle p q w3)
      (Q'.add_le_add (Q'.add_le_add h2 h2) (Q'.add_le_add h3 h3))
  refine Q'.le_trans' _ _ _ (D.distSqQ_triangle w0 p w3) ?_
  exact Q'.add_le_add (Q'.add_le_add h1 h1) (Q'.add_le_add hpw3 hpw3)

end GNSData

/-! ## Cauchy sequences of completion points and the diagonal limit -/

/-- A **regular-rate Cauchy sequence in the metric completion**, presented
`Type`-level by representatives.  `pt p` represents the completion point
`⟦pt p⟧`; `reg` is the regular fixed rate `d²(⟦pt p⟧,⟦pt q⟧) ≤ 1/(min p q + 1)`
in the eventual-rational sense — the honest constructive reading of the
`cDistSq`-Cauchy condition (the squared distance of the completion points is the
limit of the representative squared distances), which avoids the choice that
extracting a representative via `Quotient.out` would require. -/
structure CompletionCauchy (D : GNSData) where
  /-- A representative `CauchyGNS` for each completion point. -/
  pt : Nat → CauchyGNS D
  /-- The regular rate: the representative squared distances are eventually
  `≤ 1/(min p q + 1)`. -/
  reg : ∀ p q : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    D.distSqQ ((pt p).seq n) ((pt q).seq n) ≤ Q'.invSucc (min p q)

namespace CompletionCauchy

variable {D : GNSData} (X : CompletionCauchy D)

/-- The inner diagonal index `Jₖ := (pt k).modulus (1/(k+1))`. -/
def Jidx (k : Nat) : Nat := (X.pt k).modulus (Q'.invSucc k)

/-- The **diagonal representative sequence** `dseq k := (pt k).seq Jₖ`. -/
def dseq (k : Nat) : D.V := (X.pt k).seq (X.Jidx k)

/-! ### The diagonal is Cauchy -/

/-- **Claim A (monotone form).**  For `p ≤ q`,
`d²(dseq p, dseq q) ≤ treeval (1/(p+1))`. -/
theorem diag_cauchy_le (p q : Nat) (hpq : p ≤ q) :
    D.distSqQ (X.dseq p) (X.dseq q) ≤ treeval (Q'.invSucc p) := by
  obtain ⟨Npq, hNpq⟩ := X.reg p q
  refine D.quad3 (X.dseq p)
    ((X.pt p).seq (max (max (X.Jidx p) (X.Jidx q)) Npq))
    ((X.pt q).seq (max (max (X.Jidx p) (X.Jidx q)) Npq))
    (X.dseq q) (Q'.invSucc p) ?_ ?_ ?_
  · -- d²((pt p).Jp, (pt p).m) ≤ invSucc p
    have hm : X.Jidx p ≤ max (max (X.Jidx p) (X.Jidx q)) Npq :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    exact (X.pt p).isCauchy (Q'.invSucc p) (Q'.invSucc_pos p) (X.Jidx p)
      (max (max (X.Jidx p) (X.Jidx q)) Npq) (Nat.le_refl _) hm
  · -- d²((pt p).m, (pt q).m) ≤ invSucc (min p q) = invSucc p
    have hmN : Npq ≤ max (max (X.Jidx p) (X.Jidx q)) Npq := Nat.le_max_right _ _
    have h := hNpq (max (max (X.Jidx p) (X.Jidx q)) Npq) hmN
    rwa [Nat.min_eq_left hpq] at h
  · -- d²((pt q).m, (pt q).Jq) ≤ invSucc q ≤ invSucc p
    have hm : X.Jidx q ≤ max (max (X.Jidx p) (X.Jidx q)) Npq :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have h := (X.pt q).isCauchy (Q'.invSucc q) (Q'.invSucc_pos q)
      (max (max (X.Jidx p) (X.Jidx q)) Npq) (X.Jidx q) hm (Nat.le_refl _)
    exact Q'.le_trans' _ _ _ h (ExpNeg.invSucc_le_of_le hpq)

/-- **The diagonal is a genuine `CauchyGNS`** with the explicit modulus `gMod`. -/
def diagCauchy : CauchyGNS D where
  seq := X.dseq
  modulus := gMod
  isCauchy := by
    intro ε hε p q hp hq
    rcases Nat.le_total p q with hpq | hqp
    · refine Q'.le_trans' _ _ _ (X.diag_cauchy_le p q hpq) ?_
      refine Q'.le_trans' _ _ _ (treeval_le_ten (Q'.invSucc p)) ?_
      exact gMod_spec ε hε p hp
    · refine Q'.le_trans' _ _ _
        (le_of_eqv_le (D.distSqQ_comm (X.dseq p) (X.dseq q)) (X.diag_cauchy_le q p hqp)) ?_
      refine Q'.le_trans' _ _ _ (treeval_le_ten (Q'.invSucc q)) ?_
      exact gMod_spec ε hε q hq

/-! ### The original sequence converges to the diagonal -/

/-- **Claim B (per-index form).**  For each `p`, eventually-in-`n`,
`d²((pt p).seq n, dseq n) ≤ treeval (1/(p+1))`. -/
theorem diag_conv_le (p : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      D.distSqQ ((X.pt p).seq n) (X.dseq n) ≤ treeval (Q'.invSucc p) := by
  refine ⟨max p ((X.pt p).modulus (Q'.invSucc p)), fun n hn => ?_⟩
  have hnp : p ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hthr : (X.pt p).modulus (Q'.invSucc p) ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨Npn, hNpn⟩ := X.reg p n
  refine D.quad3 ((X.pt p).seq n)
    ((X.pt p).seq (max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn)))
    ((X.pt n).seq (max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn)))
    (X.dseq n) (Q'.invSucc p) ?_ ?_ ?_
  · -- d²((pt p).n, (pt p).m) ≤ invSucc p
    have hm : (X.pt p).modulus (Q'.invSucc p)
        ≤ max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn) :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    exact (X.pt p).isCauchy (Q'.invSucc p) (Q'.invSucc_pos p) n
      (max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn)) hthr hm
  · -- d²((pt p).m, (pt n).m) ≤ invSucc (min p n) = invSucc p
    have hmN : Npn ≤ max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn) :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have h := hNpn (max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn)) hmN
    rwa [Nat.min_eq_left hnp] at h
  · -- d²((pt n).m, (pt n).Jn) ≤ invSucc n ≤ invSucc p
    have hm : X.Jidx n
        ≤ max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn) :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have h := (X.pt n).isCauchy (Q'.invSucc n) (Q'.invSucc_pos n)
      (max (max n (X.Jidx n)) (max ((X.pt p).modulus (Q'.invSucc p)) Npn)) (X.Jidx n)
      hm (Nat.le_refl _)
    exact Q'.le_trans' _ _ _ h (ExpNeg.invSucc_le_of_le hnp)

/-- **The original sequence converges to the diagonal class.**  For every
tolerance `ε > 0`, the completion points `⟦pt p⟧` are eventually (in `p`) within
squared distance `ε` of `⟦dseq⟧`: `d²(⟦pt p⟧, ⟦dseq⟧) → 0`. -/
theorem diag_converges :
    ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        D.distSqQ ((X.pt p).seq n) (X.dseq n) ≤ ε := by
  intro ε hε
  refine ⟨gMod ε, fun p hp => ?_⟩
  obtain ⟨N, hN⟩ := X.diag_conv_le p
  refine ⟨N, fun n hn => ?_⟩
  refine Q'.le_trans' _ _ _ (hN n hn) ?_
  refine Q'.le_trans' _ _ _ (treeval_le_ten (Q'.invSucc p)) ?_
  exact gMod_spec ε hε p hp

end CompletionCauchy

/-! ## The capstone: the complete constructive GNS Hilbert space -/

/-- **The constructive COMPLETE GNS Hilbert space.**  Bundles the
`GNSHilbertSpace` capstone (carrier = metric completion, dense isometric
embedding, `CReal`-valued inner product extending the GNS form) with genuine
**metric completeness**: every regular-rate `cDistSq`-Cauchy sequence of
completion points converges to a completion point `⟦z⟧`. -/
structure CompleteGNSHilbert (D : GNSData) where
  /-- The underlying GNS Hilbert space (inner product + dense embedding). -/
  hilbert : D.GNSHilbertSpace
  /-- **Completeness.**  Every regular-rate Cauchy sequence of completion points
  has a limit representative `z` whose class `⟦z⟧` it converges to. -/
  complete : ∀ X : CompletionCauchy D,
    ∃ z : CauchyGNS D,
      ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
        ∃ N : Nat, ∀ n : Nat, N ≤ n →
          D.distSqQ ((X.pt p).seq n) (z.seq n) ≤ ε

namespace GNSData

variable (D : GNSData)

/-- **CAPSTONE.**  The genuine constructive complete GNS Hilbert space: the
metric completion with its `CReal`-valued inner product, now proved metrically
complete (the diagonal limit `diagCauchy`). -/
def gnsComplete : CompleteGNSHilbert D where
  hilbert := D.gnsHilbertSpace
  complete := fun X => ⟨X.diagCauchy, X.diag_converges⟩

end GNSData

/-! ## Goal 1: UNCONDITIONAL (arbitrary-modulus) metric completeness

`CompletionCauchy` carries the *regular* fixed rate `1/(min p q + 1)`.  A general
Cauchy sequence in the completion comes with an arbitrary `Type`-level modulus
`mod : Q′ → Nat`.  We close the gap by a **cofinal regular reindexing**: a
strictly-increasing `φ : Nat → Nat` with `φ k ≥ mod (1/(k+1))`.  The reindexed
sequence `p ↦ pt (φ p)` is regular-rate (`reindex : CompletionCauchy`), so it has
the diagonal limit `diagCauchy`; and a Cauchy sequence converges to any limit of a
cofinal subsequence (`converges`, the `Q′`-level lemma proved here from the
quadratic triangle).  This yields UNCONDITIONAL completeness
(`gnsComplete_general`). -/

/-- The strictly-increasing reindexing modulus: `φ 0 = mod(1/1)`,
`φ(k+1) = max (φ k + 1) (mod(1/(k+2)))`.  Strictly increasing AND
`φ k ≥ mod(1/(k+1))`. -/
def genPhiAux (mod : Q' → Nat) : Nat → Nat
  | 0 => mod (Q'.invSucc 0)
  | k + 1 => max (genPhiAux mod k + 1) (mod (Q'.invSucc (k + 1)))

/-- A **general (arbitrary-modulus) Cauchy sequence in the metric completion**,
presented `Type`-level by representatives `pt` with an arbitrary modulus `mod`
(the honest eventual-rational reading of the completion-distance Cauchy
condition, exactly as in `CompletionCauchy` but with no fixed rate). -/
structure GeneralCompletionCauchy (D : GNSData) where
  /-- A representative `CauchyGNS` for each completion point. -/
  pt : Nat → CauchyGNS D
  /-- The arbitrary `Type`-level Cauchy modulus. -/
  mod : Q' → Nat
  /-- Past `mod ε`, the representative squared distances are eventually `≤ ε`. -/
  cauchy : ∀ ε : Q', (0 : Q') < ε → ∀ p q : Nat, mod ε ≤ p → mod ε ≤ q →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      D.distSqQ ((pt p).seq n) ((pt q).seq n) ≤ ε

namespace GeneralCompletionCauchy

variable {D : GNSData} (X : GeneralCompletionCauchy D)

/-- The cofinal regular reindexing `φ`. -/
def phi (k : Nat) : Nat := genPhiAux X.mod k

/-- `φ(k+1) = max (φ k + 1) (mod(1/(k+2)))`. -/
theorem phi_succ_eq (k : Nat) :
    X.phi (k + 1) = max (X.phi k + 1) (X.mod (Q'.invSucc (k + 1))) := rfl

/-- `φ` is strictly increasing at successors. -/
theorem phi_lt_succ (k : Nat) : X.phi k < X.phi (k + 1) := by
  rw [X.phi_succ_eq k]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)

/-- `φ` is monotone. -/
theorem phi_mono {a b : Nat} (h : a ≤ b) : X.phi a ≤ X.phi b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (Nat.le_of_lt (X.phi_lt_succ b))
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

/-- `φ` is cofinal: `k ≤ φ k`. -/
theorem self_le_phi (k : Nat) : k ≤ X.phi k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (X.phi_lt_succ k))

/-- `φ k ≥ mod(1/(k+1))`: the reindex clears the modulus at rate `1/(k+1)`. -/
theorem phi_ge_mod (k : Nat) : X.mod (Q'.invSucc k) ≤ X.phi k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => rw [X.phi_succ_eq k]; exact Nat.le_max_right _ _

/-- **The regular-rate cofinal reindexing** `p ↦ pt (φ p)` as a genuine
`CompletionCauchy` (fixed rate `1/(min p q + 1)`). -/
def reindex : CompletionCauchy D where
  pt := fun k => X.pt (X.phi k)
  reg := fun p q => by
    have hmp : X.mod (Q'.invSucc (min p q)) ≤ X.phi p :=
      Nat.le_trans (X.phi_ge_mod (min p q)) (X.phi_mono (Nat.min_le_left p q))
    have hmq : X.mod (Q'.invSucc (min p q)) ≤ X.phi q :=
      Nat.le_trans (X.phi_ge_mod (min p q)) (X.phi_mono (Nat.min_le_right p q))
    exact X.cauchy (Q'.invSucc (min p q)) (Q'.invSucc_pos (min p q)) (X.phi p) (X.phi q) hmp hmq

/-- The limit representative: the diagonal of the regular reindexing. -/
def lim : CauchyGNS D := X.reindex.diagCauchy

/-- **The original (arbitrary-modulus) sequence converges to `lim`.**  A Cauchy
sequence converges to any limit of a cofinal subsequence: combine the Cauchy
condition between `pt p` and the cofinal `pt (φ k)` with the subsequence's
convergence (`reindex.diag_converges`) through the quadratic triangle. -/
theorem converges :
    ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        D.distSqQ ((X.pt p).seq n) (X.lim.seq n) ≤ ε := by
  intro ε hε
  let τ : Q' := HalfPow.half * (HalfPow.half * ε)
  have hτpos : (0 : Q') < τ := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨Psub, hPsub⟩ := X.reindex.diag_converges τ hτpos
  -- fix one cofinal index `k` that clears both the subsequence stage and `mod τ`
  let k : Nat := max Psub (X.mod τ)
  have hphik_modτ : X.mod τ ≤ X.phi k :=
    Nat.le_trans (Nat.le_max_right _ _) (X.self_le_phi k)
  obtain ⟨Nk, hNk⟩ := hPsub k (Nat.le_max_left _ _)
  refine ⟨X.mod τ, fun p hp => ?_⟩
  obtain ⟨Npk, hNpk⟩ := X.cauchy τ hτpos p (X.phi k) hp hphik_modτ
  refine ⟨max Nk Npk, fun n hn => ?_⟩
  have hn_k : Nk ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn_pk : Npk ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have ha : D.distSqQ ((X.pt p).seq n) ((X.pt (X.phi k)).seq n) ≤ τ := hNpk n hn_pk
  have hb : D.distSqQ ((X.pt (X.phi k)).seq n) (X.lim.seq n) ≤ τ := hNk n hn_k
  have htri := D.distSqQ_triangle ((X.pt p).seq n) ((X.pt (X.phi k)).seq n) (X.lim.seq n)
  have hr := Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb)
  have heps : ((τ + τ) + (τ + τ)).eqv ε := by
    have hqq : (τ + τ).eqv (HalfPow.half * ε) := ExpNeg.two_halves (HalfPow.half * ε)
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hqq hqq) (ExpNeg.two_halves ε)
  exact le_of_le_eqv (Q'.le_trans' _ _ _ htri hr) heps

end GeneralCompletionCauchy

/-! ## The UNCONDITIONAL complete constructive GNS Hilbert space -/

/-- **The constructive COMPLETE GNS Hilbert space, UNCONDITIONALLY.**  Like
`CompleteGNSHilbert` but the completeness field accepts every
`GeneralCompletionCauchy` (arbitrary `Type`-level modulus), not only the
regular-rate `CompletionCauchy`. -/
structure CompleteGNSHilbertGeneral (D : GNSData) where
  /-- The underlying GNS Hilbert space. -/
  hilbert : D.GNSHilbertSpace
  /-- **Unconditional completeness.**  Every arbitrary-modulus Cauchy sequence of
  completion points has a limit representative it converges to. -/
  complete : ∀ X : GeneralCompletionCauchy D,
    ∃ z : CauchyGNS D,
      ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
        ∃ N : Nat, ∀ n : Nat, N ≤ n →
          D.distSqQ ((X.pt p).seq n) (z.seq n) ≤ ε

namespace GNSData

variable (D : GNSData)

/-- **CAPSTONE (Goal 1).**  The genuine constructive complete GNS Hilbert space
with UNCONDITIONAL metric completeness — every arbitrary-modulus Cauchy sequence
of completion points converges (cofinal regular reindexing + diagonal limit).
This fully closes the constructive complete GNS Hilbert space. -/
def gnsComplete_general : CompleteGNSHilbertGeneral D where
  hilbert := D.gnsHilbertSpace
  complete := fun X => ⟨X.lim, X.converges⟩

end GNSData

end YMGap.Continuum.GNSQuotient

/-! ## The complete GNS Hilbert space of a finite-volume Wilson theory -/

namespace YMGap.Continuum.WilsonGNS

open YMGap.Continuum.GNSQuotient

/-- **The constructive COMPLETE GNS Hilbert space of the finite-volume Wilson
theory.**  The actual Wilson observable bundle yields a genuine constructive
complete inner-product (Hilbert) space: the metric completion of its GNS
pre-Hilbert quotient is metrically complete. -/
def WilsonGNSData.completeGnsHilbert {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A) :
    CompleteGNSHilbert W.toGNSData :=
  W.toGNSData.gnsComplete

/-- **UNCONDITIONAL completeness for the Wilson theory (Goal 1).**  The
finite-volume Wilson GNS Hilbert space is metrically complete for arbitrary
(non-regular-rate) Cauchy sequences. -/
def WilsonGNSData.completeGnsHilbertGeneral {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) : CompleteGNSHilbertGeneral W.toGNSData :=
  W.toGNSData.gnsComplete_general

end YMGap.Continuum.WilsonGNS

namespace YMGap.Constructive

/-! ## Axiom gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.treeval_eqv_ten
#print axioms YMGap.Constructive.treeval_le_ten
#print axioms YMGap.Constructive.gMod_spec
#print axioms YMGap.Continuum.GNSQuotient.GNSData.quad3
#print axioms YMGap.Continuum.GNSQuotient.CompletionCauchy.diag_cauchy_le
#print axioms YMGap.Continuum.GNSQuotient.CompletionCauchy.diagCauchy
#print axioms YMGap.Continuum.GNSQuotient.CompletionCauchy.diag_conv_le
#print axioms YMGap.Continuum.GNSQuotient.CompletionCauchy.diag_converges
#print axioms YMGap.Continuum.GNSQuotient.GNSData.gnsComplete
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.completeGnsHilbert
#print axioms YMGap.Continuum.GNSQuotient.GeneralCompletionCauchy.phi_mono
#print axioms YMGap.Continuum.GNSQuotient.GeneralCompletionCauchy.self_le_phi
#print axioms YMGap.Continuum.GNSQuotient.GeneralCompletionCauchy.phi_ge_mod
#print axioms YMGap.Continuum.GNSQuotient.GeneralCompletionCauchy.reindex
#print axioms YMGap.Continuum.GNSQuotient.GeneralCompletionCauchy.converges
#print axioms YMGap.Continuum.GNSQuotient.GNSData.gnsComplete_general
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.completeGnsHilbertGeneral

end YMGap.Constructive
